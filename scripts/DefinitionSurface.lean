module
/-
Export the semantic dependency graph of the public Paper or Report theorem TYPES.

This is deliberately not a theorem-proof dependency extractor. Traversal starts
at each theorem's type, follows types and computational/predicate definitions
owned by KFOL, and includes constructor declarations of reachable inductives.
Proof-valued subterms are erased with Meta.isProof in a correctly extended local
context. Theorem proof bodies are never inspected. External declarations are
recorded as boundary interfaces and are not unfolded.

Run through scripts/export_definition_surface.py; its temporary output path is
provided in KFOL_DEFINITION_SURFACE_RAW. No project source is changed here.
-/
import all Paper
import all Report
import Lean.Meta
import Lean.Elab.Command
import Lean.DeclarationRange

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Lean Meta
namespace DefinitionSurface

structure References where
  names : Array Name := #[]
  skippedProofTerms : Nat := 0

private def References.append (left right : References) : References :=
  ⟨left.names ++ right.names, left.skippedProofTerms + right.skippedProofTerms⟩

/-- Enter binders before inferring whether a subterm is proof-valued. Erasing
proofs also erases helper definitions occurring only inside those proofs. -/
partial def references (expression : Expr) : MetaM References := do
  if ← isProof expression then
    return ⟨#[], 1⟩
  match expression with
  | .const name _ => return ⟨#[name], 0⟩
  | .app function argument =>
    return (← references function).append (← references argument)
  | .lam name type body info | .forallE name type body info =>
    let domain ← references type
    let range ← withLocalDecl name info type fun x => references (body.instantiate1 x)
    return domain.append range
  | .letE name type value body _ =>
    let domain ← references type
    let definition ← references value
    let range ← withLetDecl name type value fun x => references (body.instantiate1 x)
    return (domain.append definition).append range
  | .mdata _ body => references body
  | .proj structureName _ body =>
    return (⟨#[structureName], 0⟩ : References).append (← references body)
  | _ => return {}

private def moduleName (environment : Environment) (name : Name) : Name :=
  match environment.getModuleIdxFor? name with
  | some index => environment.header.moduleNames[index.toNat]!
  | none => .anonymous

private def projectOwned (environment : Environment) (entrypoint name : Name) : Bool :=
  let owner := moduleName environment name
  (`KFOL).isPrefixOf owner || owner == `Paper || (entrypoint == `Report && owner == `Report)

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque_definition"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def strings (names : Array Name) : Json := toJson (names.map Name.toString)
private def sortedNames (names : Array Name) : Array Name :=
  (names.toList.mergeSort (fun a b => a.toString ≤ b.toString)).toArray.foldl
    (fun result name => if result.back? == some name then result else result.push name) #[]

private def location (name : Name) : MetaM Json := do
  match ← findDeclarationRanges? name with
  | none => return Json.null
  | some ranges => return Json.mkObj [
      ("line", toJson ranges.range.pos.line),
      ("column", toJson ranges.range.pos.column)]

private def typeText (info : ConstantInfo) : MetaM String :=
  withOptions (fun options => options.set `pp.width (110 : Nat) |>.set `pp.maxSteps (1000000 : Nat))
    ((·.pretty) <$> ppExpr info.type)

/-- Only mathematical/predicate and computational bodies are inspected. In
particular, `allowOpaque` never enables access to theorem proof values. -/
private def definitionValue : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

private def constructors : ConstantInfo → Array Name
  | .inductInfo value => (value.ctors ++ value.all).toArray
  | _ => #[]

/-- A global graph is computed once; Python computes each root's transitive
slice from its edges, without re-entering or unfolding any proof. -/
def exportGraph (entrypoint : Name := `Paper) : MetaM Json := do
  let environment ← getEnv
  let publicNamespace := if entrypoint == `Report then `KFOL.Report else `KFOL.Paper
  let roots := sortedNames <| environment.constants.toList.toArray.filterMap fun (name, info) =>
    if name.getPrefix == publicNamespace && moduleName environment name == entrypoint && info.isTheorem
    then some name else none
  if roots.isEmpty then throwError "Definition surface: no public {entrypoint} theorem types found"
  let mut pending := roots
  let mut visited : NameSet := {}
  let mut externalNames : NameSet := {}
  let mut nodes : Array Json := #[]
  while let some name := pending.back? do
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      let info ← getConstInfo name
      let typeRefs ← references info.type
      let bodyRefs ← match definitionValue info with
        | some value => references value
        | none => pure {}
      let constructorRefs := constructors info
      let edges := sortedNames (typeRefs.names ++ bodyRefs.names ++ constructorRefs)
      let mut projectEdges : Array Name := #[]
      let mut externalEdges : Array Name := #[]
      for dependency in edges do
        if projectOwned environment entrypoint dependency then
          projectEdges := projectEdges.push dependency
          if !visited.contains dependency then pending := pending.push dependency
        else
          externalEdges := externalEdges.push dependency
          externalNames := externalNames.insert dependency
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("module", toJson (moduleName environment name).toString),
        ("kind", toJson (kind info)),
        ("type", toJson (← typeText info)),
        ("location", ← location name),
        ("type_dependencies", strings (sortedNames typeRefs.names)),
        ("definition_dependencies", strings (sortedNames bodyRefs.names)),
        ("constructor_dependencies", strings (sortedNames constructorRefs)),
        ("project_dependencies", strings projectEdges),
        ("external_dependencies", strings externalEdges),
        ("proof_subterms_erased", toJson (typeRefs.skippedProofTerms + bodyRefs.skippedProofTerms)),
        ("definition_body_traversed", toJson (definitionValue info).isSome),
        ("theorem_proof_traversed", toJson false)]
  let mut externals : Array Json := #[]
  for name in sortedNames externalNames.toArray do
    let info ← getConstInfo name
    externals := externals.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson (moduleName environment name).toString),
      ("kind", toJson (kind info)),
      ("type", toJson (← typeText info))]
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("entrypoint", toJson entrypoint.toString),
    ("roots", strings roots),
    ("project_declarations", toJson nodes),
    ("external_interfaces", toJson externals)]
end DefinitionSurface

run_cmd Lean.Elab.Command.liftTermElabM do
  let requested := (← IO.getEnv "KFOL_DEFINITION_SURFACE_ENTRYPOINT").getD "Paper"
  let entrypoint ← match requested with
    | "Paper" => pure `Paper
    | "Report" => pure `Report
    | _ => throwError "Definition surface: unknown entrypoint {requested}; expected Paper or Report"
  let output ← DefinitionSurface.exportGraph entrypoint
  let some path ← IO.getEnv "KFOL_DEFINITION_SURFACE_RAW"
    | throwError "Set KFOL_DEFINITION_SURFACE_RAW or run scripts/export_definition_surface.py"
  IO.FS.writeFile path output.compress
  logInfo m!"Exported {entrypoint} theorem-type definition surface (theorem proof bodies excluded)."
