module

public import KFOL.Algorithms.FullTermCode.Actions
public import KFOL.Algorithms.FullTermCode.Validation
public import KFOL.Algebra.Idempotent
public import Mathlib.Data.List.Forall2

/-! # Exact original-input extraction using sparse accumulated arrays -/

@[expose] public section

namespace KFOL.FullTermCode

/-- Direct raw constructor wrappers preserve actual finite child positions. -/
def rawWinner (role : ℕ) : Raw := .func (.winner role) Fin.elim0
def rawChoice (owner : ℕ) (left right : Raw) : Raw :=
  .func (.choice owner) (fun i => if i=0 then left else right)
def rawRename (forward : List ℕ) (term : Raw) : Raw :=
  .func (.rename forward) (fun _ => term)

/-- Transport every winner/owner label through one explicitly stored array.
The total raw implementation also preserves any rename node it encounters;
normalization supplies a rename-free input at the extraction call sites. -/
def mapRoles (forward : List ℕ) : Raw → Raw
  | .var name => .var name
  | .func (.winner role) _ => rawWinner (forward.getD role 0)
  | .func (.choice owner) children =>
      rawChoice (forward.getD owner 0) (mapRoles forward (children 0)) (mapRoles forward (children 1))
  | .func (.rename original) children => rawRename original (mapRoles forward (children 0))

/-- Cached normalized syntax, absence of winner leaves, and one sparse action
per actual variable occurrence. Repeated occurrences are never identified. -/
abbrev Annotation := Raw × (Bool × List Action)

/-- A bottom-up exact syntax traversal. Rename nodes use only their actual
array payloads, both for owner transport and for leaf-action composition. -/
def annotate : Raw → Annotation
  | .var name => (.var name,true,[none])
  | .func (.winner role) _ => (rawWinner role,false,[])
  | .func (.choice owner) children =>
      let left := annotate (children 0)
      let right := annotate (children 1)
      (rawChoice owner left.1 right.1,left.2.1 && right.2.1,left.2.2 ++ right.2.2)
  | .func (.rename forward) children =>
      let child := annotate (children 0)
      (mapRoles forward child.1,child.2.1,child.2.2.map (Action.compose (some forward)))

/-- Finish only if every actual variable occurrence has identity accumulated
action and no winner leaf occurred. Missing identity arrays stay absent. -/
def extractRaw (raw : Raw) : Option Raw :=
  let result := annotate raw
  if result.2.1 && result.2.2.all Action.isIdentity then some result.1 else none

/-- Whole original-input word extraction first parses binary K and its actual
tree, then checks all role labels/physical arrays, and returns the original
role-count header with the extracted core's complete original tree code. -/
def extractWord (word : List Bool) : Option (List Bool) := do
  let (countWord,treeWord) ← Words.unpair? word
  let K ← Words.BinaryNatCode.decode? countWord
  let raw ← decode treeWord
  if valid K raw then
    let core ← extractRaw raw
    return Words.pair countWord (encode core)
  else none

/-- Explicit-array label transport is exactly actual permutation transport. -/
theorem mapRoles_view_push {K : ℕ} (p q : Equiv.Perm (Fin K)) (term : KFOL.Term (Fin K) ℕ) :
    mapRoles (permutationArray p) (view (term.pushRenames q)) = view (term.pushRenames (p*q)) := by
  induction term generalizing q with
  | var name => rfl
  | winner role => simp [KFOL.Term.pushRenames,view,mapRoles,rawWinner,permutationArray,Equiv.Perm.mul_apply]
  | choice owner left right hl hr =>
    change rawChoice ((permutationArray p).getD (q owner).val 0)
      (mapRoles (permutationArray p) (view (left.pushRenames q)))
      (mapRoles (permutationArray p) (view (right.pushRenames q))) =
      rawChoice ((p*q) owner).val (view (left.pushRenames (p*q))) (view (right.pushRenames (p*q)))
    rw [hl q,hr q,permutationArray_getD]
    rfl
  | rename r term ih =>
    simpa only [KFOL.Term.pushRenames,mul_assoc] using ih (q*r)

/-- The cached raw output is exactly the original permutation-pushed term,
for every input, including inputs whose eventual clean check fails. -/
theorem annotate_view_core {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    (annotate (view term)).1 = view (term.pushRenames 1) := by
  induction term with
  | var name => rfl
  | winner role => simp [view,annotate,KFOL.Term.pushRenames,rawWinner]
  | choice owner left right hl hr =>
    simp [view,annotate,KFOL.Term.pushRenames,rawChoice,hl,hr]
  | rename p term ih =>
    simp only [view,annotate,ih]
    simpa only [one_mul,mul_one,KFOL.Term.pushRenames] using mapRoles_view_push p 1 term

/-- Winner-leaf rejection is an exact syntactic test, independent of the
runtime machine or the idempotency characterization. -/
theorem annotate_view_noWinner {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    (annotate (view term)).2.1 = true ↔ ¬ term.HasWinner := by
  induction term with
  | var name => simp [view,annotate,KFOL.Term.HasWinner]
  | winner role => simp [view,annotate,KFOL.Term.HasWinner]
  | choice owner left right hl hr =>
    simp [view,annotate,KFOL.Term.HasWinner,hl,hr]
  | rename p term ih => simpa only [view,annotate,KFOL.Term.HasWinner] using ih

/-- Every actual variable occurrence retains its exact accumulated action.
This relation permits the physically absent representation of identity. -/
theorem annotate_view_actions {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    List.Forall₂ (fun action occurrence => Action.Represents action occurrence.2)
      (annotate (view term)).2.2 term.inputOccurrences := by
  induction term with
  | var name => exact .cons Action.represents_none .nil
  | winner role => exact .nil
  | choice owner left right hl hr =>
    simpa [view,annotate,KFOL.Term.inputOccurrences] using List.rel_append hl hr
  | rename p term ih =>
    simp only [view,annotate,KFOL.Term.inputOccurrences]
    exact List.rel_map (P := fun action (occurrence : ℕ × Equiv.Perm (Fin K)) =>
      Action.Represents action occurrence.2)
      (fun action occurrence h => Action.compose_represents (Action.represents_some p) h) ih

private theorem all_identity_of_related {K : ℕ} {actions : List Action}
    {occurrences : List (ℕ × Equiv.Perm (Fin K))}
    (related : List.Forall₂ (fun action occurrence => Action.Represents action occurrence.2)
      actions occurrences) :
    actions.all Action.isIdentity = true ↔ ∀ occurrence ∈ occurrences, occurrence.2 = 1 := by
  induction related with
  | nil => simp
  | cons h related ih =>
    simpa only [List.all_cons,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp] using
      and_congr (Action.isIdentity_iff h) ih

/-- The sparse finite-array check is exactly the existing independent
`CleanUnder 1` invariant, without enumerating absent identity arrays. -/
theorem annotate_view_clean_iff {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    ((annotate (view term)).2.1 && (annotate (view term)).2.2.all Action.isIdentity) = true ↔
      term.CleanUnder 1 := by
  rw [Bool.and_eq_true,annotate_view_noWinner,
    all_identity_of_related (annotate_view_actions term)]
  simp only [KFOL.Term.CleanUnder,one_mul]
  constructor
  · rintro ⟨hw,hp⟩
    exact ⟨hw,fun x q h => hp (x,q) h⟩
  · rintro ⟨hw,hp⟩
    exact ⟨hw,fun occurrence h => hp occurrence.1 occurrence.2 h⟩

/-- The complete actual raw computation equals the already proved native
checked extraction, on every original typed input and for every K. -/
theorem extractRaw_view {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    extractRaw (view term) = (term.extractCore? 1).map view := by
  unfold extractRaw
  dsimp only
  by_cases hclean : term.CleanUnder 1
  · have he := (term.extractCore?_eq_some_iff 1 (term.pushRenames 1)).2 ⟨hclean,rfl⟩
    rw [(annotate_view_clean_iff term).2 hclean,he]
    simp only [ite_true,Option.map_some,annotate_view_core]
  · have hnone : term.extractCore? 1 = none := by
      cases he : term.extractCore? 1 with
      | none => rfl
      | some core => exact (hclean ((term.extractCore?_eq_some_iff 1 core).1 he).1).elim
    have hfalse : ((annotate (view term)).2.1 &&
        (annotate (view term)).2.2.all Action.isIdentity) = false :=
      Bool.eq_false_iff.mpr (fun h => hclean ((annotate_view_clean_iff term).1 h))
    rw [hfalse,hnone]
    rfl

/-- Exact original-input word correctness, including failure, output byte
format, role count, and every repeated source occurrence. -/
theorem extractWord_encodeInput (input : Input) :
    extractWord (encodeInput input) =
      (input.2.extractCore? 1).map (fun core => encodeInput ⟨input.1,core⟩) := by
  rcases input with ⟨K,term⟩
  cases he : term.extractCore? 1 <;> simp [extractWord,encodeInput,extractRaw_view,he]

end KFOL.FullTermCode
