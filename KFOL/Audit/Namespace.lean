module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-! A failing axiom check for every declaration in a mathematical namespace. -/

open Lean Elab Command

/-- Audit the complete namespace, including nested declarations, against the
standard mathematical axioms. Proof dependencies are checked transitively. -/
syntax (name := auditNamespace) "#audit_namespace " ident : command

elab_rules : command
  | `(#audit_namespace $namespaceName:ident) => do
      let environment ← getEnv
      let targetNamespace := namespaceName.getId
      let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
      let mut checked : Nat := 0
      for (name, _) in environment.constants.toList do
        if targetNamespace.isPrefixOf name then
          checked := checked + 1
          for axiomName in (← collectAxioms name) do
            unless allowed.contains axiomName do
              throwError "Namespace axiom audit: {name} depends on forbidden axiom {axiomName}"
      if checked == 0 then
        throwError "Namespace axiom audit: no declarations in {targetNamespace}"
      logInfo m!"Axiom audit: {checked} declarations in {targetNamespace}; only propext, Classical.choice and Quot.sound"
