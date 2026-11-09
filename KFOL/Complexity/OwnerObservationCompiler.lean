module

public import KFOL.Owner.ObservationCompilation
public import KFOL.Complexity.OwnerTermFrontend

/-! # Native linear syntax compilation for relative owner observations -/
@[expose] public section
namespace KFOL.Complexity.OwnerObservationCompiler
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {Role : Type} [Fintype Role] [DecidableEq Role]

noncomputable abbrev sourceEncoding := OwnerTermMachines.termEncoding (Role := Role)
noncomputable abbrev targetEncoding := OwnerTermFrontend.termEncoding

noncomputable def compileBound : ℕ :=
  1 + 2 * OwnerTermMachines.resetHeader (Role := Unit) + OwnerTermMachines.guardedHeader ()

/-- Every source child occurs once; a guarded node contributes at most two resets. -/
theorem encode_length (observer : Role) (term : Owner.Term Role ℕ) :
    (targetEncoding (term.compileObservation observer)).length ≤
      compileBound * (sourceEncoding term).length := by
  have hb : 1 ≤ compileBound := by unfold compileBound; omega
  induction term using Owner.Term.induction_owner with
  | var j =>
    change (sourceEncoding (.var j : Owner.Term Role ℕ)).length ≤ _
    nlinarith
  | step s t hs ht =>
    rw [Owner.Term.compileObservation_step]
    change (OwnerTermMachines.termEncoding _).length ≤ _
    rw [OwnerTermMachines.length_step,OwnerTermMachines.length_step]
    have hh : OwnerTermMachines.resetHeader (Role := Unit) ≤ compileBound := by
      unfold compileBound; omega
    have hp : 1 ≤ OwnerTermMachines.resetHeader (Role := Role) := by
      unfold OwnerTermMachines.resetHeader; omega
    nlinarith
  | guarded r x y z hx hy hz =>
    rw [Owner.Term.compileObservation_guarded]
    have hp : 1 ≤ OwnerTermMachines.guardedHeader r := by
      unfold OwnerTermMachines.guardedHeader; omega
    by_cases he : r = observer
    · rw [ite_eq_left he]
      change (OwnerTermMachines.termEncoding _).length ≤ _
      rw [OwnerTermMachines.length_step,OwnerTermMachines.length_step,
        OwnerTermMachines.length_guarded]
      have hh : 2 * OwnerTermMachines.resetHeader (Role := Unit) ≤ compileBound := by
        unfold compileBound; omega
      nlinarith
    · rw [ite_eq_right he]
      change (OwnerTermMachines.termEncoding _).length ≤ _
      rw [OwnerTermMachines.length_guarded,OwnerTermMachines.length_guarded]
      have hh : OwnerTermMachines.guardedHeader () ≤ compileBound := by
        unfold compileBound; omega
      nlinarith

private def leaf (_ : Unit) (j : ℕ) : Owner.Term Unit ℕ := .var j
private def node (observer : Role) (_ : Unit) (operation : Operation (Owner.Symbol Role))
    (children : List (Owner.Term Unit ℕ)) : Owner.Term Unit ℕ :=
  let x := children.getD 0 (.var 0)
  let y := children.getD 1 (.var 0)
  let z := children.getD 2 (.var 0)
  match operation with
  | ⟨_,.reset⟩ => x.step y
  | ⟨_,.guarded r⟩ => if r = observer then z.step (y.step x) else Owner.Term.guarded () x y z

omit [Fintype Role] in
private theorem fold_compile (observer : Role) (term : Owner.Term Role ℕ) :
    FiniteFoldMachine.fold leaf (node observer) () term = term.compileObservation observer := by
  induction term using Owner.Term.induction_owner with
  | var => rfl
  | step s t hs ht =>
    simp [FiniteFoldMachine.fold,node,Owner.Term.step,List.ofFn_succ,hs,ht,
      Owner.Term.compileObservation]
  | guarded r x y z hx hy hz =>
    simp [FiniteFoldMachine.fold,node,Owner.Term.guarded,List.ofFn_succ,hx,hy,hz,
      Owner.Term.compileObservation]

private theorem leaf_polyTime : ComputableInPolyTime
    (fun p : Unit × ℕ => leaf p.1 p.2) (encPair encUnit encNat) targetEncoding :=
  OwnerTermMachines.var_polyTime.comp (snd _ _)

private theorem node_polyTime (observer : Role) : ComputableInPolyTime
    (fun p : Unit × (Operation (Owner.Symbol Role) × List (Owner.Term Unit ℕ)) =>
      node observer p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList targetEncoding)))
    targetEncoding := by
  let input := encPair encUnit (encPair
    (FiniteTermMachines.operationEncoding (σ := Owner.Symbol Role)) (encList targetEncoding))
  have hop : ComputableInPolyTime
      (fun p : Unit × (Operation (Owner.Symbol Role) × List (Owner.Term Unit ℕ)) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : Unit × (Operation (Owner.Symbol Role) × List (Owner.Term Unit ℕ)) => p.2.2)
      input (encList targetEncoding) := by fun_prop
  have hx := (listGetD (encA := targetEncoding) (.var 0 : Owner.Term Unit ℕ)).comp (hc.prod (const 0))
  have hy := (listGetD (encA := targetEncoding) (.var 0 : Owner.Term Unit ℕ)).comp (hc.prod (const 1))
  have hz := (listGetD (encA := targetEncoding) (.var 0 : Owner.Term Unit ℕ)).comp (hc.prod (const 2))
  apply hop.finite_cases (branch := fun operation p => node observer p.1 operation p.2.2)
  rintro ⟨arity,operation⟩
  cases operation with
  | reset => exact OwnerTermMachines.step_polyTime.comp (hx.prod hy)
  | guarded r =>
    by_cases he : r = observer
    · simpa only [node,ite_eq_left he,Function.comp_def,targetEncoding,OwnerTermFrontend.termEncoding] using
        OwnerTermMachines.step_polyTime.comp
          (hz.prod (OwnerTermMachines.step_polyTime.comp (hy.prod hx)))
    · simpa only [node,ite_eq_right he,Function.comp_def,targetEncoding,OwnerTermFrontend.termEncoding] using
        (OwnerTermMachines.guarded_polyTime ()).comp (hx.prod (hy.prod hz))

/-- The source syntax is compiled in native polynomial time, with a linear
output bound in its original binary encoding. -/
theorem compile_polyTime (observer : Role) : ComputableInPolyTime
    (Owner.Term.compileObservation (Var := ℕ) observer) sourceEncoding targetEncoding := by
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit)
    (valueEncoding := targetEncoding) leaf (node observer) leaf_polyTime (node_polyTime observer)
    compileBound 1 (by
      intro context term
      cases context
      rw [fold_compile]
      have h := encode_length observer term
      simp only [Nat.pow_one]
      apply h.trans
      apply Nat.mul_le_mul_left
      change (FiniteTermCode.encode (Owner.Symbol Role) term).length ≤ _
      omega) (.var 0)
  have hp : ComputableInPolyTime (fun term : Owner.Term Role ℕ => ((),term))
      sourceEncoding (encPair encUnit sourceEncoding) := (const ()).prod id'
  convert hf.comp hp using 1
  funext term
  exact (fold_compile observer term).symm

/-- Observing one role uses the same complete sparse guard data as the
one-owner checker after the node-for-node translation. -/
theorem observation_guards_polyTime (observer : Role) : ComputableInPolyTime
    (fun term : Owner.Term Role ℕ => term.guards observer) sourceEncoding
    (encList OwnerTermFrontend.guardEncoding) := by
  convert OwnerTermFrontend.guards_polyTime.comp (compile_polyTime observer) using 1
  funext term
  exact (Owner.Term.guards_compileObservation observer term).symm

end KFOL.Complexity.OwnerObservationCompiler
