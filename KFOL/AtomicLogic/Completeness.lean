module

public import KFOL.AtomicLogic.Soundness
public import KFOL.Algebra.Basic

/-! # Completeness by ordered role cases

The proof first expands native role-sorted input variables into finite
cases, then normalizes all ground leaves by the explicit operation tables.
Semantic atomic validity is never defined through derivability.
-/

@[expose] public section

namespace KFOL.AtomicLogic

universe u v w

namespace Derives

private def params {Role : Type u} {A : Type v} {W : Type w}
    (left right : Role → WinnerTerm Role A W) (other : WinnerTerm Role A W) :
    Parameter Role → WinnerTerm Role A W
  | .inl (false, r) => left r
  | .inl (true, r) => right r
  | .inr () => other

theorem case_diagonal {Role : Type u} {A : Type v} {W : Type w}
    (a : RoleTerm Role A) (t : WinnerTerm Role A W) :
    Derives (.cases a (fun _ => t)) t := by
  simpa only [basis, WinnerTerm.subst, RoleTerm.subst, params] using
    (Derives.axiom (.caseDiagonal : BasisIndex Role) (fun _ => a)
      (params (fun _ => t) (fun _ => t) t))

theorem inject_cases {Role : Type u} {A : Type v} {W : Type w}
    (a : RoleTerm Role A) :
    Derives (.inject a : WinnerTerm Role A W)
      (.cases a (fun r => .value (WinnerSet.singleton r))) := by
  simpa only [basis, WinnerTerm.subst, RoleTerm.subst] using
    (Derives.axiom (.injection : BasisIndex Role) (fun _ => a) (fun _ => .inject a))

theorem choice_cases {Role : Type u} {A : Type v} {W : Type w}
    (r : Role) (a : RoleTerm Role A) (s t : Role → WinnerTerm Role A W) :
    Derives (.choice r (.cases a s) (.cases a t))
      (.cases a (fun i => .choice r (s i) (t i))) := by
  simpa only [basis, WinnerTerm.subst, RoleTerm.subst, params] using
    (Derives.axiom (.choiceCases r) (fun _ => a) (params s t (.cases a s)))

theorem rename_cases {Role : Type u} {A : Type v} {W : Type w}
    (p : Equiv.Perm Role) (a : RoleTerm Role A) (s : Role → WinnerTerm Role A W) :
    Derives (.rename p (.cases a s)) (.cases a (fun i => .rename p (s i))) := by
  simpa only [basis, WinnerTerm.subst, RoleTerm.subst, params] using
    (Derives.axiom (.renameCases p) (fun _ => a) (params s s (.cases a s)))

theorem choice_values {Role : Type u} {A : Type v} {W : Type w}
    (r : Role) (S T : WinnerSet Role) :
    Derives (.choice r (.value S) (.value T) : WinnerTerm Role A W)
      (.value (WinnerSet.choice r S T)) := by
  simpa only [basis, WinnerTerm.subst] using
    (Derives.axiom (.choiceTable r S T) (fun _ => .constant r) (fun _ => .value S))

theorem rename_value {Role : Type u} {A : Type v} {W : Type w}
    (p : Equiv.Perm Role) (S : WinnerSet Role) :
    Derives (.rename p (.value S) : WinnerTerm Role A W)
      (.value (WinnerSet.rename p S)) := by
  let atoms : Unit → RoleTerm Role A := fun _ => .constant (Classical.choose S.property)
  simpa only [basis, WinnerTerm.subst] using
    (Derives.axiom (.renameTable p S) atoms (fun _ => .value S))

end Derives

/-- Fix the first atomic input and keep the other inputs in their original order. -/
def cofactor {Role : Type u} {n : ℕ} (t : KFOL.Term Role (Fin (n + 1))) (r : Role) :
    KFOL.Term Role (Fin n) :=
  t.subst (Fin.cases (.winner r) (fun i => .var i))

/-- Include a term on the remaining inputs back into the original variable set. -/
def lift {Role : Type u} {n : ℕ} (t : WinnerTerm Role (Fin n) Empty) :
    WinnerTerm Role (Fin (n + 1)) Empty :=
  t.subst (fun i => .var i.succ) Empty.elim

/-- Native syntax admits exact Shannon expansion in the sorted case operation. -/
theorem native_expand {Role : Type u} {n : ℕ} (t : KFOL.Term Role (Fin (n + 1))) :
    Derives (WinnerTerm.ofNative t)
      (.cases (.var 0) (fun r => lift (WinnerTerm.ofNative (cofactor t r)))) := by
  induction t with
  | winner r =>
    exact (Derives.case_diagonal (.var 0) (.value (WinnerSet.singleton r))).symm
  | var x =>
    refine Fin.cases ?_ (fun i => ?_) x
    · exact Derives.inject_cases (.var 0)
    · exact (Derives.case_diagonal (.var 0) (.inject (.var i.succ))).symm
  | choice r s t ihs iht =>
    exact (Derives.choice r ihs iht).trans
      (Derives.choice_cases r (.var 0) _ _)
  | rename p t ih =>
    exact (Derives.rename p ih).trans (Derives.rename_cases p (.var 0) _)

private theorem ground_normalization {Role : Type u} (t : KFOL.Term Role (Fin 0)) :
    Derives (WinnerTerm.ofNative t)
      (.value (t.eval (fun x => Fin.elim0 x))) := by
  induction t with
  | winner => exact .refl _
  | var x => exact Fin.elim0 x
  | choice r s t ihs iht =>
    exact (Derives.choice r ihs iht).trans (Derives.choice_values r _ _)
  | rename p t ih => exact (Derives.rename p ih).trans (Derives.rename_value p _)

theorem cofactor_valid {Role : Type u} {n : ℕ}
    {s t : KFOL.Term Role (Fin (n + 1))} (h : Valid s t) (r : Role) :
    Valid (cofactor s r) (cofactor t r) := by
  intro valuation
  let replacement : Fin (n + 1) → KFOL.Term Role (Fin n) :=
    Fin.cases (.winner r) (fun i => .var i)
  let assignment : Fin (n + 1) → Role := Fin.cases r valuation
  have hv :
      (fun x : Fin (n + 1) =>
        (replacement x).eval
          (fun i => WinnerSet.singleton (valuation i))) =
      (fun x => WinnerSet.singleton (assignment x)) := by
    funext x
    refine Fin.cases ?_ (fun i => ?_) x <;> rfl
  change (s.subst replacement).eval _ = (t.subst replacement).eval _
  rw [KFOL.Term.eval_subst, KFOL.Term.eval_subst, hv]
  exact h assignment

/-- Every atom-valid native equation of finite arity follows from the finite sorted basis. -/
theorem derives_of_valid {Role : Type u} {n : ℕ}
    (s t : KFOL.Term Role (Fin n)) (h : Valid s t) :
    Derives (WinnerTerm.ofNative s) (WinnerTerm.ofNative t) := by
  induction n with
  | zero =>
    have e : s.eval (fun x => Fin.elim0 x) = t.eval (fun x => Fin.elim0 x) := by
      have hv : (fun x : Fin 0 => WinnerSet.singleton (Fin.elim0 x : Role)) =
          (fun x => Fin.elim0 x) := funext (fun x => Fin.elim0 x)
      simpa only [hv] using h Fin.elim0
    exact (ground_normalization s).trans (e ▸ (ground_normalization t).symm)
  | succ n ih =>
    apply (native_expand s).trans
    apply Derives.trans _ (native_expand t).symm
    apply Derives.cases
    intro r
    exact (ih (cofactor s r) (cofactor t r) (cofactor_valid h r)).subst
      (fun i => .var i.succ) Empty.elim

/-- Atomic validity and finite sorted equational derivability are equivalent. -/
theorem valid_iff_derives {Role : Type u} {n : ℕ} (s t : KFOL.Term Role (Fin n)) :
    Valid s t ↔ Derives (WinnerTerm.ofNative s) (WinnerTerm.ofNative t) :=
  ⟨derives_of_valid s t, valid_of_derives⟩

/-- The finite sorted presentation is exact on every native atomic equation. -/
theorem finite_sorted_presentation {Role : Type u} [Finite Role] :
    (Set.range (@basis Role)).Finite ∧
      ∀ (n : ℕ) (s t : KFOL.Term Role (Fin n)),
        Valid s t ↔ Derives (WinnerTerm.ofNative s) (WinnerTerm.ofNative t) :=
  ⟨basis_finite, fun _ s t => valid_iff_derives s t⟩

end KFOL.AtomicLogic
