module

public import KFOL.Definitions.AtomicLogic

/-! # Soundness and finiteness of the sorted atomic-input basis -/

@[expose] public section

namespace KFOL.AtomicLogic

universe u v w v' w'

namespace RoleTerm

@[simp] theorem eval_subst {Role : Type u} {Var : Type v} {Var' : Type v'}
    (t : RoleTerm Role Var) (replacement : Var → RoleTerm Role Var')
    (valuation : Var' → Role) :
    (t.subst replacement).eval valuation = t.eval (fun x => (replacement x).eval valuation) := by
  cases t <;> rfl

end RoleTerm

namespace WinnerTerm

@[simp] theorem eval_subst {Role : Type u} {AtomVar : Type v} {WinnerVar : Type w}
    {AtomVar' : Type v'} {WinnerVar' : Type w'}
    (t : WinnerTerm Role AtomVar WinnerVar)
    (atoms : AtomVar → RoleTerm Role AtomVar')
    (winners : WinnerVar → WinnerTerm Role AtomVar' WinnerVar')
    (av : AtomVar' → Role) (wv : WinnerVar' → WinnerSet Role) :
    (t.subst atoms winners).eval av wv =
      t.eval (fun x => (atoms x).eval av) (fun x => (winners x).eval av wv) := by
  induction t with
  | var => rfl
  | value => rfl
  | inject => simp [subst, eval]
  | choice r s t ihs iht => simp [subst, eval, ihs, iht]
  | rename p t ih => simp [subst, eval, ih]
  | cases a branches ih => simp [subst, eval, ih]

@[simp] theorem ofNative_eval {Role : Type u} {Var : Type v}
    (t : KFOL.Term Role Var) (valuation : Var → Role) :
    (ofNative t).eval valuation Empty.elim =
      t.eval (fun x => WinnerSet.singleton (valuation x)) := by
  induction t with
  | winner => rfl
  | var => rfl
  | choice r s t ihs iht => simp [ofNative, eval, KFOL.Term.eval, ihs, iht]
  | rename p t ih => simp [ofNative, eval, KFOL.Term.eval, ih]

end WinnerTerm

theorem basis_valid {Role : Type u} (index : BasisIndex Role)
    (av : Unit → Role) (wv : Parameter Role → WinnerSet Role) :
    (basis index).1.eval av wv = (basis index).2.eval av wv := by
  cases index <;> rfl

/-- All derivations are sound at arbitrary well-sorted valuations. -/
theorem Derives.sound {Role : Type u} {AtomVar : Type v} {WinnerVar : Type w}
    {s t : WinnerTerm Role AtomVar WinnerVar} (h : Derives s t) :
    ∀ av wv, s.eval av wv = t.eval av wv := by
  induction h with
  | «axiom» index atoms winners =>
    intro av wv
    rw [WinnerTerm.eval_subst, WinnerTerm.eval_subst]
    exact basis_valid index _ _
  | refl t => intro av wv; rfl
  | symm h ih => intro av wv; exact (ih av wv).symm
  | trans h₁ h₂ ih₁ ih₂ => intro av wv; exact (ih₁ av wv).trans (ih₂ av wv)
  | choice r h₁ h₂ ih₁ ih₂ =>
    intro av wv
    exact congrArg₂ (WinnerSet.choice r) (ih₁ av wv) (ih₂ av wv)
  | rename p h ih =>
    intro av wv
    exact congrArg (WinnerSet.rename p) (ih av wv)
  | cases a h ih =>
    intro av wv
    exact ih (a.eval av) av wv
  | subst h atoms winners ih =>
    intro av wv
    rw [WinnerTerm.eval_subst, WinnerTerm.eval_subst]
    exact ih _ _

/-- Sorted derivations restrict to the independently defined native atomic semantics. -/
theorem valid_of_derives {Role : Type u} {Var : Type v} {s t : KFOL.Term Role Var}
    (h : Derives (WinnerTerm.ofNative s) (WinnerTerm.ofNative t)) : Valid s t := by
  intro valuation
  simpa using h.sound valuation Empty.elim

private abbrev IndexData (Role : Type u) :=
  Role ⊕ Unit ⊕ Unit ⊕ Role ⊕ Role ⊕ Equiv.Perm Role ⊕
    (Role × WinnerSet Role × WinnerSet Role) ⊕ (Equiv.Perm Role × WinnerSet Role)

private def indexOfData {Role : Type u} : IndexData Role → BasisIndex Role
  | .inl r => .caseConstant r
  | .inr (.inl _) => .caseDiagonal
  | .inr (.inr (.inl _)) => .injection
  | .inr (.inr (.inr (.inl r))) => .injectConstant r
  | .inr (.inr (.inr (.inr (.inl r)))) => .choiceCases r
  | .inr (.inr (.inr (.inr (.inr (.inl p))))) => .renameCases p
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (r, S, T))))))) => .choiceTable r S T
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (p, S))))))) => .renameTable p S

instance {Role : Type u} [Finite Role] : Finite (BasisIndex Role) := by
  apply Finite.of_surjective (@indexOfData Role)
  intro index
  cases index with
  | caseConstant r => exact ⟨.inl r, rfl⟩
  | caseDiagonal => exact ⟨.inr (.inl ()), rfl⟩
  | injection => exact ⟨.inr (.inr (.inl ())), rfl⟩
  | injectConstant r => exact ⟨.inr (.inr (.inr (.inl r))), rfl⟩
  | choiceCases r => exact ⟨.inr (.inr (.inr (.inr (.inl r)))), rfl⟩
  | renameCases p => exact ⟨.inr (.inr (.inr (.inr (.inr (.inl p))))), rfl⟩
  | choiceTable r S T =>
    exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl (r, S, T))))))), rfl⟩
  | renameTable p S =>
    exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (p, S))))))), rfl⟩

/-- The presentation has finitely many actual equation templates at every fixed role count. -/
theorem basis_finite {Role : Type u} [Finite Role] :
    (Set.range (@basis Role)).Finite := Set.finite_range _

end KFOL.AtomicLogic
