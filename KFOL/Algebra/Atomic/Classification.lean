module

public import KFOL.Algebra.Atomic.Boolean

/-! # Exact atomic S2 classification without external clone-theoretic assumptions -/

@[expose] public section

namespace KFOL.Term

universe u v

variable {Role : Type u} {Var : Type v}

/-- Every essentially unary function has a realizing term. -/
theorem atomic_realization_essentiallyUnary [Finite Role]
    (f : (Var → Role) → Role) (hf : Atomic.EssentiallyUnary f) :
    ∃ t : Term Role Var, t.AtomicRealizes f := by
  obtain ⟨i,g,hg⟩ := hf
  obtain ⟨t,ht⟩ := atomic_realization_unary i g
  exact ⟨t,fun v => (ht v).trans (congrArg WinnerSet.singleton (hg v).symm)⟩

/-- At each finite arity the atomic functions of the full public syntax are
exactly the essentially unary and at most two-valued functions. Both
realization directions construct actual terms; no clone theorem is assumed.
The statement also covers arity zero. -/
theorem atomic_function_classification [Finite Role] [Nonempty Role] [Finite Var]
    (f : (Var → Role) → Role) :
    (∃ t : Term Role Var, t.AtomicRealizes f) ↔
      Atomic.EssentiallyUnary f ∨ Atomic.AtMostTwo f := by
  constructor
  · rintro ⟨t,ht⟩
    exact ht.essentiallyUnary_or_atMostTwo
  · intro h
    exact h.elim (atomic_realization_essentiallyUnary f) (atomic_realization_atMostTwo f)

/-- An atom-preserving term admits one of the independently defined S2 atomic
functions, and every such function is realized by an atom-preserving term. -/
theorem atomic_function_classification_with_preservation
    [Finite Role] [Nonempty Role] [Finite Var] (f : (Var → Role) → Role) :
    (∃ t : Term Role Var, t.AtomPreserving ∧ t.AtomicRealizes f) ↔
      Atomic.EssentiallyUnary f ∨ Atomic.AtMostTwo f := by
  constructor
  · rintro ⟨t,_,ht⟩
    exact (atomic_function_classification f).mp ⟨t,ht⟩
  · intro h
    obtain ⟨t,ht⟩ := (atomic_function_classification f).mpr h
    exact ⟨t,fun v => ⟨f v,ht v⟩,ht⟩

end KFOL.Term
