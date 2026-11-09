module

public import KFOL.Algebra.Atomic.FiniteProduct
public import KFOL.Algebra.CommonSource

/-! # Atomic classification necessity and idempotent determinacy -/

@[expose] public section

namespace KFOL

universe u v

namespace Atomic

/-- An operation fixing the diagonal over at least three labels cannot have
its entire image in a fixed pair. -/
theorem not_atMostTwo_of_diagonal {Index : Type v} {Role : Type u}
    (three : Fin 3 ↪ Role) (f : (Index → Role) → Role)
    (hd : ∀ r, f (fun _ => r) = r) : ¬AtMostTwo f := by
  rintro ⟨a,b,hpair⟩
  have h (i : Fin 3) : three i = a ∨ three i = b := by
    simpa [hd] using hpair (fun _ => three i)
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h 2 with h2 | h2
  all_goals first
    | exact (by decide : (0 : Fin 3) ≠ 1) (three.injective (h0.trans h1.symm))
    | exact (by decide : (0 : Fin 3) ≠ 2) (three.injective (h0.trans h2.symm))
    | exact (by decide : (1 : Fin 3) ≠ 2) (three.injective (h1.trans h2.symm))

end Atomic

namespace Term

variable {Role : Type u} {Var : Type v}

/-- The common-source theorem proves relation preservation for every atomic
function actually realized by a full-language term. -/
theorem AtomicRealizes.preservesRepeat {t : Term Role Var} {f : (Var → Role) → Role}
    (hf : t.AtomicRealizes f) : Atomic.PreservesRepeat f := by
  intro x y z h
  let v : Fin 3 → Var → Role := fun i => if i = 0 then x else if i = 1 then y else z
  let out : Fin 3 → Role := fun i => if i = 0 then f x else if i = 1 then f y else f z
  exact t.atomic_preserves_repeat_triple v (by simpa [v,Atomic.Repeat] using h) out (by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simpa [v,out] using hf _)

/-- Necessity in the atomic S2 classification. No finiteness of the label
set is used in this direction. -/
theorem AtomicRealizes.essentiallyUnary_or_atMostTwo [Finite Var] [Nonempty Role]
    {t : Term Role Var} {f : (Var → Role) → Role} (hf : t.AtomicRealizes f) :
    Atomic.EssentiallyUnary f ∨ Atomic.AtMostTwo f :=
  Atomic.essentiallyUnary_or_atMostTwo f hf.preservesRepeat

/-- On atoms, every atom-preserving term fixing constant atomic inputs is a
projection. The hypothesis fixes only atomic diagonals; idempotence on every
winner set is stronger than needed. -/
theorem atomic_determinacy [Finite Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ha : t.AtomPreserving)
    (hd : ∀ r, t.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) :
    ∃ i : Var, ∀ v : Var → Role,
      t.eval (fun x => WinnerSet.singleton (v x)) = WinnerSet.singleton (v i) := by
  classical
  let _ : Nonempty Role := ⟨three 0⟩
  choose f hf using ha
  have hdiag (r : Role) : f (fun _ => r) = r :=
    WinnerSet.singleton_inj.mp ((hf (fun _ => r)).symm.trans (hd r))
  rcases (AtomicRealizes.essentiallyUnary_or_atMostTwo hf) with ⟨i,g,hg⟩ | htwo
  · have hid (r : Role) : g r = r := (hg (fun _ => r)).symm.trans (hdiag r)
    exact ⟨i,fun v => by rw [hf,hg,hid]⟩
  · exact False.elim (Atomic.not_atMostTwo_of_diagonal three f hdiag htwo)

end Term

end KFOL
