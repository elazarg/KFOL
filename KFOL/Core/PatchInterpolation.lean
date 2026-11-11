module

public import KFOL.Core.RelationalInterpolation

/-! # Finite patch families and smaller interpolation tests

More patches than sampled valuations leave a common interpolant when each
valuation excludes at most one patch. Local interpolation is antitone in the
number of sampled valuations, including empty types and zero samples.
-/

@[expose] public section
namespace KFOL.Core

universe u v w

/-- A finite patch family with one possible exception at every valuation gives
all interpolation tests using fewer rows than there are patches. -/
theorem locallyInterpolable_of_finite_patches {Role : Type u} {Var : Type v}
    {I : Type w} [Fintype I] (n : ℕ) (hn : n < Fintype.card I)
    (terms : I → Term Role Var) (hcore : ∀ i, (terms i).IsCore)
    (f : (Var → WinnerSet Role) → WinnerSet Role)
    (h : ∀ v, ∃ bad : I, ∀ i, i ≠ bad → (terms i).eval v = f v) :
    LocallyInterpolable n f := by
  classical
  intro v
  choose bad hb using fun j => h (v j)
  have hns : ¬Function.Surjective bad := by
    intro hs
    have hh := Fintype.card_le_of_surjective bad hs
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨i,hi⟩ : ∃ i, ∀ j, bad j ≠ i := by
    simpa only [Function.Surjective,not_forall,not_exists] using hns
  exact ⟨terms i,hcore i,fun j => hb j i (Ne.symm (hi j))⟩

/-- Fewer sampled valuations give a weaker interpolation requirement. No
inhabitedness assumptions are needed, even when the valuation type is empty. -/
theorem LocallyInterpolable.of_le {Role : Type u} {Var : Type v}
    {m n : ℕ} {f : (Var → WinnerSet Role) → WinnerSet Role}
    (hf : LocallyInterpolable n f) (hmn : m ≤ n) : LocallyInterpolable m f := by
  classical
  by_cases hv : Nonempty (Var → WinnerSet Role)
  · intro v
    let w : Fin n → Var → WinnerSet Role := fun i =>
      if hi : i.val < m then v ⟨i.val,hi⟩ else Classical.choice hv
    obtain ⟨t,ht,he⟩ := hf w
    refine ⟨t,ht,fun i => ?_⟩
    simpa only [w,Fin.val_castLE,dite_eq_left i.isLt] using he (Fin.castLE hmn i)
  · have hvar : Nonempty Var := by
      by_contra hn
      exact hv ⟨fun j => (hn ⟨j⟩).elim⟩
    obtain ⟨j⟩ := hvar
    intro v
    exact ⟨.var j,trivial,fun i => (hv ⟨v i⟩).elim⟩

theorem locallyInterpolable_antitone {Role : Type u} {Var : Type v}
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Antitone (fun n => LocallyInterpolable n f) :=
  fun _ _ hle hf => hf.of_le hle

end KFOL.Core
