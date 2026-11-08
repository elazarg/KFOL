module

public import KFOL.Algebra.TestDomains
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-! # The exact size of the smallest complete test domain -/

@[expose] public section

namespace KFOL

universe u

/-- Unordered pairs with repetition represent exactly the singleton-or-pair values.
This is a bijection of the actual winner sets, rather than a count of syntax. -/
noncomputable def pairValuesEquiv (Role : Type u) :
    Sym2 Role ≃ {A : WinnerSet Role // ∃ a b, A.val = {a, b}} := by
  let f : Sym2 Role → {A : WinnerSet Role // ∃ a b, A.val = {a, b}} := fun z =>
    ⟨⟨(z : Set Role), z.out.1, z.out_fst_mem⟩, by
      induction z using Sym2.ind with
      | _ a b => exact ⟨a, b, by ext x; exact Sym2.mem_iff⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact SetLike.coe_injective (congrArg (fun A => A.val.val) h)
  · rintro ⟨A, a, b, hab⟩
    refine ⟨Sym2.mk a b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (Sym2.mk a b : Set Role) = A.val
    rw [hab]
    ext x
    exact Sym2.mem_iff

/-- Exact counting by the preceding bijection, for every finite role type,
including the empty, one-role and two-role cases. -/
theorem card_pairValues (Role : Type u) [Fintype Role] :
    Nat.card {A : WinnerSet Role // ∃ a b, A.val = {a, b}} =
      Fintype.card Role * (Fintype.card Role + 1) / 2 := by
  classical
  rw [← Nat.card_congr (pairValuesEquiv Role), Nat.card_eq_fintype_card,
    Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel_right, Nat.mul_comm]

end KFOL
