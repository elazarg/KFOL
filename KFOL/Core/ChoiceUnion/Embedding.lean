module

public import KFOL.Core.ChoiceUnion.Laws
public import KFOL.Equational.Preservation

/-! # The actual three-element subalgebra for any specified owner -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u

open FirstOrder

variable {Role : Type u}

/-- Three nested nonempty winner sets with the specified owner at their base. -/
def threeEmbed (owner b c : Role) : Three → WinnerSet Role
  | .b => WinnerSet.singleton owner
  | .n => (WinnerSet.singleton owner).union (WinnerSet.singleton b)
  | .p => ((WinnerSet.singleton owner).union (WinnerSet.singleton b)).union (WinnerSet.singleton c)

theorem threeEmbed_injective (owner b c : Role) (hb : b ≠ owner) (hc : c ≠ owner) (hcb : c ≠ b) :
    Function.Injective (threeEmbed owner b c) := by
  intro x y he
  have hB := congrArg (fun A : WinnerSet Role => b ∈ A.val) he
  have hC := congrArg (fun A : WinnerSet Role => c ∈ A.val) he
  cases x <;> cases y
  all_goals first | rfl | simp [threeEmbed,WinnerSet.singleton,WinnerSet.union,hb,hc,hcb] at hB hC

theorem threeEmbed_add (owner b c : Role) (x y : Three) :
    threeEmbed owner b c (Three.add x y) = (threeEmbed owner b c x).union (threeEmbed owner b c y) := by
  cases x <;> cases y
  all_goals apply Subtype.ext
  all_goals ext role
  all_goals simp only [threeEmbed,Three.add,WinnerSet.singleton,WinnerSet.union,Set.mem_union,Set.mem_singleton_iff]
  all_goals tauto

theorem threeEmbed_eq_singleton (owner b c : Role) (hb : b ≠ owner) (hc : c ≠ owner) (hcb : c ≠ b)
    (x : Three) : threeEmbed owner b c x = WinnerSet.singleton owner ↔ x = .b := by
  exact ⟨fun he => threeEmbed_injective owner b c hb hc hcb he, fun he => he ▸ rfl⟩

theorem Three.mul_eq_ite (x y : Three) :
    Three.mul x y = if x = .b ∨ y = .b then .b else Three.add x y := by
  cases x <;> cases y <;> rfl

theorem threeEmbed_mul (owner b c : Role) (hb : b ≠ owner) (hc : c ≠ owner) (hcb : c ≠ b)
    (x y : Three) :
    threeEmbed owner b c (Three.mul x y) = WinnerSet.choice owner (threeEmbed owner b c x) (threeEmbed owner b c y) := by
  classical
  rw [Three.mul_eq_ite]
  simp only [apply_ite,WinnerSet.choice,threeEmbed_eq_singleton owner b c hb hc hcb,
    threeEmbed_add]
  split_ifs <;> rfl

/-- An actual language homomorphism, with the original owner and union
operations on its target. -/
def threeHom (owner b c : Role) (hb : b ≠ owner) (hc : c ≠ owner) (hcb : c ≠ b) :
    letI := Three.structureOf
    letI := winnerStructure owner
    Three →[Equational.language Symbol] WinnerSet Role := by
  letI := Three.structureOf
  letI := winnerStructure owner
  refine {
    toFun := threeEmbed owner b c
    map_fun' := ?_ }
  intro n sym args
  cases sym with
  | join =>
    rw [funMap_join,funMap_join]
    exact threeEmbed_add owner b c (args 0) (args 1)
  | mul =>
    rw [funMap_mul,funMap_mul]
    exact threeEmbed_mul owner b c hb hc hcb (args 0) (args 1)

/-- The role count is used only to find two distinct roles other than the
specified owner, not to assume that the owner is one fixed embedding position. -/
theorem three_in_winner_variety (three : Fin 3 ↪ Role) (owner : Role) :
    letI := Three.structureOf
    letI := winnerStructure owner
    Equational.InVariety Symbol (WinnerSet Role) Three := by
  let _ := Three.structureOf
  let _ := winnerStructure owner
  let _ : Nonempty Three := ⟨.b⟩
  let _ : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton owner⟩
  obtain ⟨b,hb,_⟩ := exists_role_outside_pair three owner owner
  obtain ⟨c,hca,hcb⟩ := exists_role_outside_pair three owner b
  exact (Equational.InVariety.refl (σ := Symbol) (M := WinnerSet Role)).of_injective
    (threeHom owner b c hb hca hcb) (threeEmbed_injective owner b c hb hca hcb)

end KFOL.Dissemilattice
