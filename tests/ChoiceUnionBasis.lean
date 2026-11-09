module

public import KFOL.Core.ChoiceUnion

/-! Complete proposed paper statement and arbitrary-owner basis regressions. -/

@[expose] public section

namespace KFOLTest.ChoiceUnionBasis

open KFOL Dissemilattice

universe u v

/-- All seven laws and their exact generating variety are repeated here;
the two semilattice orders are not identified by absorption. -/
theorem choice_union_basis {Role : Type v} (three : Fin 3 ↪ Role) (owner : Role) :
    letI := winnerStructure owner
    theory.ncard = 7 ∧ theory.Finite ∧ Equational.IsBasis (WinnerSet Role) theory ∧
    (∀ (M : Type u) [_str : (Equational.language Symbol).Structure M],
      Equational.InVariety Symbol (WinnerSet Role) M ↔
        Nonempty M ∧
        (∀ x : M, add x x = x) ∧
        (∀ x y : M, add x y = add y x) ∧
        (∀ x y z : M, add (add x y) z = add x (add y z)) ∧
        (∀ x : M, mul x x = x) ∧
        (∀ x y : M, mul x y = mul y x) ∧
        (∀ x y z : M, mul (mul x y) z = mul x (mul y z)) ∧
        (∀ x y z : M, mul x (add y z) = add (mul x y) (mul x z))) := by
  let _ := winnerStructure owner
  refine ⟨theory_ncard,theory_finite,basis_winner three owner,?_⟩
  intro M _
  constructor
  · intro hM
    obtain ⟨hne,hL⟩ := (inVariety_winner_iff_laws three owner M).mp hM
    exact ⟨hne,hL.add_idem,hL.add_comm,hL.add_assoc,hL.mul_idem,hL.mul_comm,hL.mul_assoc,hL.mul_add⟩
  · rintro ⟨hne,h1,h2,h3,h4,h5,h6,h7⟩
    exact (inVariety_winner_iff_laws three owner M).mpr ⟨hne,⟨h1,h2,h3,h4,h5,h6,h7⟩⟩

private def three4 : Fin 3 ↪ Fin 4 := {
  toFun := fun i => ⟨i.val,by omega⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun x : Fin 4 => x.val) h) }

/-- The owner can lie outside the supplied three-role embedding. -/
example :
    letI := winnerStructure (3 : Fin 4)
    Equational.IsBasis (WinnerSet (Fin 4)) theory := basis_winner three4 3

example : theory.ncard = 7 := theory_ncard

example : Three.add .n (Three.mul .b .p) ≠ Three.mul (Three.add .n .b) (Three.add .n .p) :=
  three_not_other_distributive

example : Three.add .n (Three.mul .n .p) ≠ Three.n := by decide

/-- info: 'KFOLTest.ChoiceUnionBasis.choice_union_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.ChoiceUnionBasis.choice_union_basis

end KFOLTest.ChoiceUnionBasis
