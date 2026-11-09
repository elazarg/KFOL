module

public import KFOL.Owner.Public

/-! # Agreement of two owner observations does not determine an equation -/
@[expose] public section
namespace KFOL.Owner
universe u
variable {Role : Type u}

private theorem value_observations (a b : Role) (Z Y1 Y2 C : WinnerSet Role) :
    let W := Y1.reset (Y2.reset Z)
    let T := (WinnerSet.guardedChoice a Z Y1 C).reset
      ((WinnerSet.guardedChoice b Z Y2 C).reset W)
    (a ∈ (C.reset T).val ↔ a ∈ T.val) ∧ (b ∈ (C.reset T).val ↔ b ∈ T.val) := by
  let W := Y1.reset (Y2.reset Z)
  let U := (WinnerSet.guardedChoice b Z Y2 C).reset W
  let T := (WinnerSet.guardedChoice a Z Y1 C).reset U
  change (a ∈ (C.reset T).val ↔ a ∈ T.val) ∧ (b ∈ (C.reset T).val ↔ b ∈ T.val)
  have hW : W.Ambiguous ↔ Z.Ambiguous := by simp only [W,WinnerSet.ambiguous_reset]
  have hU : U.Ambiguous ↔ Z.Ambiguous := (WinnerSet.ambiguous_reset _ _).trans hW
  have hT : T.Ambiguous ↔ Z.Ambiguous := (WinnerSet.ambiguous_reset _ _).trans hU
  have ownA (hz : Z.Ambiguous) (hc : a ∈ C.val) : a ∈ T.val := by
    apply (WinnerSet.mem_reset _ _ a).mpr
    refine Or.inr ⟨hU.mpr hz,?_⟩
    apply (WinnerSet.mem_reset _ _ a).mpr
    exact Or.inr ⟨hz,(WinnerSet.mem_choice_owner a Y1 C).mpr (Or.inr hc)⟩
  have ownB (hz : Z.Ambiguous) (hc : b ∈ C.val) : b ∈ T.val := by
    apply (WinnerSet.mem_reset _ _ b).mpr
    apply Or.inl
    apply (WinnerSet.mem_reset _ _ b).mpr
    refine Or.inr ⟨hW.mpr hz,?_⟩
    apply (WinnerSet.mem_reset _ _ b).mpr
    exact Or.inr ⟨hz,(WinnerSet.mem_choice_owner b Y2 C).mpr (Or.inr hc)⟩
  constructor
  · rw [WinnerSet.mem_reset]
    exact ⟨fun h => h.elim id (fun h => ownA (hT.mp h.1) h.2),Or.inl⟩
  · rw [WinnerSet.mem_reset]
    exact ⟨fun h => h.elim id (fun h => ownB (hT.mp h.1) h.2),Or.inl⟩

/-- The equality of both owners' observations is universal in the actual
native four-input reset/H syntax; no restriction on valuations is imposed. -/
theorem joint_observations_agree (a b : Role) (v : Fin 4 → WinnerSet Role) :
    (a ∈ ((jointObservationEquation a b).1.eval v).val ↔
      a ∈ ((jointObservationEquation a b).2.eval v).val) ∧
    (b ∈ ((jointObservationEquation a b).1.eval v).val ↔
      b ∈ ((jointObservationEquation a b).2.eval v).val) := by
  exact value_observations a b (v 0) (v 1) (v 2) (v 3)

/-- The same original equation fails on a third role's actual marker value. -/
theorem joint_observations_separate (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let v := jointObservationValuation a b c
    (jointObservationEquation a b).1.eval v ≠ (jointObservationEquation a b).2.eval v := by
  classical
  have hz : ((WinnerSet.singleton a).union (WinnerSet.singleton b)).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ a b hab (by simp [WinnerSet.union]) (by simp [WinnerSet.union])
  have ha : WinnerSet.choice a (WinnerSet.singleton a) (WinnerSet.singleton c) = WinnerSet.singleton a := by
    simp [WinnerSet.choice]
  have hb : WinnerSet.choice b (WinnerSet.singleton b) (WinnerSet.singleton c) = WinnerSet.singleton b := by
    simp [WinnerSet.choice]
  dsimp only
  intro he
  have hm := congrArg (fun A : WinnerSet Role => c ∈ A.val) he
  simp only [jointObservationEquation,Term.eval_step,Term.eval_guarded,Term.eval_var,
    jointObservationValuation,WinnerSet.guardedChoice] at hm
  simp only [show (3 : Fin 4) ≠ 0 by decide,show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide,show (2 : Fin 4) ≠ 0 by decide,
    show (2 : Fin 4) ≠ 1 by decide,show (1 : Fin 4) ≠ 0 by decide,
    ite_false,ite_true,ha,hb] at hm
  have hrA : (WinnerSet.singleton a).reset
      ((WinnerSet.singleton a).union (WinnerSet.singleton b)) =
      (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
    rw [WinnerSet.reset_of_ambiguous _ _ hz]
    apply Subtype.ext
    exact Set.union_eq_right.mpr (fun _ hi => Or.inl hi)
  have hrB : (WinnerSet.singleton b).reset
      ((WinnerSet.singleton a).union (WinnerSet.singleton b)) =
      (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
    rw [WinnerSet.reset_of_ambiguous _ _ hz]
    apply Subtype.ext
    exact Set.union_eq_right.mpr (fun _ hi => Or.inr hi)
  simp only [hrA,hrB,WinnerSet.reset_self] at hm
  have hnot : c ∉ ((WinnerSet.singleton a).union (WinnerSet.singleton b)).val := by
    simp [WinnerSet.union,Ne.symm hac,Ne.symm hbc]
  exact hnot (hm.mp ((WinnerSet.mem_reset _ _ c).mpr (Or.inr ⟨hz,rfl⟩)))

end KFOL.Owner
