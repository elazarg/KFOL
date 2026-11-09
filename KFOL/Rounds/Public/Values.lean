module

public import KFOL.Rounds.Public.Stage

/-! # Exact public-choice sequential-equilibrium distributions -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game
open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The complete one-active-role instance of the serial-SE recursion. Pure
endpoints are allowed; positive weight enforces the corresponding weak
preference, and an interior weight requires indifference. -/
theorem sequentialValues_publicChoice_iff (owner : Role) (left right : Game Role)
    (order : ExplicitOrder Role) (value : PMF Role) :
    value ∈ (publicChoice owner left right).sequentialValues order ↔
      ∃ p ∈ left.sequentialValues order, ∃ q ∈ right.sequentialValues order,
        ∃ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
          (0 < α → (q owner).toReal ≤ (p owner).toReal) ∧
          (α < 1 → (p owner).toReal ≤ (q owner).toReal) ∧
          value = mix α h0 h1 p q := by
  change value ∈ (Game.round (Public.sizes owner)
    (fun a => if (a owner).val = 0 then left else right)).sequentialValues order ↔ _
  rw [sequentialValues_round_iff]
  constructor
  · rintro ⟨p,hp,root,nash,hvalue⟩
    have hp0 : p (Public.action owner 0) ∈ left.sequentialValues order := by
      simpa [Public.action] using hp (Public.action owner 0)
    have hp1 : p (Public.action owner 1) ∈ right.sequentialValues order := by
      simpa [Public.action] using hp (Public.action owner 1)
    exact ⟨_,hp0,_,hp1,Public.weight owner root,Public.weight_nonneg owner root,
      Public.weight_le_one owner root,(Public.stage_nash_iff owner p root).mp nash |>.1,
      (Public.stage_nash_iff owner p root).mp nash |>.2,
      hvalue.trans (Public.stage_law owner p root)⟩
  · rintro ⟨p,hp,q,hq,α,h0,h1,preferLeft,preferRight,hvalue⟩
    let table : ((i : Role) → Fin (Public.sizes owner i+1)) → PMF Role :=
      fun a => if (a owner).val = 0 then p else q
    have table0 : table (Public.action owner 0) = p := by simp [table,Public.action]
    have table1 : table (Public.action owner 1) = q := by simp [table,Public.action]
    refine ⟨table,?_,Public.profile owner α h0 h1,?_,?_⟩
    · intro a
      dsimp only [table]
      split <;> assumption
    · rw [Public.stage_nash_iff,Public.weight_profile,table0,table1]
      exact ⟨preferLeft,preferRight⟩
    · change value = (independentProduct (Public.profile owner α h0 h1)).bind table
      have hl : (independentProduct (Public.profile owner α h0 h1)).bind table =
          mix (Public.weight owner (Public.profile owner α h0 h1))
            (Public.weight_nonneg owner _) (Public.weight_le_one owner _)
            (table (Public.action owner 0)) (table (Public.action owner 1)) :=
        Public.stage_law owner table (Public.profile owner α h0 h1)
      have hm : (independentProduct (Public.profile owner α h0 h1)).bind table = mix α h0 h1 p q := by
        simpa only [Public.weight_profile,table0,table1] using hl
      exact hvalue.trans hm.symm



/-- The same exact law for the independently defined observed SPE values. -/
theorem observedValues_publicChoice_iff (owner : Role) (left right : Game Role)
    (value : PMF Role) :
    value ∈ (publicChoice owner left right).observedValues ↔
      ∃ p ∈ left.observedValues, ∃ q ∈ right.observedValues,
        ∃ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
          (0 < α → (q owner).toReal ≤ (p owner).toReal) ∧
          (α < 1 → (p owner).toReal ≤ (q owner).toReal) ∧
          value = mix α h0 h1 p q := by
  let order : ExplicitOrder Role := ⟨Fintype.card Role,(Fintype.equivFin Role).symm⟩
  simpa only [sequentialValues_eq_observedValues] using
    sequentialValues_publicChoice_iff owner left right order value

end KFOL.Rounds.Game
