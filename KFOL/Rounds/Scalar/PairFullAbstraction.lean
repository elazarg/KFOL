module

public import KFOL.Rounds.Scalar.FullAbstraction
public import KFOL.Rounds.TwoPlayers.Values

/-! # Boolean observation completeness for arbitrary two-role games -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.TwoPlayers

open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- For arbitrary actual finite games whose effective actors and terminal
winners lie in a designated pair, equality of their complete canonical
sequential-equilibrium law sets is characterized by
one third role's possible victory in Boolean-menu contexts. The games being
compared may have arbitrary finite menus. -/
theorem sequentialValues_eq_iff_boolean_observation (left right : Game Role)
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hleft : left.UsesOnly a b) (hright : right.UsesOnly a b) (order : ExplicitOrder Role) :
    left.sequentialValues order = right.sequentialValues order ↔
      ∀ context : Context Role, context.BooleanMenus →
        (c ∈ possibleWinners ((context.fill left).sequentialValues order) ↔
          c ∈ possibleWinners ((context.fill right).sequentialValues order)) := by
  constructor
  · intro hv context _
    rw [Scalar.sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    obtain ⟨x,hx0,hx1,hx⟩ := sequentialValues_scalar a b hab left hleft order
    obtain ⟨y,hy0,hy1,hy⟩ := sequentialValues_scalar a b hab right hright order
    have he := (Scalar.singleton_third_boolean_full_abstraction left right a b c hab hac hbc
      order x y hx0 hx1 hy0 hy1 hx hy).2 equivalent
    subst y
    exact hx.trans hy.symm

/-- Full possible-winner sets in Boolean contexts give the same exact
criterion, without any scalar syntax or caller-supplied uniqueness premise. -/
theorem sequentialValues_eq_iff_boolean_winners (left right : Game Role)
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hleft : left.UsesOnly a b) (hright : right.UsesOnly a b) (order : ExplicitOrder Role) :
    left.sequentialValues order = right.sequentialValues order ↔
      ∀ context : Context Role, context.BooleanMenus →
        possibleWinners ((context.fill left).sequentialValues order) =
          possibleWinners ((context.fill right).sequentialValues order) := by
  constructor
  · intro hv context _
    rw [Scalar.sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    apply (sequentialValues_eq_iff_boolean_observation left right a b c hab hac hbc
      hleft hright order).2
    intro context hc
    rw [equivalent context hc]

/-- A countable family of literal one-hole Boolean comparisons suffices to
recover the complete equilibrium winner law of every two-role game. -/
theorem sequentialValues_eq_iff_rational_observation (left right : Game Role)
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hleft : left.UsesOnly a b) (hright : right.UsesOnly a b) (order : ExplicitOrder Role) :
    left.sequentialValues order = right.sequentialValues order ↔
      ∀ probe : ScalarTerm, probe.UnaryGenerated →
        (c ∈ possibleWinners ((publicChoice a left (probe.game a c)).sequentialValues order) ↔
          c ∈ possibleWinners ((publicChoice a right (probe.game a c)).sequentialValues order)) := by
  obtain ⟨x,hx0,hx1,hx⟩ := sequentialValues_scalar a b hab left hleft order
  obtain ⟨y,hy0,hy1,hy⟩ := sequentialValues_scalar a b hab right hright order
  have hs := Scalar.singleton_scalar_eq_iff_rational_tests left right a b c hab hac hbc
    order x y hx0 hx1 hy0 hy1 hx hy
  constructor
  · intro hv
    apply hs.mp
    have he : Scalar.distribution a b x hx0 hx1 = Scalar.distribution a b y hy0 hy1 :=
      Set.singleton_injective (hx.symm.trans (hv.trans hy))
    have hc := congrArg (fun law => (law a).toReal) he
    simpa only [Scalar.distribution_a a b hab] using hc
  · intro observations
    have he := hs.mpr observations
    subst y
    exact hx.trans hy.symm

end KFOL.Rounds.Game.TwoPlayers
