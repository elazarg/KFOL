module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation

/-! # Least reachable scope of a prime exclusion guard -/

@[expose] public section

namespace KFOL.Core.ReachableGuardScope

variable {V R : Type*}

/-- A legal probe only posts owners allowed by the facet and the guard. -/
def Legal (allowed : V → R → Prop) (probe : V → Option R) : Prop :=
  ∀ v r, probe v = some r → allowed v r

/-- Reachability along edges whose owner disagrees with the destination posting. -/
def Reach (edge : V → R → V → Prop) (head : V) (probe : V → Option R) : Set V :=
  {v | Relation.ReflTransGen (fun u v => ∃ r, edge u r v ∧ probe v ≠ some r) head v}

/-- The exterior of a scope can be posted so that no disagreement leaves it. -/
def Closed (edge : V → R → V → Prop) (allowed : V → R → Prop)
    (head : V) (scope : Set V) : Prop :=
  head ∈ scope ∧ ∀ v ∉ scope, ∃ posting : Option R,
    (∀ r, posting = some r → allowed v r) ∧
    (∀ u ∈ scope, ∀ r, edge u r v → posting = some r)

def leastScope (edge : V → R → V → Prop) (allowed : V → R → Prop) (head : V) : Set V :=
  {v | ∀ scope, Closed edge allowed head scope → v ∈ scope}

theorem reach_closed {edge : V → R → V → Prop} {allowed : V → R → Prop}
    {head : V} {probe : V → Option R} (hlegal : Legal allowed probe) :
    Closed edge allowed head (Reach edge head probe) := by
  classical
  refine ⟨Relation.ReflTransGen.refl, ?_⟩
  intro v hv
  refine ⟨probe v, hlegal v, ?_⟩
  intro u hu r hedge
  by_contra hne
  exact hv (Relation.ReflTransGen.tail hu ⟨r, hedge, hne⟩)

theorem leastScope_closed (edge : V → R → V → Prop) (allowed : V → R → Prop) (head : V) :
    Closed edge allowed head (leastScope edge allowed head) := by
  classical
  refine ⟨fun scope hscope => hscope.1, ?_⟩
  intro v hv
  have hout : ∃ scope, Closed edge allowed head scope ∧ v ∉ scope := by
    by_contra h
    apply hv
    intro scope hscope
    by_contra hmem
    exact h ⟨scope, hscope, hmem⟩
  obtain ⟨scope, hscope, hmem⟩ := hout
  obtain ⟨posting, hlegal, hagree⟩ := hscope.2 v hmem
  exact ⟨posting, hlegal, fun u hu => hagree u (hu scope hscope)⟩

theorem leastScope_subset_reach {edge : V → R → V → Prop} {allowed : V → R → Prop}
    {head : V} {probe : V → Option R} (hlegal : Legal allowed probe) :
    leastScope edge allowed head ⊆ Reach edge head probe :=
  fun _ hv => hv _ (reach_closed hlegal)

/-- Directly excluded head arrows can be accounted for entirely by seeding
their destinations. The original menus then suffice for testing closure. -/
theorem closed_with_exclusions_iff {edge : V → R → V → Prop}
    {allowed excluded : V → R → Prop} {head : V} {scope : Set V}
    (hdirect : ∀ v r, excluded v r → edge head r v) :
    Closed edge (fun v r => allowed v r ∧ ¬ excluded v r) head scope ↔
      Closed edge allowed head scope ∧ (∀ v r, excluded v r → v ∈ scope) := by
  classical
  constructor
  · intro h
    refine ⟨⟨h.1, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨posting, hlegal, hagree⟩ := h.2 v hv
      exact ⟨posting, fun r hr => (hlegal r hr).1, hagree⟩
    · intro v r hex
      by_contra hv
      obtain ⟨posting, hlegal, hagree⟩ := h.2 v hv
      exact (hlegal r (hagree head h.1 r (hdirect v r hex))).2 hex
  · rintro ⟨h, hseed⟩
    refine ⟨h.1, ?_⟩
    intro v hv
    obtain ⟨posting, hlegal, hagree⟩ := h.2 v hv
    exact ⟨posting, fun r hr => ⟨hlegal r hr, fun hex => hv (hseed v r hex)⟩, hagree⟩

/-- Every legal interior assignment extends to a probe that stays in a closed scope. -/
theorem Closed.extend {edge : V → R → V → Prop} {allowed : V → R → Prop}
    {head : V} {scope : Set V} (hscope : Closed edge allowed head scope)
    (localProbe : V → Option R)
    (hlocal : ∀ v ∈ scope, ∀ r, localProbe v = some r → allowed v r) :
    ∃ probe, Legal allowed probe ∧ (∀ v ∈ scope, probe v = localProbe v) ∧
      Reach edge head probe ⊆ scope := by
  classical
  let probe := fun v => if hv : v ∈ scope then localProbe v else
    Classical.choose (hscope.2 v hv)
  refine ⟨probe, ?_, fun v hv => dite_eq_left hv, ?_⟩
  · intro v r hr
    by_cases hv : v ∈ scope
    · exact hlocal v hv r ((dite_eq_left hv).symm.trans hr)
    · exact (Classical.choose_spec (hscope.2 v hv)).1 r ((dite_eq_right hv).symm.trans hr)
  · intro v hv
    change Relation.ReflTransGen (fun u v => ∃ r, edge u r v ∧ probe v ≠ some r)
      head v at hv
    induction hv with
    | refl => exact hscope.1
    | tail _ step ih =>
      obtain ⟨r, hedge, hne⟩ := step
      by_contra hout
      exact hne ((dite_eq_right hout).trans
        ((Classical.choose_spec (hscope.2 _ hout)).2 _ ih r hedge))

/-- Every legal interior assignment on the least scope attains exactly that scope. -/
theorem leastScope_attained (edge : V → R → V → Prop) (allowed : V → R → Prop) (head : V)
    (localProbe : V → Option R)
    (hlocal : ∀ v ∈ leastScope edge allowed head, ∀ r, localProbe v = some r → allowed v r) :
    ∃ probe, Legal allowed probe ∧
      (∀ v ∈ leastScope edge allowed head, probe v = localProbe v) ∧
      Reach edge head probe = leastScope edge allowed head := by
  obtain ⟨probe, hlegal, hagree, hsub⟩ :=
    (leastScope_closed edge allowed head).extend localProbe hlocal
  exact ⟨probe, hlegal, hagree, Set.Subset.antisymm hsub (leastScope_subset_reach hlegal)⟩

end KFOL.Core.ReachableGuardScope
