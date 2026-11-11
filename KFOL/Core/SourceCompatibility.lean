module

public import KFOL.Core.SourceNormalForm
public import KFOL.Core.Cuts

/-! # Exact compatibility of prime source-guard families

Only the observer bit is constrained at each probe. Atomic cuts synthesize
witnesses satisfying every negative observation; finite union joins witnesses
for all positive observations. Canonicality then recovers the exact guards.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

private theorem subset_allowance_iff (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop)
    (q : ProbeIndex Role Var) (A : WinnerSet Role) :
    A.val ⊆ (allowance three F q).val ↔ (q.1 ∈ A.val → F q.1 q.2.1 q.2.2) := by
  classical
  by_cases h : F q.1 q.2.1 q.2.2
  · simp [allowance, h]
  · simp only [allowance, ite_eq_right h, representative, PlayerView.representative]
    constructor
    · intro hs hm; exact (hs hm rfl).elim
    · intro hs r hr he; subst r; exact (h (hs hr)).elim

/-- A core term has a positive source observation, even when the variable type
has not been assumed nonempty. This rejects fictitious nullary constants. -/
theorem exists_positive_probe (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore) :
    ∃ k j p, k ∈ (t.eval (probe three k j p)).val := by
  let k := three 0
  have hm : k ∈ (t.eval (fun _ => WinnerSet.singleton k)).val := by
    rw [ht.eval_diagonal]
    exact Set.mem_singleton k
  obtain ⟨j, _, hj⟩ := (membership_iff_source three t ht _ k).mp hm
  exact ⟨k, j, _, hj⟩

/-- Exact simultaneous synthesis of an arbitrary Boolean coefficient array.
Neither nonempty output values nor source self-consistency are assumed. -/
theorem compatible_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) :
    Compatible three F ↔ ∃ t : Term Role Var, t.IsCore ∧
      ∀ k j p, (k ∈ (t.eval (probe three k j p)).val ↔ F k j p) := by
  classical
  constructor
  · rintro ⟨⟨k₀, j₀, p₀, h₀⟩, h⟩
    obtain ⟨t, ht, hb, he⟩ := Cuts.maximum_of_saturated three
      (fun q : ProbeIndex Role Var => probe three q.1 q.2.1 q.2.2)
      (allowance three F) (fun _ => .target) ⟨⟨k₀, j₀, p₀⟩, k₀, h k₀ j₀ p₀ h₀⟩
    refine ⟨t, ht, ?_⟩
    intro k j p
    constructor
    · exact (subset_allowance_iff three F ⟨k, j, p⟩ _).mp (hb ⟨k, j, p⟩)
    · intro hp
      exact (he ⟨k, j, p⟩ k).mpr (h k j p hp)
  · rintro ⟨t, ht, he⟩
    obtain ⟨k₀, j₀, p₀, h₀⟩ := exists_positive_probe three t ht
    refine ⟨⟨k₀, j₀, p₀, (he k₀ j₀ p₀).mp h₀⟩, ?_⟩
    intro k j p hp
    apply (FiniteHorn.mem_saturate_iff _ _).mpr
    apply Cuts.derives_complete _ _ t ht (fun _ => .target)
    · intro q
      exact (subset_allowance_iff three F q _).mpr (he q.1 q.2.1 q.2.2).mp
    · exact (he k j p).mpr hp

/-- Exact, term-free joint-realizability conditions on all source families. -/
theorem admissible_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    Admissible three G ↔ ∃ t : Term Role Var, t.IsCore ∧
      normalForm three (fun v => t.eval v) = G := by
  classical
  constructor
  · rintro ⟨hc, hp⟩
    obtain ⟨t, ht, he⟩ := (compatible_iff three _).mp hp
    refine ⟨t, ht, ?_⟩
    funext k j
    apply Finset.ext
    intro g
    rw [mem_normalForm, hc k j g]
    have hf : (fun p => k ∈ (t.eval (probe three k j p)).val) = coefficients G k j :=
      funext (fun p => propext (he k j p))
    rw [hf]
  · rintro ⟨t, ht, rfl⟩
    have he (k : Role) (j : Var) (p : Pattern k j) :
        k ∈ (t.eval (probe three k j p)).val ↔
          coefficients (normalForm three (fun v => t.eval v)) k j p :=
      coefficient_iff_guard three t k j p
    refine ⟨?_, (compatible_iff three _).mpr ⟨t, ht, he⟩⟩
    intro k j g
    rw [mem_normalForm]
    have hf : (fun p => k ∈ (t.eval (probe three k j p)).val) =
        coefficients (normalForm three (fun v => t.eval v)) k j :=
      funext (fun p => propext (he k j p))
    rw [hf]

/-- Each retained bit has a witness obeying all negative observations. -/
theorem interior_iff_witness [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) (k : Role) (j : Var) (p : Pattern k j) :
    interior three F k j p ↔ ∃ t : Term Role Var, t.IsCore ∧
      (∀ a b q, a ∈ (t.eval (probe three a b q)).val → F a b q) ∧
      k ∈ (t.eval (probe three k j p)).val := by
  classical
  constructor
  · intro h
    obtain ⟨t, ht, hb, hm⟩ := Cuts.derives_sound
      (fun q : ProbeIndex Role Var => probe three q.1 q.2.1 q.2.2)
      (allowance three F) ((FiniteHorn.mem_saturate_iff _ _).mp h)
    exact ⟨t, ht, fun a b q => (subset_allowance_iff three F ⟨a, b, q⟩ _).mp
      (hb ⟨a, b, q⟩), hm⟩
  · rintro ⟨t, ht, hb, hm⟩
    apply (FiniteHorn.mem_saturate_iff _ _).mpr
    apply Cuts.derives_complete _ _ t ht (fun _ => .target)
    · intro q
      exact (subset_allowance_iff three F q _).mpr (hb q.1 q.2.1 q.2.2)
    · exact hm

/-- Every jointly realizable array below the specification lies below its interior. -/
theorem interior_greatest [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop)
    (t : Term Role Var) (ht : t.IsCore)
    (hb : ∀ k j p, k ∈ (t.eval (probe three k j p)).val → F k j p) :
    ∀ k j p, k ∈ (t.eval (probe three k j p)).val → interior three F k j p :=
  fun k j p hm => (interior_iff_witness three F k j p).mpr ⟨t, ht, hb, hm⟩

/-- Saturation never adds a bit forbidden by its specification. -/
theorem interior_le [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) : interior three F ≤ F := by
  intro k j p h
  obtain ⟨_, _, hb, hm⟩ := (interior_iff_witness three F k j p).mp h
  exact hb k j p hm

/-- Weakening the allowed coefficients cannot remove a bounded witness. -/
theorem interior_mono [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role) :
    Monotone (interior (Var := Var) three) := by
  intro F G h k j p hp
  obtain ⟨t, ht, hb, hm⟩ := (interior_iff_witness three F k j p).mp hp
  exact (interior_iff_witness three G k j p).mpr
    ⟨t, ht, fun a b q hq => h a b q (hb a b q hq), hm⟩

/-- A second pass makes no further deletions. -/
theorem interior_idem [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) :
    interior three (interior three F) = interior three F := by
  funext k j p
  apply propext
  constructor
  · exact interior_le three _ k j p
  · intro h
    obtain ⟨t, ht, hb, hm⟩ := (interior_iff_witness three F k j p).mp h
    refine (interior_iff_witness three _ k j p).mpr ⟨t, ht, ?_, hm⟩
    intro a b q hq
    exact (interior_iff_witness three F a b q).mpr ⟨t, ht, hb, hq⟩

/-- Every nonzero interior is realized by one term, simultaneously at every bit. -/
theorem interior_realizes [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop)
    (h : ∃ k j p, interior three F k j p) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ k j p,
      (k ∈ (t.eval (probe three k j p)).val ↔ interior three F k j p) := by
  classical
  obtain ⟨k, j, p, hp⟩ := h
  obtain ⟨t, ht, _, he⟩ := Cuts.maximum_of_saturated three
    (fun q : ProbeIndex Role Var => probe three q.1 q.2.1 q.2.2)
    (allowance three F) (fun _ => .target) ⟨⟨k, j, p⟩, k, hp⟩
  exact ⟨t, ht, fun a b q => he ⟨a, b, q⟩ a⟩

/-- Nonzero fixed points are precisely the compatible coefficient arrays. -/
theorem compatible_iff_fixed [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) :
    Compatible three F ↔ (∃ k j p, F k j p) ∧ interior three F = F := by
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    funext k j p
    exact propext ⟨interior_le three F k j p, he k j p⟩
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    intro k j p h
    rwa [he]

/-- A direct compatibility criterion on guard data, with no prescribed value table. -/
theorem guard_fixed_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (Canonical G ∧ (∃ k j p, coefficients G k j p) ∧
      interior three (coefficients G) = coefficients G) ↔
      ∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G := by
  rw [← compatible_iff_fixed]
  exact admissible_iff three G

end KFOL.Core.Sources
