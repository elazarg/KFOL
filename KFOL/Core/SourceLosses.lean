module

public import KFOL.Definitions.CoreLosses
public import KFOL.Core.SourceNormalForm

/-! # Losses determine the prime guards

For an operation with a system of losses, the coefficient at a source is the
absence of a posted loss, the prime guards are the minimal sets of postings
meeting every loss, and the guards reconstruct the operation. The operation
need not be a term operation.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

namespace LossSystem

variable {f : (Var → WinnerSet Role) → WinnerSet Role}
  {zeros : Var → List (List (Var × Role))}

theorem posted_probe (three : Fin 3 ↪ Role) (h : LossSystem f zeros) {k : Role} {j : Var}
    (p : Pattern k j) {z : List (Var × Role)} (hz : z ∈ zeros j) :
    Posted z k (probe three k j p) ↔ PostedAt z k j p := by
  constructor
  · intro hp q hq
    obtain ⟨hr, hv⟩ := hp q hq
    have hi := h.off_source j z hz q hq
    refine ⟨hi, hr, ?_⟩
    rw [probe_other three k j p q.1 hi] at hv
    exact (representative_atom_iff three k _ ⟨q.2, hr⟩).1 hv
  · intro hp q hq
    obtain ⟨hi, hr, hv⟩ := hp q hq
    refine ⟨hr, ?_⟩
    rw [probe_other three k j p q.1 hi]
    exact (representative_atom_iff three k _ ⟨q.2, hr⟩).2 hv

/-- The coefficient at a source is the absence of a posted loss. -/
theorem coefficient_iff (three : Fin 3 ↪ Role) (h : LossSystem f zeros) (k : Role) (j : Var)
    (p : Pattern k j) :
    k ∈ (f (probe three k j p)).val ↔ ∀ z ∈ zeros j, ¬PostedAt z k j p := by
  rw [h.mem_iff]
  constructor
  · rintro ⟨i, hi, hz⟩ z hzj hp
    obtain rfl := (mem_probe_iff three k j p i).1 hi
    exact hz z hzj ((h.posted_probe three p hzj).2 hp)
  · intro hz
    exact ⟨j, (mem_probe_iff three k j p j).2 rfl,
      fun z hzj hp => hz z hzj ((h.posted_probe three p hzj).1 hp)⟩

theorem postedAt_pattern (h : LossSystem f zeros) (k : Role) (j : Var)
    (v : Var → WinnerSet Role) {z : List (Var × Role)} (hz : z ∈ zeros j) :
    PostedAt z k j (pattern k j v) ↔ Posted z k v := by
  constructor
  · intro hp q hq
    obtain ⟨hi, hr, hv⟩ := hp q hq
    exact ⟨hr, (passive_eq_atom_iff k (v q.1) ⟨q.2, hr⟩).1 hv⟩
  · intro hp q hq
    obtain ⟨hr, hv⟩ := hp q hq
    exact ⟨h.off_source j z hz q hq, hr, (passive_eq_atom_iff k (v q.1) ⟨q.2, hr⟩).2 hv⟩

theorem coefficient_mono (three : Fin 3 ↪ Role) (h : LossSystem f zeros) (k : Role) (j : Var) :
    Monotone (fun p : Pattern k j => k ∈ (f (probe three k j p)).val) := by
  intro p p' hpp hp
  rw [h.coefficient_iff three] at hp ⊢
  intro z hz hpost
  refine hp z hz fun q hq => ?_
  obtain ⟨hi, hr, hv⟩ := hpost q hq
  refine ⟨hi, hr, ?_⟩
  have hle := hpp ⟨q.1, hi⟩
  change p' ⟨q.1, hi⟩ = .neutral ∨ p ⟨q.1, hi⟩ = p' ⟨q.1, hi⟩ at hle
  rcases hle with hn | he
  · rw [hv] at hn
    cases hn
  · rw [he]
    exact hv

/-- The prime guards reconstruct the operation. -/
theorem meaning_normalForm [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (h : LossSystem f zeros) (v : Var → WinnerSet Role) :
    meaning (normalForm three f) v = (f v).val := by
  ext k
  rw [h.mem_iff]
  change (∃ j, k ∈ (v j).val ∧ ∃ g ∈ normalForm three f k j, Enabled g (pattern k j v)) ↔ _
  refine exists_congr fun j => and_congr_right fun _ => ?_
  have e := iff_enabled_prime _ (h.coefficient_mono three k j) (pattern k j v)
  simp only [mem_normalForm]
  rw [← e, h.coefficient_iff three]
  exact forall₂_congr fun z hz => not_congr (h.postedAt_pattern k j v hz)

/-- A core term with the same prime guards realizes the operation. -/
theorem eq_of_normalForm_eq [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (h : LossSystem f zeros) (t : Term Role Var) (ht : t.IsCore)
    (e : normalForm three (fun v => t.eval v) = normalForm three f)
    (v : Var → WinnerSet Role) : t.eval v = f v := by
  apply Subtype.ext
  rw [← normalForm_correct three t ht v, e, h.meaning_normalForm three v]

/-- A guard is sufficient exactly when it meets every loss that does not
name the observer. -/
theorem sound_iff (three : Fin 3 ↪ Role) (h : LossSystem f zeros) (k : Role) (j : Var)
    (g : Guard k j) :
    Sound (fun p => k ∈ (f (probe three k j p)).val) g ↔ MeetsAll (zeros j) g := by
  classical
  constructor
  · intro hs z hz hk
    by_contra hmeet
    let p : Pattern k j := fun i =>
      if hx : ∃ r, (i.val, r) ∈ z then .atom ⟨hx.choose, hk _ hx.choose_spec⟩ else .neutral
    have hen : Enabled g p := by
      intro a ha hpa
      apply hmeet
      refine ⟨a, ha, ?_⟩
      by_cases hx : ∃ r, (a.1.val, r) ∈ z
      · have hpa' : Passive.atom ⟨hx.choose, hk _ hx.choose_spec⟩ = Passive.atom a.2 := by
          simpa only [p, hx, ↓reduceDIte] using hpa
        have hc : hx.choose = a.2.val := congrArg Subtype.val (Passive.atom.inj hpa')
        rw [← hc]
        exact hx.choose_spec
      · have hpa' : (Passive.neutral : Passive k) = Passive.atom a.2 := by
          simpa only [p, hx, ↓reduceDIte] using hpa
        cases hpa'
    have hf : k ∈ (f (probe three k j p)).val := hs p hen
    rw [h.coefficient_iff three] at hf
    refine hf z hz fun q hq => ?_
    have hi := h.off_source j z hz q hq
    have hx : ∃ r, ((⟨q.1, hi⟩ : {i : Var // i ≠ j}).val, r) ∈ z := ⟨q.2, hq⟩
    refine ⟨hi, hk q hq, ?_⟩
    have hc : hx.choose = q.2 := h.functional j z hz _ hx.choose_spec q hq rfl
    simp only [p, hx, ↓reduceDIte]
    exact congrArg Passive.atom (Subtype.ext hc)
  · intro hm p hen
    refine (h.coefficient_iff three k j p).2 ?_
    intro z hz hpost
    obtain ⟨a, ha, haz⟩ := hm z hz fun q hq => (hpost q hq).2.1
    obtain ⟨hi, hr, hv⟩ := hpost _ haz
    exact hen a ha hv

/-- The prime guards are the minimal sets of postings meeting every loss. -/
theorem mem_normalForm_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (h : LossSystem f zeros) (k : Role) (j : Var) (g : Guard k j) :
    g ∈ normalForm three f k j ↔ Minimal (MeetsAll (zeros j)) g := by
  rw [mem_normalForm]
  have e : Sound (fun p : Pattern k j => k ∈ (f (probe three k j p)).val) =
      MeetsAll (zeros j) := funext fun g => propext (h.sound_iff three k j g)
  unfold Prime
  rw [e]

end LossSystem

/-- A minimal guard meeting a list of losses has at most one posting for
each loss. -/
theorem card_le_of_minimal_meetsAll {k : Role} {j : Var} (zs : List (List (Var × Role)))
    (g : Guard k j) (hg : Minimal (MeetsAll zs) g) : g.card ≤ zs.length := by
  classical
  let c : List (Var × Role) → Option (Literal k j) := fun z =>
    if h : Meets g z then some h.choose else none
  have hsub : (zs.filterMap c).toFinset ⊆ g := by
    intro a ha
    obtain ⟨z, -, hz⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 ha)
    by_cases h : Meets g z
    · have : some h.choose = some a := by simpa only [c, h, ↓reduceDIte] using hz
      rw [← Option.some.inj this]
      exact h.choose_spec.1
    · have : (none : Option (Literal k j)) = some a := by
        simpa only [c, h, ↓reduceDIte] using hz
      cases this
  have hall : MeetsAll zs (zs.filterMap c).toFinset := by
    intro z hz hk
    have h := hg.prop z hz hk
    refine ⟨h.choose, List.mem_toFinset.2 (List.mem_filterMap.2 ⟨z, hz, ?_⟩), h.choose_spec.2⟩
    simp only [c, h, ↓reduceDIte]
  calc g.card ≤ (zs.filterMap c).toFinset.card := Finset.card_le_card (hg.2 hall hsub)
    _ ≤ (zs.filterMap c).length := List.toFinset_card_le _
    _ ≤ zs.length := List.length_filterMap_le _ _

end KFOL.Core.Sources
