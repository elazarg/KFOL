module

public import KFOL.Core.SourceNormalForm

/-! # Duality for canonical source guards

Ordinary minimal transversals of a canonical list are automatically
consistent. A pairwise consensus test checks this directly on the guards.
-/

@[expose] public section
namespace KFOL.Core.Sources

open scoped Classical

universe u v
variable {Role : Type u} {Var : Type v} {k : Role} {j : Var}

/-- Each guard is hit by some posting. This does not require the postings
to be mutually consistent. -/
def HitsGuards (guards : Finset (Guard k j)) (z : Guard k j) : Prop :=
  ∀ g ∈ guards, ∃ a ∈ g, a ∈ z

/-- At most one atom is posted at each input. -/
def ConsistentPostings (z : Guard k j) : Prop :=
  ∀ ⦃a b⦄, a ∈ z → b ∈ z → a.1 = b.1 → a = b

/-- Coverage by one of the listed exclusion guards. -/
def SupportedGuard (guards : Finset (Guard k j)) (g : Guard k j) : Prop :=
  ∃ h ∈ guards, h ⊆ g

/-- Resolve exclusions of two different atoms at the same input. -/
def GuardConsensus (guards : Finset (Guard k j)) : Prop :=
  ∀ g ∈ guards, ∀ h ∈ guards, ∀ a ∈ g, ∀ b ∈ h,
    a.1 = b.1 → a ≠ b → SupportedGuard guards (g.erase a ∪ h.erase b)

private theorem not_hitsGuards_erase {guards : Finset (Guard k j)}
    {z : Guard k j} (min : Minimal (HitsGuards guards) z) {a} (ha : a ∈ z) :
    ¬ HitsGuards guards (z.erase a) := by
  intro hit
  exact Finset.notMem_erase a z (min.le_of_le hit (Finset.erase_subset _ _) ha)

private theorem private_guard {guards : Finset (Guard k j)} {z : Guard k j}
    (min : Minimal (HitsGuards guards) z) {a} (ha : a ∈ z) :
    ∃ g ∈ guards, a ∈ g ∧ ∀ c ∈ g, c ∉ z.erase a := by
  classical
  have miss := not_hitsGuards_erase min ha
  simp only [HitsGuards, not_forall, not_exists] at miss
  obtain ⟨g, hg, avoid⟩ := miss
  obtain ⟨c, hc, hz⟩ := min.prop g hg
  have eq : c = a := by
    by_contra ne
    exact avoid c ⟨hc, Finset.mem_erase.mpr ⟨ne, hz⟩⟩
  exact ⟨g, hg, eq ▸ hc, fun d hd hmem => avoid d ⟨hd, hmem⟩⟩

variable [Fintype Role] [Fintype Var]

theorem guardConsensus_iff_consistent_minimal_hits (guards : Finset (Guard k j)) :
    GuardConsensus guards ↔ ∀ z, Minimal (HitsGuards guards) z → ConsistentPostings z := by
  classical
  constructor
  · intro consensus z min a b ha hb same
    by_contra ne
    obtain ⟨g, hg, privateA, avoidA⟩ := private_guard min ha
    obtain ⟨h, hh, privateB, avoidB⟩ := private_guard min hb
    obtain ⟨f, hf, sub⟩ := consensus g hg h hh a privateA b privateB same ne
    obtain ⟨c, hc, hz⟩ := min.prop f hf
    rcases Finset.mem_union.mp (sub hc) with hm | hm
    · exact avoidA c (Finset.mem_of_mem_erase hm) (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hm, hz⟩)
    · exact avoidB c (Finset.mem_of_mem_erase hm) (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hm, hz⟩)
  · intro consistent g hg h hh a ha b hb same ne
    by_contra unsupported
    let c := g.erase a ∪ h.erase b
    let t := (Finset.univ : Guard k j) \ c
    have hits : HitsGuards guards t := by
      intro f hf
      obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp (fun sub => unsupported ⟨f, hf, sub⟩)
      exact ⟨x, hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩⟩
    obtain ⟨z, sub, min⟩ := exists_minimal_le_of_wellFoundedLT (HitsGuards guards) t hits
    obtain ⟨x, hx, hz⟩ := min.prop g hg
    obtain ⟨y, hy, hw⟩ := min.prop h hh
    have ex : x = a := by
      by_contra diff
      exact (Finset.mem_sdiff.mp (sub hz)).2 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨diff, hx⟩))
    have ey : y = b := by
      by_contra diff
      exact (Finset.mem_sdiff.mp (sub hw)).2 (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨diff, hy⟩))
    exact ne (consistent z min (ex ▸ hz) (ey ▸ hw) same)

/-- The set of all atomic postings in a passive pattern. -/
noncomputable def postings (p : Pattern k j) : Guard k j := by
  classical
  exact Finset.univ.filter fun a => p a.1 = .atom a.2

@[simp] theorem mem_postings {p : Pattern k j} {a : Literal k j} :
    a ∈ postings p ↔ p a.1 = .atom a.2 := by
  classical
  simp [postings]

theorem consistentPostings_postings (p : Pattern k j) : ConsistentPostings (postings p) := by
  rintro ⟨i, r⟩ ⟨l, s⟩ hr hs (he : i = l)
  subst l
  exact Prod.ext rfl (Passive.atom.inj ((mem_postings.mp hr).symm.trans (mem_postings.mp hs)))

theorem exists_postings_eq {z : Guard k j} (consistent : ConsistentPostings z) :
    ∃ p, postings p = z := by
  classical
  let p : Pattern k j := fun i =>
    if h : ∃ a ∈ z, a.1 = i then .atom h.choose.2 else .neutral
  refine ⟨p, Finset.Subset.antisymm ?_ ?_⟩
  · intro a ha
    have post := mem_postings.mp ha
    by_cases h : ∃ b ∈ z, b.1 = a.1
    · have atom : h.choose.2 = a.2 := by
        dsimp only [p] at post
        rw [dite_eq_left h] at post
        exact Passive.atom.inj post
      exact (Prod.ext h.choose_spec.2 atom : h.choose = a) ▸ h.choose_spec.1
    · dsimp only [p] at post
      rw [dite_eq_right h] at post
      cases post
  · intro a ha
    have h : ∃ b ∈ z, b.1 = a.1 := ⟨a, ha, rfl⟩
    have eq := consistent h.choose_spec.1 ha h.choose_spec.2
    exact mem_postings.mpr (by dsimp only [p]; rw [dite_eq_left h, eq])

private theorem hitsGuards_postings_iff (guards : Finset (Guard k j)) (p : Pattern k j) :
    HitsGuards guards (postings p) ↔ ¬ ∃ g ∈ guards, Enabled g p := by
  classical
  constructor
  · rintro hits ⟨g, hg, enabled⟩
    obtain ⟨a, ha, post⟩ := hits g hg
    exact enabled a ha (mem_postings.mp post)
  · intro loss g hg
    by_contra miss
    exact loss ⟨g, hg, fun a ha post => miss ⟨a, ha, mem_postings.mpr post⟩⟩

/-- A canonical list detects losses even in a set admitting multiple
candidate postings at each input. -/
theorem hitsGuards_iff_exists_loss (guards : Finset (Guard k j))
    (consensus : GuardConsensus guards) (z : Guard k j) :
    HitsGuards guards z ↔ ∃ p, postings p ⊆ z ∧ ¬ ∃ g ∈ guards, Enabled g p := by
  constructor
  · intro hits
    obtain ⟨t, sub, min⟩ := exists_minimal_le_of_wellFoundedLT (HitsGuards guards) z hits
    obtain ⟨p, rfl⟩ := exists_postings_eq ((guardConsensus_iff_consistent_minimal_hits guards).mp
      consensus t min)
    exact ⟨p, sub, (hitsGuards_postings_iff guards p).mp min.prop⟩
  · rintro ⟨p, sub, loss⟩ g hg
    obtain ⟨a, ha, hm⟩ := (hitsGuards_postings_iff guards p).mpr loss g hg
    exact ⟨a, ha, sub hm⟩

/-- Coverage by offered posting sets is an ordinary hypergraph implication. -/
theorem covers_losses_iff (guards offers : Finset (Guard k j))
    (consensus : GuardConsensus guards) :
    (∀ p, (¬ ∃ g ∈ guards, Enabled g p) → SupportedGuard offers (postings p)) ↔
      ∀ z, HitsGuards guards z → SupportedGuard offers z := by
  constructor
  · intro cover z hits
    obtain ⟨p, sub, loss⟩ := (hitsGuards_iff_exists_loss guards consensus z).mp hits
    obtain ⟨a, ha, hsub⟩ := cover p loss
    exact ⟨a, ha, hsub.trans sub⟩
  · intro cover p loss
    exact cover (postings p) ((hitsGuards_postings_iff guards p).mpr loss)

theorem sound_consensus (guards : Finset (Guard k j)) {g h : Guard k j}
    (hg : g ∈ guards) (hh : h ∈ guards) {a b : Literal k j}
    (same : a.1 = b.1) (ne : a ≠ b) :
    Sound (fun p => ∃ f ∈ guards, Enabled f p) (g.erase a ∪ h.erase b) := by
  classical
  intro p enabled
  by_cases posted : a ∈ postings p
  · refine ⟨h, hh, fun x hx mark => ?_⟩
    by_cases eq : x = b
    · subst x
      exact ne (consistentPostings_postings p posted (mem_postings.mpr mark) same)
    · exact enabled x (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨eq, hx⟩)) mark
  · refine ⟨g, hg, fun x hx mark => ?_⟩
    by_cases eq : x = a
    · exact posted (eq ▸ mem_postings.mpr mark)
    · exact enabled x (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hx⟩)) mark

/-- Check completeness by two listed guards and two competing postings. -/
theorem canonical_iff_guardConsensus (guards : Finset (Guard k j)) :
    (∀ g, g ∈ guards ↔ Prime (fun p => ∃ h ∈ guards, Enabled h p) g) ↔
      (∀ g ∈ guards, ∀ h ∈ guards, g ⊆ h → g = h) ∧ GuardConsensus guards := by
  classical
  constructor
  · intro canonical
    refine ⟨?_, fun g hg h hh a ha b hb same ne => ?_⟩
    · intro g hg h hh sub
      exact Finset.Subset.antisymm sub ((canonical h).mp hh |>.le_of_le ((canonical g).mp hg).prop sub)
    · obtain ⟨f, sub, prime⟩ := exists_minimal_le_of_wellFoundedLT _ _
        (sound_consensus guards hg hh same ne)
      exact ⟨f, (canonical f).mpr prime, sub⟩
  · rintro ⟨antichain, consensus⟩
    have supported {g : Guard k j} (sound : Sound (fun p => ∃ h ∈ guards, Enabled h p) g) :
        SupportedGuard guards g := by
      by_contra unsupported
      let z := (Finset.univ : Guard k j) \ g
      have hits : HitsGuards guards z := by
        intro h hh
        obtain ⟨a, ha, hnot⟩ := Finset.not_subset.mp (fun sub => unsupported ⟨h, hh, sub⟩)
        exact ⟨a, ha, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩⟩
      obtain ⟨p, sub, loss⟩ := (hitsGuards_iff_exists_loss guards consensus z).mp hits
      exact loss (sound p (fun a ha post => (Finset.mem_sdiff.mp (sub (mem_postings.mpr post))).2 ha))
    intro g
    constructor
    · intro hg
      refine ⟨fun p enabled => ⟨g, hg, enabled⟩, fun h sound sub => ?_⟩
      obtain ⟨f, hf, hs⟩ := supported sound
      exact (antichain f hf g hg (hs.trans sub)) ▸ hs
    · intro prime
      obtain ⟨h, hh, sub⟩ := supported prime.prop
      exact (Finset.Subset.antisymm sub (prime.le_of_le (fun _ enabled => ⟨h, hh, enabled⟩) sub)) ▸ hh

end KFOL.Core.Sources
