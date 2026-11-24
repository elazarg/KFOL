module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic

/-! # A phase of offers at a fixed owner

The other register entries are fixed. Adopting an offer therefore
sets the register to a value depending only on that offer. The exit
test can be any continuation monotone in the accumulated offers.
-/

@[expose] public section
namespace KFOL.Core.OfferPhase

variable {Offer Register : Type*} [DecidableEq Offer]

/-- Winning trees inside one phase, with either response to each offer. -/
inductive Wins (allowed : Finset Offer) (adopt : Offer → Register)
    (exit : Finset Offer → Register → Prop) : Finset Offer → Register → Prop where
  | stop {seen r} : exit seen r → Wins allowed adopt exit seen r
  | offer {seen r e} : e ∈ allowed →
      Wins allowed adopt exit (insert e seen) r →
      Wins allowed adopt exit (insert e seen) (adopt e) →
      Wins allowed adopt exit seen r

/-- After the batch, every possible last adoption passes the exit test. -/
def Supports (adopt : Offer → Register) (exit : Finset Offer → Register → Prop)
    (seen batch : Finset Offer) : Prop :=
  ∀ e ∈ batch, exit (seen ∪ batch) (adopt e)

variable {allowed : Finset Offer} {adopt : Offer → Register}
variable {exit : Finset Offer → Register → Prop}

/-- An adaptive one-owner phase can be played in a fixed order, regardless
of the responses, even when the exit test is another game. -/
theorem wins_iff_batch
    (mono : ∀ {s t : Finset Offer}, s ⊆ t → ∀ r, exit s r → exit t r)
    (seen : Finset Offer) (r : Register) :
    Wins allowed adopt exit seen r ↔
      ∃ batch ⊆ allowed, exit (seen ∪ batch) r ∧ Supports adopt exit seen batch := by
  constructor
  · intro h
    induction h with
    | stop done => exact ⟨∅, Finset.empty_subset _, by simpa using done, by simp [Supports]⟩
    | @offer seen r e he _ _ hl hr =>
      obtain ⟨l, hla, hld, hls⟩ := hl
      obtain ⟨u, hua, hud, hus⟩ := hr
      let batch := insert e (l ∪ u)
      have left : insert e seen ∪ l ⊆ seen ∪ batch := by
        intro v hv
        simp only [Finset.mem_union, Finset.mem_insert] at hv
        rcases hv with (rfl | h) | h <;> simp_all [batch]
      have right : insert e seen ∪ u ⊆ seen ∪ batch := by
        intro v hv
        simp only [Finset.mem_union, Finset.mem_insert] at hv
        rcases hv with (rfl | h) | h <;> simp_all [batch]
      refine ⟨batch, Finset.insert_subset he (Finset.union_subset hla hua), mono left r hld, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact mono right _ hud
      · rcases Finset.mem_union.mp h with h | h
        · exact mono left _ (hls _ h)
        · exact mono right _ (hus _ h)
  · rintro ⟨batch, ha, h, hs⟩
    induction batch using Finset.induction_on generalizing seen r with
    | empty => exact Wins.stop (by simpa using h)
    | @insert e tail _ ih =>
      have same : insert e seen ∪ tail = seen ∪ insert e tail := by
        ext v
        simp
      have ht : tail ⊆ allowed := Finset.Subset.trans (Finset.subset_insert _ _) ha
      have supp : Supports adopt exit (insert e seen) tail := by
        intro v hv
        rw [same]
        exact hs v (Finset.mem_insert_of_mem hv)
      refine Wins.offer (ha (Finset.mem_insert_self _ _)) ?_ ?_
      · exact ih (insert e seen) r ht (same.symm ▸ h) supp
      · exact ih (insert e seen) (adopt e) ht
          (same.symm ▸ hs e (Finset.mem_insert_self _ _)) supp

/-- One elimination pass removes all offers whose adopted register fails
even after every currently retained offer. -/
def prune (adopt : Offer → Register) (exit : Finset Offer → Register → Prop)
    [∀ s r, Decidable (exit s r)] (seen batch : Finset Offer) : Finset Offer :=
  batch.filter fun e => exit (seen ∪ batch) (adopt e)

/-- Compute the greatest self-supporting batch. The fuel counts sweeps. -/
def greatestBatch (adopt : Offer → Register) (exit : Finset Offer → Register → Prop)
    [∀ s r, Decidable (exit s r)] (seen : Finset Offer) :
    ℕ → Finset Offer → Finset Offer
  | 0, batch => batch
  | fuel + 1, batch => greatestBatch adopt exit seen fuel (prune adopt exit seen batch)

variable [∀ s r, Decidable (exit s r)]

private theorem prune_eq_self (seen batch : Finset Offer) :
    prune adopt exit seen batch = batch ↔ Supports adopt exit seen batch := by
  simp [prune, Supports, Finset.filter_eq_self]

private theorem greatestBatch_fixed (seen batch : Finset Offer)
    (h : Supports adopt exit seen batch) (k : ℕ) :
    greatestBatch adopt exit seen k batch = batch := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [greatestBatch, (prune_eq_self seen batch).mpr h] using ih

private theorem greatestBatch_subset (seen batch : Finset Offer) (k : ℕ) :
    greatestBatch adopt exit seen k batch ⊆ batch := by
  induction k generalizing batch with
  | zero => rfl
  | succ k ih => exact (ih _).trans (Finset.filter_subset _ _)

private theorem greatestBatch_supports (seen batch : Finset Offer) (k : ℕ)
    (bound : batch.card ≤ k) :
    Supports adopt exit seen (greatestBatch adopt exit seen k batch) := by
  induction k generalizing batch with
  | zero =>
    have h : batch = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero bound)
    simp [greatestBatch, h, Supports]
  | succ k ih =>
    by_cases h : prune adopt exit seen batch = batch
    · have hs := (prune_eq_self seen batch).mp h
      rw [greatestBatch_fixed seen batch hs (k + 1)]
      exact hs
    · apply ih
      have ss : prune adopt exit seen batch ⊂ batch :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, h⟩
      have := Finset.card_lt_card ss
      omega

private theorem subset_greatestBatch
    (mono : ∀ {s t : Finset Offer}, s ⊆ t → ∀ r, exit s r → exit t r)
    (seen batch : Finset Offer) (hs : Supports adopt exit seen batch)
    (k : ℕ) (candidate : Finset Offer) (inc : batch ⊆ candidate) :
    batch ⊆ greatestBatch adopt exit seen k candidate := by
  induction k generalizing candidate with
  | zero => exact inc
  | succ _ ih =>
    apply ih
    intro e he
    exact Finset.mem_filter.mpr ⟨inc he, mono (Finset.union_subset_union_right inc) _ (hs e he)⟩

/-- At most one elimination sweep per available offer suffices for a phase.
Only the exit test for the inherited register remains after the sweeps. -/
theorem wins_iff_greatestBatch
    (mono : ∀ {s t : Finset Offer}, s ⊆ t → ∀ r, exit s r → exit t r)
    (seen : Finset Offer) (r : Register) :
    Wins allowed adopt exit seen r ↔
      exit (seen ∪ greatestBatch adopt exit seen allowed.card allowed) r := by
  rw [wins_iff_batch mono]
  constructor
  · rintro ⟨b, ha, h, hs⟩
    exact mono (Finset.union_subset_union_right
      (subset_greatestBatch mono seen b hs _ allowed ha)) _ h
  · intro h
    exact ⟨_, greatestBatch_subset seen allowed _, h, greatestBatch_supports seen allowed _ le_rfl⟩

end KFOL.Core.OfferPhase
