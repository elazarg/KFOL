module

public import KFOL.Owner.Basis.CommonRoot

/-! The generic word-witness and two-source absorption argument. -/

@[expose] public section

namespace KFOL.Owner.FiniteBasis.Laws

universe u

variable {M : Type u} {f : M → M → M} {h : M → M → M → M} (laws : FiniteBasis.Laws f h)

/-- Inserting P after one K action changes no composite. -/
theorem word_root_word (r k : M) (P : List (M × M)) (x : RootFiber f r) :
    laws.word r P (laws.action r r k (laws.word r P x)) = laws.word r P (laws.action r r k x) := by
  simpa only [word_cons, word_nil] using laws.word_band r P [(r, k)] x

/-- A covering witness word adds at most its one exceptional companion test.
The conclusion is uniform in the argument, rather than an elementwise choice. -/
theorem word_reduce_witness (r k : M) (P Q : List (M × M))
    (hfirst : ∀ p ∈ Q, p.1 = r ∨ ∃ c, (p.1, c) ∈ P)
    (hsecond : ∀ p ∈ Q, (p.2 = r ∨ (∃ c, (p.2, c) ∈ P) ∨ ∃ c, (c, p.2) ∈ P) ∨ p.2 = k) :
    (∀ x : RootFiber f r, laws.word r P (laws.word r Q x) = laws.word r P x) ∨
      (∀ x : RootFiber f r, laws.word r P (laws.word r Q x) = laws.word r P (laws.action r r k x)) := by
  induction Q with
  | nil => exact Or.inl (fun _ => rfl)
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    obtain hrest | hrest := ih (fun q hq => hfirst q (List.mem_cons_of_mem _ hq))
      (fun q hq => hsecond q (List.mem_cons_of_mem _ hq))
    · rcases hsecond (a, b) (List.mem_cons_self ..) with hb | hb
      · left
        intro x
        change laws.word r P (laws.action r a b (laws.word r rest x)) = _
        rw [laws.word_capture r a b P (hfirst _ (List.mem_cons_self ..)) hb, hrest]
      · right
        have hb : b = k := hb
        intro x
        change laws.word r P (laws.action r a b (laws.word r rest x)) = _
        rw [laws.word_weak r a b P (hfirst _ (List.mem_cons_self ..)), hb,
          ← laws.word_root_word r k P (laws.word r rest x), hrest, laws.word_root_word]
    · rcases hsecond (a, b) (List.mem_cons_self ..) with hb | hb
      · right
        intro x
        change laws.word r P (laws.action r a b (laws.word r rest x)) = _
        rw [laws.word_capture r a b P (hfirst _ (List.mem_cons_self ..)) hb, hrest]
      · right
        have hb : b = k := hb
        intro x
        change laws.word r P (laws.action r a b (laws.word r rest x)) = _
        rw [laws.word_weak r a b P (hfirst _ (List.mem_cons_self ..)), hb,
          ← laws.word_root_word r k P (laws.word r rest x), hrest, laws.word_root_word,
          laws.action_idem]

/-- A tested or self companion can be removed even after the exceptional K. -/
theorem word_exceptional_terminal (r j k t : M) (P : List (M × M))
    (ht : (t = r ∨ (∃ c, (t, c) ∈ P) ∨ ∃ c, (c, t) ∈ P) ∨ t = k ∨ t = j) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.word r P (laws.action r r k (laws.action r j t ⊥)) =
      laws.word r P (laws.action r r k (laws.constant r j)) := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  rcases ht with ht | ht | ht
  · rw [← laws.word_root_word r k P (laws.action r j t ⊥), laws.word_terminal r j t P (Or.inl ht),
      laws.word_root_word]
  · subst t
    rw [laws.action_terminal]
  · rw [← laws.word_root_word r k P (laws.action r j t ⊥), laws.word_terminal r j t P (Or.inr ht),
      laws.word_root_word]

/-- A single source witness supplies either its own projected constant or
both terminal sources together. -/
theorem source_absorption (r j k t : M) (P Q : List (M × M))
    (hfirst : ∀ p ∈ Q, p.1 = r ∨ ∃ c, (p.1, c) ∈ P)
    (hsecond : ∀ p ∈ Q, (p.2 = r ∨ (∃ c, (p.2, c) ∈ P) ∨ ∃ c, (c, p.2) ∈ P) ∨ p.2 = k)
    (ht : (t = r ∨ (∃ c, (t, c) ∈ P) ∨ ∃ c, (c, t) ∈ P) ∨ t = k ∨ t = j) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    ∀ W : RootFiber f r, laws.word r P ⊥ ≤ W → laws.word r Q (laws.action r j t ⊥) ≤ W →
      laws.word r P (laws.constant r j) ≤ W ∨ laws.word r P (laws.action r j k ⊥) ≤ W := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  intro W hzero hwitness
  have hpref : laws.word r P (laws.word r Q (laws.action r j t ⊥)) ≤ W :=
    (laws.word_contract r P _).trans (sup_le hzero hwitness)
  obtain hreduce | hreduce := laws.word_reduce_witness r k P Q hfirst hsecond
  · rw [hreduce] at hpref
    rcases ht with ht | ht | ht
    · left
      rw [laws.word_terminal r j t P (Or.inl ht)] at hpref
      exact hpref
    · right
      simpa only [ht] using hpref
    · left
      rw [laws.word_terminal r j t P (Or.inr ht)] at hpref
      exact hpref
  · right
    rw [hreduce, laws.word_exceptional_terminal r j k t P ht] at hpref
    exact (laws.word_mono r P (laws.action_zero_le_tested_constant r j k)).trans hpref

/-- Two-source absorption is derived from the thirty-six laws in an arbitrary
algebra. Each source is either old or has an explicit covering word witness. -/
theorem two_source_absorption (r a b : M) (P : List (M × M)) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    ∀ W : RootFiber f r, laws.word r P ⊥ ≤ W →
      (∀ j k, (j = a ∧ k = b) ∨ (j = b ∧ k = a) →
        (j = r ∨ (∃ c, (j, c) ∈ P) ∨ ∃ c, (c, j) ∈ P) ∨
          ∃ Q : List (M × M), ∃ t : M,
            (∀ p ∈ Q, p.1 = r ∨ ∃ c, (p.1, c) ∈ P) ∧
            (∀ p ∈ Q, (p.2 = r ∨ (∃ c, (p.2, c) ∈ P) ∨ ∃ c, (c, p.2) ∈ P) ∨ p.2 = k) ∧
            ((t = r ∨ (∃ c, (t, c) ∈ P) ∨ ∃ c, (c, t) ∈ P) ∨ t = k ∨ t = j) ∧
            laws.word r Q (laws.action r j t ⊥) ≤ W) →
      laws.word r P (laws.action r a b ⊥) ≤ W := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  intro W hzero hwitness
  have hsource (j k : M) (hjk : (j = a ∧ k = b) ∨ (j = b ∧ k = a)) :
      laws.word r P (laws.constant r j) ≤ W ∨ laws.word r P (laws.action r j k ⊥) ≤ W := by
    rcases hwitness j k hjk with hj | ⟨Q, t, hf, hs, ht, hQ⟩
    · left
      rw [laws.word_constant r j P hj]
      exact hzero
    · exact laws.source_absorption r j k t P Q hf hs ht W hzero hQ
  obtain ha | ha := hsource a b (Or.inl ⟨rfl, rfl⟩)
  · obtain hb | hb := hsource b a (Or.inr ⟨rfl, rfl⟩)
    · have hpair := laws.word_mono r P (laws.action_zero_le_constants r a b)
      rw [laws.word_sup] at hpair
      exact hpair.trans (sup_le ha hb)
    · have he : laws.action r b a ⊥ = laws.action r a b ⊥ := by
        apply Subtype.ext
        rw [laws.action_zero, laws.action_zero]
        exact laws.h_sym r b a
      simpa only [he] using hb
  · exact ha

end KFOL.Owner.FiniteBasis.Laws
