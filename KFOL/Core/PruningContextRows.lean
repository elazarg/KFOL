module

public import KFOL.Core.PruningContexts

/-! # Completion sets from one-headed implications -/

@[expose] public section
namespace KFOL.Core.PruningContexts

open CompulsoryPruning ProfileBudgets
variable {V : Type*} [DecidableEq V]

inductive RowStatus where
  | hit
  | unmarked
  | marked
  deriving DecidableEq

/-- A tail hits every support, misses only unmarked supports, or misses
at least one support containing the head. -/
noncomputable def rowStatus (head : V) (tail : Finset V) (family : Set (Finset V)) : RowStatus := by
  classical
  exact if ∃ H ∈ family, head ∈ H ∧ Disjoint H tail then .marked
    else if ∃ H ∈ family, Disjoint H tail then .unmarked else .hit

def legalRows (head : V) (tails : Set (Finset V)) : Set (Finset V) :=
  {H | ∀ tail ∈ tails, head ∈ H → ¬ Disjoint H tail}

theorem completion_rows_iff (head : V) (tails family : Set (Finset V)) (extra : Finset V) :
    extra ∈ completions (legalRows head tails) family ↔ ∀ tail ∈ tails,
      ¬ Disjoint extra tail ∨ rowStatus head tail family = .hit ∨
        (rowStatus head tail family = .unmarked ∧ head ∉ extra) := by
  classical
  constructor
  · intro h tail ht
    by_cases d : Disjoint extra tail
    · right
      have unmarked : ¬ ∃ H ∈ family, head ∈ H ∧ Disjoint H tail := by
        rintro ⟨H, hH, hh, hd⟩
        exact h H hH tail ht (Finset.mem_union_left _ hh) (Finset.disjoint_union_left.mpr ⟨hd,d⟩)
      by_cases miss : ∃ H ∈ family, Disjoint H tail
      · right
        refine ⟨by simp [rowStatus, unmarked, miss], ?_⟩
        intro hx
        obtain ⟨H,hH,hd⟩ := miss
        exact h H hH tail ht (Finset.mem_union_right _ hx) (Finset.disjoint_union_left.mpr ⟨hd,d⟩)
      · exact Or.inl (by simp [rowStatus, unmarked, miss])
    · exact Or.inl d
  · intro h H hH tail ht hx all
    obtain ⟨hd, ed⟩ := Finset.disjoint_union_left.mp all
    have marked : ¬ ∃ J ∈ family, head ∈ J ∧ Disjoint J tail := by
      intro bad
      simpa [rowStatus, bad, ed] using h tail ht
    have exactStatus : rowStatus head tail family = .unmarked := by
      simp [rowStatus, marked, show ∃ J ∈ family, Disjoint J tail from ⟨H, hH, hd⟩]
    have notExtra : head ∉ extra := by simpa [ed, exactStatus] using h tail ht
    exact marked ⟨H, hH, (Finset.mem_union.mp hx).resolve_right notExtra, hd⟩

private theorem complement_hits {tails : Set (Finset V)} {ambient A B : Finset V}
    (anti : IsAntichain (· ⊆ ·) tails) (ha : A ∈ tails) (hb : B ∈ tails) (ne : A ≠ B)
    (inside : B ⊆ ambient) : ¬ Disjoint (ambient \ A) B := by
  intro dj
  have sub : B ⊆ A := by
    intro x hx
    by_contra nx
    exact (Finset.disjoint_left.mp dj) (Finset.mem_sdiff.mpr ⟨inside hx,nx⟩) hx
  exact anti hb ha ne.symm sub

private theorem complement_disjoint (ambient tail : Finset V) : Disjoint (ambient \ tail) tail :=
  Finset.disjoint_left.mpr (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 h₂)

/-- An antichain of tails at a single head has no redundancy between the
three completion conditions contributed by the different tails. -/
theorem completions_eq_iff_rowStatus (head : V) (ambient : Finset V)
    (outside : head ∉ ambient) (tails A B : Set (Finset V))
    (anti : IsAntichain (· ⊆ ·) tails) (inside : ∀ tail ∈ tails, tail ⊆ ambient) :
    completions (legalRows head tails) A = completions (legalRows head tails) B ↔
      ∀ tail ∈ tails, rowStatus head tail A = rowStatus head tail B := by
  classical
  constructor
  · intro eq tail ht
    let extra := ambient \ tail
    have hd : Disjoint extra tail := complement_disjoint _ _
    have notHead : head ∉ extra := fun h => outside (Finset.mem_sdiff.mp h).1
    have insertedDisjoint : Disjoint (insert head extra) tail := by
      rw [Finset.disjoint_insert_left]
      exact ⟨fun h => outside (inside _ ht h), hd⟩
    have onlyRow (F : Set (Finset V)) (U : Finset V) (sub : extra ⊆ U)
        (dj : Disjoint U tail) :
        U ∈ completions (legalRows head tails) F ↔ rowStatus head tail F = .hit ∨
          (rowStatus head tail F = .unmarked ∧ head ∉ U) := by
      rw [completion_rows_iff]
      refine ⟨fun h => (h tail ht).resolve_left (not_not_intro dj), ?_⟩
      intro row T hT
      by_cases e : tail = T
      · subst T
        exact Or.inr row
      · exact Or.inl (fun d => complement_hits anti ht hT e (inside T hT) (d.mono_left sub))
    have sameHit : rowStatus head tail A = .hit ↔ rowStatus head tail B = .hit := by
      have h := Set.ext_iff.mp eq (insert head extra)
      rw [onlyRow _ _ (Finset.subset_insert _ _) insertedDisjoint,
        onlyRow _ _ (Finset.subset_insert _ _) insertedDisjoint] at h
      simpa using h
    have sameClear : (rowStatus head tail A = .hit ∨ rowStatus head tail A = .unmarked) ↔
        (rowStatus head tail B = .hit ∨ rowStatus head tail B = .unmarked) := by
      have h := Set.ext_iff.mp eq extra
      rw [onlyRow _ _ Finset.Subset.rfl hd, onlyRow _ _ Finset.Subset.rfl hd] at h
      simpa [notHead] using h
    cases ea : rowStatus head tail A <;> cases eb : rowStatus head tail B <;>
      simp_all
  · intro eq
    ext extra
    rw [completion_rows_iff, completion_rows_iff]
    exact forall₂_congr fun tail ht => by rw [eq tail ht]

private theorem exists_word_with_supports {Role : Type*} [DecidableEq Role]
    {r q : Role} (different : q ≠ r) (family : Finset (Finset V)) (active : family.Nonempty)
    (nonempty : ∀ S ∈ family, S.Nonempty) :
    ∃ t : CoreTerm Role V, Supports r t = (family : Set (Finset V)) := by
  induction family using Finset.induction_on with
  | empty => simp at active
  | insert S family _ ih =>
    obtain ⟨base, hb⟩ := exists_single_support r S (nonempty S (Finset.mem_insert_self ..))
    by_cases hn : family.Nonempty
    · obtain ⟨rest, hr⟩ := ih hn
        (fun T ht => nonempty T (Finset.mem_insert_of_mem ht))
      refine ⟨choiceTerm q base rest, ?_⟩
      ext H
      rw [foreign different, hb, hr]
      simp [eq_comm]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      exact ⟨base, by simpa using hb⟩

/-- At a single head with incomparable nonempty proper tails, every assignment
of the three statuses is realized by an actual owned-choice word. -/
theorem exists_word_with_rowStatus {Role : Type*} [DecidableEq Role]
    {r q : Role} (different : q ≠ r) (head : V) (ambient : Finset V)
    (available : ambient.Nonempty) (outside : head ∉ ambient)
    (tails : Finset (Finset V)) (anti : IsAntichain (· ⊆ ·) (tails : Set (Finset V)))
    (proper : ∀ tail ∈ tails, tail.Nonempty ∧ tail ⊂ ambient)
    (desired : Finset V → RowStatus) :
    ∃ t : CoreTerm Role V, ∀ tail ∈ tails, rowStatus head tail (Supports r t) = desired tail := by
  classical
  let support (tail : Finset V) : Finset V :=
    match desired tail with
    | .hit => ambient
    | .unmarked => ambient \ tail
    | .marked => insert head (ambient \ tail)
  let family := insert ambient (tails.image support)
  have whole {tail : Finset V} (ht : tail ∈ tails) : ¬ Disjoint ambient tail := by
    obtain ⟨x, hx⟩ := (proper tail ht).1
    exact fun d => Finset.disjoint_left.mp d ((proper tail ht).2.le hx) hx
  have familyNonempty : ∀ S ∈ family, Finset.Nonempty S := by
    intro S hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact available
    · obtain ⟨tail, ht, rfl⟩ := Finset.mem_image.mp hs
      have diff : (ambient \ tail).Nonempty :=
        Finset.sdiff_nonempty.mpr (not_le_of_gt (proper tail ht).2)
      cases hd : desired tail
      · simpa [support, hd] using available
      · simpa [support, hd] using diff
      · simp [support, hd]
  obtain ⟨t, eq⟩ := exists_word_with_supports different family
    ⟨ambient, Finset.mem_insert_self ..⟩ familyNonempty
  refine ⟨t, fun tail ht => ?_⟩
  rw [eq]
  have source : support tail ∈ family :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨tail, ht, rfl⟩)
  have only {S : Finset V} (hs : S ∈ family) (hd : Disjoint S tail) : S = support tail := by
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact (whole ht hd).elim
    obtain ⟨row, hr, rfl⟩ := Finset.mem_image.mp hs
    by_contra! ne
    have incompatible : ¬ Disjoint (ambient \ row) tail :=
      complement_hits anti hr ht (fun e => ne (congrArg support e)) (proper tail ht).2.le
    apply incompatible
    apply hd.mono_left
    cases e : desired row
    · simp [support, e]
    · simp [support, e]
    · simp [support, e]
  have headAbsent : head ∉ ambient \ tail := fun h => outside (Finset.mem_sdiff.mp h).1
  have chosenDisjoint : Disjoint (ambient \ tail) tail := complement_disjoint _ _
  cases hd : desired tail with
  | hit =>
    have none : ¬ ∃ S ∈ (family : Set (Finset V)), Disjoint S tail := by
      rintro ⟨S, hm, dj⟩
      exact whole ht (by simpa [only hm dj, support, hd] using dj)
    have noneMarked : ¬ ∃ S ∈ (family : Set (Finset V)), head ∈ S ∧ Disjoint S tail :=
      fun ⟨S, hm, hh⟩ => none ⟨S, hm, hh.2⟩
    simp only [rowStatus, ite_eq_right noneMarked, ite_eq_right none]
  | unmarked =>
    have unmarked : ¬ ∃ S ∈ (family : Set (Finset V)), head ∈ S ∧ Disjoint S tail := by
      rintro ⟨S, hm, hx, dj⟩
      exact headAbsent (by simpa [only hm dj, support, hd] using hx)
    have miss : ∃ S ∈ (family : Set (Finset V)), Disjoint S tail :=
      ⟨support tail, source, by simpa [support, hd] using chosenDisjoint⟩
    simp only [rowStatus, ite_eq_right unmarked, ite_eq_left miss]
  | marked =>
    have marked : ∃ S ∈ (family : Set (Finset V)), head ∈ S ∧ Disjoint S tail := by
      refine ⟨support tail, source, by simp [support, hd], ?_⟩
      simp [support, hd, Finset.disjoint_insert_left, chosenDisjoint,
        show head ∉ tail from fun h => outside ((proper tail ht).2.le h)]
    simp only [rowStatus, ite_eq_left marked]

end KFOL.Core.PruningContexts
