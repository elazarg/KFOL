module

public import KFOL.Algorithms.Words

/-! # Complete block framing and reusable exact list-codec proofs -/

@[expose] public section

namespace KFOL.Algorithms.Framing

open _root_.KFOL.Words

private theorem undelimitBlocksAux_sound (fuel : ℕ) (word : List Bool)
    (blocks : List (List Bool)) (h : undelimitBlocksAux fuel word = some blocks) :
    (blocks.map delimit).flatten = word := by
  induction fuel generalizing word blocks with
  | zero =>
    cases word with
    | nil => cases h; rfl
    | cons b word => simp [undelimitBlocksAux] at h
  | succ fuel ih =>
    cases word with
    | nil => cases h; rfl
    | cons b word =>
      simp only [undelimitBlocksAux] at h
      obtain ⟨⟨block, rest⟩, hp, ht⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, he⟩ := Option.bind_eq_some_iff.mp ht
      have he := Option.some.inj he
      subst blocks
      rw [List.map_cons, List.flatten_cons, ih rest tail htail]
      exact (eq_delimit_append_of_unpair?_eq_some hp).symm

/-- A successful complete parse consumes precisely the frames it returns.
This supplies the soundness direction missing from the library's round trip. -/
theorem undelimitBlocks_sound {word : List Bool} {blocks : List (List Bool)}
    (h : undelimitBlocks word = some blocks) : (blocks.map delimit).flatten = word :=
  undelimitBlocksAux_sound _ _ _ h

theorem length_frames (blocks : List (List Bool)) :
    (blocks.map delimit).flatten.length = 2 * (blocks.map List.length).sum + 2 * blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, delimit_length,
      List.sum_cons, List.length_cons, ih]
    omega

theorem mapM_decode_encode {α : Type*} (enc : α → List Bool) (dec : List Bool → Option α)
    (h : ∀ a, dec (enc a) = some a) (xs : List α) :
    (xs.map enc).mapM dec = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons, h, ih]

theorem map_eq_of_mapM_decode {α : Type*} (enc : α → List Bool) (dec : List Bool → Option α)
    (h : ∀ word a, dec word = some a → enc a = word)
    (blocks : List (List Bool)) (xs : List α) (hs : blocks.mapM dec = some xs) :
    xs.map enc = blocks := by
  induction blocks generalizing xs with
  | nil => cases hs; rfl
  | cons block blocks ih =>
    rw [List.mapM_cons] at hs
    obtain ⟨a, ha, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨tail, htail, he⟩ := Option.bind_eq_some_iff.mp hs
    have he := Option.some.inj he
    subst xs
    simp only [List.map_cons, h block a ha, ih tail htail]

end KFOL.Algorithms.Framing
