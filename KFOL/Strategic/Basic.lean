module

public import KFOL.Definitions.Strategic
public import KFOL.Algebra.Basic

/-! # Public backward induction and the canonical strategic-form bridge -/

@[expose] public section

namespace KFOL.Strategic

universe u

private theorem exists_outside {α : Type u} (r : α) (A : Set α) (hne : A.Nonempty)
    (ha : A ≠ {r}) : ∃ i, A i ∧ i ≠ r := by
  classical
  by_contra h
  push Not at h
  apply ha
  funext i
  apply propext
  constructor
  · intro hi
    exact h i hi
  · intro hi
    obtain ⟨j,hj⟩ := hne
    have hjr := h j hj
    subst j
    exact hi.symm ▸ hj
theorem change_refl {α : Type u} {g : Tree α} (i : α) (p : Profile g) :
    Deviation i p p := by
  induction p with
  | leaf w => exact Deviation.leaf w
  | node r action left right ihl ihr =>
    exact Deviation.node (fun _ => rfl) ihl ihr

@[simp] theorem spe_leaf {α : Type u} (w : α) : IsSubgamePerfect (.leaf w) := by
  intro h q hq
  cases hq
  intro i q _ hw
  cases q
  exact hw

theorem spe_node_subgames {α : Type u} {left right : Tree α} (r : α) (a : Bool)
    (p : Profile left) (q : Profile right) :
    IsSubgamePerfect (.node r a p q) ↔ IsNash (.node r a p q) ∧ IsSubgamePerfect p ∧ IsSubgamePerfect q := by
  constructor
  · intro h
    exact ⟨h _ (.refl _), fun s hs => h s (.left hs), fun s hs => h s (.right hs)⟩
  · rintro ⟨hn, hp, hq⟩ h s hs
    cases hs with
    | refl => exact hn
    | left h => exact hp _ h
    | right h => exact hq _ h

theorem spe_nash {α : Type u} {g : Tree α} {p : Profile g} (hp : IsSubgamePerfect p) :
    IsNash p := hp p (.refl p)

def LocallyOptimal {α : Type u} {left right : Tree α} (r : α) (a : Bool)
    (p : Profile left) (q : Profile right) : Prop :=
  (winner p = r ∨ winner q = r) → winner (.node r a p q) = r

theorem spe_node_iff {α : Type u} {left right : Tree α} (r : α) (a : Bool)
    (p : Profile left) (q : Profile right) :
    IsSubgamePerfect (.node r a p q) ↔ IsSubgamePerfect p ∧ IsSubgamePerfect q ∧ LocallyOptimal r a p q := by
  classical
  constructor
  · intro hs
    rcases (spe_node_subgames r a p q).mp hs with ⟨hn, hp, hq⟩
    refine ⟨hp, hq, ?_⟩
    intro h
    rcases h with h | h
    · apply hn r (.node r false p q)
      · exact Deviation.node (fun hne => False.elim (hne rfl))
          (change_refl r p) (change_refl r q)
      · exact h
    · apply hn r (.node r true p q)
      · exact Deviation.node (fun hne => False.elim (hne rfl))
          (change_refl r p) (change_refl r q)
      · exact h
  · rintro ⟨hp, hq, hl⟩
    apply (spe_node_subgames r a p q).mpr
    refine ⟨?_, hp, hq⟩
    intro i deviation hc hw
    cases deviation with
    | node _ b p' q' =>
      cases hc with
      | node hroot hleft hright =>
        by_cases he : r = i
        · cases he
          cases b with
          | false =>
            have h : winner p = r := spe_nash hp r p' hleft hw
            exact hl (Or.inl h)
          | true =>
            have h : winner q = r := spe_nash hq r q' hright hw
            exact hl (Or.inr h)
        · have hab : a = b := hroot he
          subst b
          cases a with
          | false => exact spe_nash hp i p' hleft hw
          | true => exact spe_nash hq i q' hright hw

theorem exists_spe {α : Type u} (g : Tree α) : ∃ p : Profile g, IsSubgamePerfect p := by
  classical
  induction g with
  | leaf w => exact ⟨.leaf w, spe_leaf _⟩
  | node r left right ihl ihr =>
    rcases ihl with ⟨p, hp⟩
    rcases ihr with ⟨q, hq⟩
    by_cases h : winner p = r
    · refine ⟨.node r false p q, (spe_node_iff r false p q).mpr ⟨hp, hq, ?_⟩⟩
      intro _
      exact h
    · refine ⟨.node r true p q, (spe_node_iff r true p q).mpr ⟨hp, hq, ?_⟩⟩
      rintro (h' | h')
      · exact False.elim (h h')
      · exact h'

theorem possibleWinners_ne {α : Type u} (g : Tree α) : (possibleWinners g).Nonempty := by
  rcases exists_spe g with ⟨p, hp⟩
  exact ⟨winner p, p, hp, rfl⟩

theorem possibleWinners_leaf {α : Type u} (r : α) : possibleWinners (.leaf r) = {r} := by
  funext i
  apply propext
  constructor
  · rintro ⟨p, _, h⟩
    cases p
    exact h.symm
  · intro h
    exact ⟨.leaf r, spe_leaf _, h.symm⟩

theorem winner_of_singleton {α : Type u} {g : Tree α} (r : α)
    (he : possibleWinners g = {r}) (p : Profile g) (hp : IsSubgamePerfect p) : winner p = r := by
  have hm : possibleWinners g (winner p) := ⟨p, hp, rfl⟩
  rw [he] at hm
  exact hm

theorem exists_spe_losing {α : Type u} (g : Tree α) (r : α)
    (he : possibleWinners g ≠ {r}) : ∃ p : Profile g, IsSubgamePerfect p ∧ winner p ≠ r := by
  rcases exists_outside r (possibleWinners g) (possibleWinners_ne g) he with ⟨i, hi, hir⟩
  rcases hi with ⟨p, hp, hw⟩
  exact ⟨p, hp, fun h => hir (hw.symm.trans h)⟩

theorem possibleWinners_node {α : Type u} (r : α) (left right : Tree α) :
    possibleWinners (.node r left right) = (if possibleWinners left = {r} ∨ possibleWinners right = {r} then {r}
      else possibleWinners left ∪ possibleWinners right) := by
  classical
  by_cases h : possibleWinners left = {r} ∨ possibleWinners right = {r}
  · rw [show (if possibleWinners left = {r} ∨ possibleWinners right = {r} then {r}
      else possibleWinners left ∪ possibleWinners right) = {r} from by simp [h]]
    funext i
    apply propext
    constructor
    · rintro ⟨profile, hp, hw⟩
      cases profile with
      | node _ action p q =>
        rcases (spe_node_iff r action p q).mp hp with ⟨hl, hr, ho⟩
        have hwin : winner (.node r action p q) = r := by
          rcases h with h | h
          · exact ho (Or.inl (winner_of_singleton r h p hl))
          · exact ho (Or.inr (winner_of_singleton r h q hr))
        exact hw.symm.trans hwin
    · intro hir
      change i = r at hir
      subst i
      rcases exists_spe left with ⟨p, hp⟩
      rcases exists_spe right with ⟨q, hq⟩
      rcases h with h | h
      · have hw := winner_of_singleton r h p hp
        refine ⟨.node r false p q, ?_, hw⟩
        exact (spe_node_iff r false p q).mpr ⟨hp, hq, fun _ => hw⟩
      · have hw := winner_of_singleton r h q hq
        refine ⟨.node r true p q, ?_, hw⟩
        exact (spe_node_iff r true p q).mpr ⟨hp, hq, fun _ => hw⟩
  · rw [show (if possibleWinners left = {r} ∨ possibleWinners right = {r} then {r}
      else possibleWinners left ∪ possibleWinners right) =
        (possibleWinners left ∪ possibleWinners right) from by simp [h]]
    have hl : possibleWinners left ≠ {r} := fun e => h (Or.inl e)
    have hr : possibleWinners right ≠ {r} := fun e => h (Or.inr e)
    funext i
    apply propext
    constructor
    · rintro ⟨profile, hp, hw⟩
      cases profile with
      | node _ action p q =>
        rcases (spe_node_iff r action p q).mp hp with ⟨hP, hQ, _⟩
        cases action with
        | false => exact Or.inl ⟨p, hP, hw⟩
        | true => exact Or.inr ⟨q, hQ, hw⟩
    · rintro (hi | hi)
      · rcases hi with ⟨p, hp, hw⟩
        rcases exists_spe_losing right r hr with ⟨q, hq, hlose⟩
        refine ⟨.node r false p q, ?_, hw⟩
        apply (spe_node_iff r false p q).mpr
        refine ⟨hp, hq, ?_⟩
        rintro (hwin | hwin)
        · exact hwin
        · exact False.elim (hlose hwin)
      · rcases hi with ⟨q, hq, hw⟩
        rcases exists_spe_losing left r hl with ⟨p, hp, hlose⟩
        refine ⟨.node r true p q, ?_, hw⟩
        apply (spe_node_iff r true p q).mpr
        refine ⟨hp, hq, ?_⟩
        rintro (hwin | hwin)
        · exact False.elim (hlose hwin)
        · exact hwin

@[simp] theorem assemble_constant {α : Type u} {g : Tree α} (p : Profile g) :
    assemble g (fun _ => p) = p := by
  induction p with
  | leaf w => rfl
  | node r a p q hp hq => simp only [assemble, Profile.action, Profile.left, Profile.right, hp, hq]

@[simp] theorem winningPreference_pure {α : Type u} [DecidableEq α] (i a b : α) :
    winningPreference α i (PMF.pure a) (PMF.pure b) ↔ (b = i → a = i) := by
  simp only [winningPreference, PMF.pure_apply]
  by_cases hb : i = b <;> by_cases ha : i = a <;> simp_all <;> grind

private theorem assemble_update_change {α : Type u} [DecidableEq α]
    (g : Tree α) (plans : α → Profile g) (i : α) (replacement : Profile g) :
    Deviation i (assemble g plans)
      (assemble g (GameTheory.Profile.update (sig := (gameForm g).sig) plans i replacement)) := by
  induction g with
  | leaf w => exact .leaf w
  | node r l h hl hh =>
    cases replacement with
    | node _ a p q =>
      have hl' := hl (fun j => (plans j).left) p
      have hh' := hh (fun j => (plans j).right) q
      have el : (fun j => (GameTheory.Profile.update (sig := (gameForm (.node r l h)).sig)
          plans i (.node r a p q) j).left) =
          GameTheory.Profile.update (sig := (gameForm l).sig) (fun j => (plans j).left) i p := by
        funext j
        by_cases hj : j = i
        · subst j; simp [GameTheory.Profile.update, Profile.left]
        · simp [GameTheory.Profile.update, Function.update, hj, Profile.left]
      have er : (fun j => (GameTheory.Profile.update (sig := (gameForm (.node r l h)).sig)
          plans i (.node r a p q) j).right) =
          GameTheory.Profile.update (sig := (gameForm h).sig) (fun j => (plans j).right) i q := by
        funext j
        by_cases hj : j = i
        · subst j; simp [GameTheory.Profile.update, Profile.right]
        · simp [GameTheory.Profile.update, Function.update, hj, Profile.right]
      simp only [assemble, el, er]
      apply Deviation.node ?_ hl' hh'
      intro hr
      rw [GameTheory.Profile.update_of_ne _ _ hr]

private theorem assemble_update_of_change {α : Type u} [DecidableEq α]
    {g : Tree α} {p q : Profile g} (i : α) (hchange : Deviation i p q) :
    assemble g (GameTheory.Profile.update (sig := (gameForm g).sig) (fun _ => p) i q) = q := by
  induction hchange with
  | leaf w => rfl
  | @node l h r a b p p' q q' hr hl hh il ih =>
    have el : (fun j => (GameTheory.Profile.update (sig := (gameForm (.node r l h)).sig)
        (fun _ => Profile.node r a p q) i (.node r b p' q') j).left) =
        GameTheory.Profile.update (sig := (gameForm l).sig) (fun _ => p) i p' := by
      funext j
      by_cases hj : j = i
      · subst j; simp [GameTheory.Profile.update, Profile.left]
      · simp [GameTheory.Profile.update, Function.update, hj, Profile.left]
    have er : (fun j => (GameTheory.Profile.update (sig := (gameForm (.node r l h)).sig)
        (fun _ => Profile.node r a p q) i (.node r b p' q') j).right) =
        GameTheory.Profile.update (sig := (gameForm h).sig) (fun _ => q) i q' := by
      funext j
      by_cases hj : j = i
      · subst j; simp [GameTheory.Profile.update, Profile.right]
      · simp [GameTheory.Profile.update, Function.update, hj, Profile.right]
    simp only [assemble, el, er, il, ih]
    congr 1
    by_cases he : r = i
    · subst r
      rw [GameTheory.Profile.update_same]
      rfl
    · rw [GameTheory.Profile.update_of_ne _ _ he]
      exact hr he

/-- Whole-player deviations are exactly unilateral replacements in the
canonical GameTheory strategic form, after irrelevant entries are erased. -/
theorem nash_iff_gameTheory {α : Type u} [DecidableEq α] {g : Tree α} (p : Profile g) :
    IsNash p ↔ GameTheory.IsNash (gameForm g) (winningPreference α) (fun _ => p) := by
  rw [GameTheory.isNash_iff]
  change IsNash p ↔ ∀ i q, winningPreference α i
    (PMF.pure (winner (assemble g (fun _ => p))))
    (PMF.pure (winner (assemble g (GameTheory.Profile.update (sig := (gameForm g).sig)
      (fun _ => p) i q))))
  simp only [assemble_constant, winningPreference_pure]
  constructor
  · intro h i q hq
    exact h i _ (by simpa only [assemble_constant] using assemble_update_change g (fun _ => p) i q) hq
  · intro h i q hc hq
    have hd := h i q
    rw [assemble_update_of_change i hc] at hd
    exact hd hq

/-- Subgame perfection compares all unilateral plans in every subtree,
using the canonical IsNash predicate, including subtrees never reached. -/
theorem spe_iff_gameTheory {α : Type u} [DecidableEq α] {g : Tree α} (p : Profile g) :
    IsSubgamePerfect p ↔ ∀ {h : Tree α} (q : Profile h), Restriction p q →
      GameTheory.IsNash (gameForm h) (winningPreference α) (fun _ => q) := by
  constructor
  · intro hp h q hq
    exact (nash_iff_gameTheory q).mp (hp q hq)
  · intro hp h q hq
    exact (nash_iff_gameTheory q).mpr (hp q hq)


end KFOL.Strategic
