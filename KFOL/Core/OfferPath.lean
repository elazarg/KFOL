module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Insert

/-! # Adopted offers on the two-owner path

Inputs are path edges indexed from zero; the offer at vertex j posts
its incident edges at owner j modulo two. Full blocks of one owner
are disjoint. Rows with the same posted vertex are removed together.
-/

@[expose] public section
namespace KFOL.Core.OfferPath

/-- Edge v is incident to vertex j. -/
def Incident (v j : ℕ) : Prop := j = v ∨ j = v + 1

/-- Register values are vertex indices; the argument is the parity of the owner. -/
abbrev Register := ℕ → Option ℕ

def update (a : Register) (j : ℕ) : Register :=
  fun owner => if owner = j % 2 then some j else a owner

/-- The mark is at edge zero. The ordinary row at v has posting v+2;
the anchor at d marks every edge not incident to d. -/
def Leaf (m : ℕ) (covered : Set ℕ) (a : Register) : Prop :=
  ∃ v < m, ((∀ r, a r = none) → v = 0) ∧
    (∀ r j, a r = some j → Incident v j) ∧
    (v + 1 < m → v + 2 ∈ covered) ∧
    ∀ d < 2, ¬Incident v d → d ∈ covered

inductive Tree where
  | leaf
  | offer (vertex : ℕ) (decline adopt : Tree)

/-- Both answers to every offer must win. -/
def Wins (m : ℕ) : Tree → Set ℕ → Register → Prop
  | .leaf, c, a => Leaf m c a
  | .offer j l r, c, a =>
    Wins m l (insert j c) a ∧ Wins m r (insert j c) (update a j)

/-- Vertices adopted on one play, in chronological order. -/
inductive Trace : Tree → List ℕ → Prop where
  | leaf : Trace .leaf []
  | decline {j l r xs} : Trace l xs → Trace (.offer j l r) xs
  | adopt {j l r xs} : Trace r xs → Trace (.offer j l r) (j :: xs)

private def Protected (c : Set ℕ) (a : Register) (k : ℕ) : Prop :=
  a (k % 2) = some k ∨ (a (k % 2) = none ∧ k < 2 ∧ k ∉ c)

private theorem leaf_incident {c : Set ℕ} {a : Register} {k v : ℕ}
    (h : Protected c a k)
    (active : ∀ r j, a r = some j → Incident v j)
    (anchors : ∀ d < 2, ¬Incident v d → d ∈ c) : Incident v k := by
  rcases h with h | ⟨_, hk, live⟩
  · exact active _ _ h
  · exact Classical.byContradiction (fun no => live (anchors k hk no))

private theorem keep {c : Set ℕ} {a : Register} {k j : ℕ}
    (h : Protected c a k) (different : k ≠ j) : Protected (insert j c) a k := by
  rcases h with h | ⟨ha, hk, live⟩
  · exact Or.inl h
  · exact Or.inr ⟨ha, hk, by simp [different, live]⟩

private theorem hold (c : Set ℕ) (a : Register) (k : ℕ) :
    Protected (insert k c) (update a k) k := Or.inl (by simp [update])

private theorem keep_other {c : Set ℕ} {a : Register} {k j : ℕ}
    (h : Protected c a k) (diff : k % 2 ≠ j % 2) :
    Protected (insert j c) (update a j) k := by
  have ne : k ≠ j := fun e => diff (congrArg (· % 2) e)
  simpa only [Protected, update, ite_eq_right diff] using keep h ne

/-- Even an implicit anchor whose register is still blank must meet
the opposite demand in any winning position. -/
private theorem compatible (m : ℕ) (t : Tree) {c : Set ℕ} {a : Register}
    (w : Wins m t c a) {k h : ℕ} (diff : k % 2 ≠ h % 2)
    (hk : Protected c a k) (hh : Protected c a h) :
    ∃ v, Incident v k ∧ Incident v h := by
  induction t generalizing c a with
  | leaf =>
    obtain ⟨v, _, _, active, _, anchors⟩ := w
    exact ⟨v, leaf_incident hk active anchors,
      leaf_incident hh active anchors⟩
  | offer j l r hl hr =>
    by_cases one : k = j
    · subst j
      exact hr w.2 (hold c a k) (keep_other hh diff.symm)
    by_cases two : h = j
    · subst j
      exact hr w.2 (keep_other hk diff) (hold c a h)
    exact hl w.1 (keep hk one) (keep hh two)

private theorem trace_exists (t : Tree) : ∃ xs, Trace t xs := by
  induction t with
  | leaf => exact ⟨[], .leaf⟩
  | offer _ _ _ ih _ =>
    obtain ⟨xs, h⟩ := ih
    exact ⟨xs, h.decline⟩

/-- A path of consecutive forward offers. -/
def consecutive (start : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => start :: consecutive (start + 1) k

private theorem milestones (m : ℕ) (t : Tree) {c : Set ℕ} {a : Register}
    (w : Wins m t c a) (i d : ℕ) (length : i + d + 1 = m)
    (p : Protected c a i) (q : Protected c a (i+1))
    (future : ∀ j, i + 2 ≤ j → j ≤ m → j ∉ c) :
    ∃ xs, Trace t xs ∧ (consecutive (i+2) d).Sublist xs := by
  induction t generalizing c a i d with
  | leaf =>
    obtain ⟨v, _, _, active, ordinary, anchors⟩ := w
    have h1 := leaf_incident p active anchors
    have h2 := leaf_incident q active anchors
    have eq : v = i := by unfold Incident at *; omega
    subst v
    have done : d = 0 := by
      by_contra no
      exact future _ (by omega) (by omega) (ordinary (by omega))
    subst d
    exact ⟨[], .leaf, .slnil⟩
  | offer j l r hl hr =>
    cases d with
    | zero =>
      obtain ⟨xs, tr⟩ := trace_exists (.offer j l r)
      exact ⟨xs, tr, List.nil_sublist _⟩
    | succ d =>
      by_cases ahead : i+2 ≤ j
      · have hj : j = i+2 := by
          by_cases parity : j % 2 = i % 2
          · have ne : j % 2 ≠ (i+1) % 2 := by omega
            obtain ⟨v, hj, hi⟩ := compatible m r w.2 ne (hold c a j) (keep_other q ne.symm)
            unfold Incident at hj hi
            omega
          · obtain ⟨v, hj, hi⟩ := compatible m r w.2 parity (hold c a j) (keep_other p (Ne.symm parity))
            unfold Incident at hj hi
            omega
        subst j
        have untouched : ∀ j, i+1+2 ≤ j → j ≤ m → j ∉ insert (i+2) c := by
          intro j ge bound
          have ne : j ≠ i+2 := by omega
          simp [ne, future _ (by omega : i+2 ≤ j) bound]
        obtain ⟨xs, hx, hsub⟩ := hr w.2 (i+1) d (by omega) (keep_other q (by omega))
          (hold c a (i+2)) untouched
        exact ⟨_, hx.adopt, List.Sublist.cons_cons _ hsub⟩
      · have untouched : ∀ k, i+2 ≤ k → k ≤ m → k ∉ insert j c := by
          intro k ge bound
          have ne : k ≠ j := by omega
          simp [ne, future _ ge bound]
        by_cases atI : i = j
        · subst j
          obtain ⟨xs, hx, hsub⟩ := hr w.2 i (d+1) length (hold c a i)
            (keep_other q (by omega)) untouched
          exact ⟨_, hx.adopt, hsub.cons _⟩
        by_cases atNext : i+1 = j
        · subst j
          obtain ⟨xs, hx, hsub⟩ := hr w.2 i (d+1) length (keep_other p (by omega))
            (hold c a (i+1)) untouched
          exact ⟨_, hx.adopt, hsub.cons _⟩
        obtain ⟨xs, hx, hsub⟩ := hl w.1 i (d+1) length (keep p atI) (keep q atNext) untouched
        exact ⟨_, hx.decline, hsub⟩

/-- From the blank register and full budget, every winning strategy has a
play adopting vertices 2,3,...,m in that order, possibly with intervening
adoptions. Their alternating parity counts changes between adopted owners. -/
theorem blank_forces_forward (d : ℕ) (t : Tree)
    (w : Wins (d+1) t ∅ (fun _ => none)) :
    ∃ xs, Trace t xs ∧ (consecutive 2 d).Sublist xs := by
  apply milestones (d+1) t w 0 d (by omega)
  · exact Or.inr ⟨rfl, by decide, Set.notMem_empty _⟩
  · exact Or.inr ⟨rfl, by decide, Set.notMem_empty _⟩
  · simp

/-- Offer the next vertex. On a decline its predecessor's row is free;
on adoption the adjacent pair advances one edge. -/
def forward (i : ℕ) : ℕ → Tree
  | 0 => .leaf
  | d + 1 => .offer (i+2) .leaf (forward (i+1) d)

/-- First cover the two anchor families, then play the path strategy. -/
def strategy (d : ℕ) : Tree :=
  let branch := Tree.offer 1 (forward 0 d) (forward 0 d)
  .offer 0 branch branch

private def AtEdge (a : Register) (i : ℕ) : Prop :=
  (∀ r j, a r = some j → r = j % 2 ∧ Incident i j) ∧
    ((∀ r, a r = none) → i = 0)

private theorem atEdge_next {a : Register} {i : ℕ} (h : AtEdge a i) :
    AtEdge (update a (i+2)) (i+1) := by
  constructor
  · intro r j active
    by_cases hr : r = (i+2) % 2
    · simp [update, hr] at active
      subst j
      exact ⟨hr, Or.inr rfl⟩
    · rw [update, ite_eq_right hr] at active
      obtain ⟨color, hj⟩ := h.1 r j active
      refine ⟨color, Or.inl ?_⟩
      unfold Incident at hj
      omega
  · intro blank
    have e := blank ((i+2) % 2)
    simp [update] at e

private theorem forward_wins (m i d : ℕ) (length : i+d+1=m) (c : Set ℕ)
    (anchors : ∀ k < 2, k ∈ c) (a : Register) (h : AtEdge a i) :
    Wins m (forward i d) c a := by
  induction d generalizing i c a with
  | zero =>
    refine ⟨i, by omega, h.2, fun r j act => (h.1 r j act).2, ?_, ?_⟩
    · omega
    · exact fun k hk _ => anchors k hk
  | succ d ih =>
    constructor
    · exact ⟨i, by omega, h.2, fun r j act => (h.1 r j act).2,
        fun _ => Set.mem_insert _ _, fun k hk _ => Set.mem_insert_of_mem _ (anchors k hk)⟩
    · exact ih (i+1) (by omega) _ (fun k hk => Set.mem_insert_of_mem _ (anchors k hk)) _
        (atEdge_next h)

/-- The blank path instance is feasible for every length. -/
theorem strategy_wins (d : ℕ) : Wins (d+1) (strategy d) ∅ (fun _ => none) := by
  have anchors : ∀ k < 2, k ∈ (insert 1 (insert 0 (∅ : Set ℕ))) := by
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have play (a : Register) (h : AtEdge a 0) :=
    forward_wins (d+1) 0 d (by omega) _ anchors a h
  have base : AtEdge (fun _ => none) 0 := ⟨by simp, fun _ => rfl⟩
  have add {a : Register} (h : AtEdge a 0) (j : ℕ) (hj : Incident 0 j) :
      AtEdge (update a j) 0 := by
    refine ⟨?_, fun _ => rfl⟩
    intro r k active
    by_cases hr : r = j % 2
    · simp [update, hr] at active
      subst k
      exact ⟨hr, hj⟩
    · exact h.1 r k (by simpa only [update, ite_eq_right hr] using active)
  exact ⟨⟨play _ base, play _ (add base 1 (Or.inr rfl))⟩,
    ⟨play _ (add base 0 (Or.inl rfl)),
      play _ (add (add base 0 (Or.inl rfl)) 1 (Or.inr rfl))⟩⟩

end KFOL.Core.OfferPath
