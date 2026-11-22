module

public import KFOL.Core.MonochromaticHeadCuts

/-! # Ranked obstructions with coded postings at three owners -/

@[expose] public section
namespace KFOL.Core.CodedPostingObstruction

open Sources AcyclicSourceQueries ProfileBudgets
attribute [local instance] Equational.coreStructure

/-- Blocks in order `w,x,y,z`, with owners in order `a,b,c`.
Each entry allows both possible posting colors when that slot carries a bit. -/
def allowed (head target : Fin 4) (owner : Fin 3) : Bool :=
  let table : List (List (List (Fin 3))) :=
    [[[], [1], [], [1, 2]],
     [[2], [], [2], [1]],
     [[0, 2], [0], [], [2]],
     [[0], [0], [0, 1], []]]
  owner ∈ (table[head.val]!)[target.val]!

/-- Each row is indexed by owner and its entries are decreasing ranks
of the four blocks. -/
def rank (owner : Fin 3) (block : Fin 4) : ℕ :=
  let ranks : List (List ℕ) := [[1, 0, 2, 3], [3, 2, 0, 1], [1, 3, 2, 0]]
  (ranks[owner.val]!)[block.val]!

theorem rank_decreases :
    ∀ head target owner, allowed head target owner = true → rank owner target < rank owner head :=
  by decide

def anchor (head target : Fin 4) : Option (Fin 3) :=
  let table : List (List (Option (Fin 3))) :=
    [[none, some 1, none, some 2],
     [some 2, none, some 2, some 1],
     [some 2, some 0, none, some 2],
     [some 0, some 0, some 1, none]]
  (table[head.val]!)[target.val]!

/-- The unmodified anchor postings conflict at an outside block for
every proper set of at least two blocks. -/
theorem anchor_boundary_conflict :
    ∀ H : Finset (Fin 4), 2 ≤ H.card → H ≠ Finset.univ →
      ∃ j ∉ H, ∃ i ∈ H, ∃ l ∈ H, ∃ r s : Fin 3,
        anchor i j = some r ∧ anchor l j = some s ∧ r ≠ s := by decide

/-- Every word supplies a mark among the rows, even if arbitrarily many
copies of each block choose different allowed postings. -/
theorem no_omitting_word {Role Var : Type*} [DecidableEq Role] (three : Fin 3 ↪ Role)
    (block : Var → Fin 4)
    (row : Var → ProbeIndex Role Var) (head : ∀ j, (row j).2.1 = j)
    (posts : ∀ j i r, posting (row j) i = some r →
      ∃ s, three s = r ∧ allowed (block j) (block i) s = true)
    (t : CoreTerm Role Var) :
    ∃ j, (row j).1 ∈ (t.realize (probeAt three (row j))).val := by
  classical
  let blockRank (r : Role) (h : Fin 4) :=
    if e : ∃ s, three s = r then rank (Classical.choose e) h else 0
  have rank_on_image (s : Fin 3) (h : Fin 4) : blockRank (three s) h = rank s h := by
    change (if e : ∃ c, three c = three s then rank (Classical.choose e) h else 0) = rank s h
    have e : ∃ c, three c = three s := ⟨s, rfl⟩
    rw [dite_eq_left e, three.injective (Classical.choose_spec e)]
  apply exists_surviving_head_of_ranked_postings three row head (fun r i => blockRank r (block i))
    ?_ t
  intro j i r posting_eq
  obtain ⟨s, rfl, hs⟩ := posts j i r posting_eq
  simpa only [rank_on_image] using
    (rank_decreases (block j) (block i) s hs)

end KFOL.Core.CodedPostingObstruction
