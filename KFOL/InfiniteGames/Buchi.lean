module

public import KFOL.Definitions.InfiniteGames
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Fin.Basic

/-! # Exact finite witnesses for reachability and infinite witnesses for Büchi -/

@[expose] public section

namespace KFOL.InfiniteGames

attribute [local instance] Classical.propDecidable

universe u
variable {State : Type u} {step : State → State → Prop}
variable {allowed target visits : Set State}

def guardedReachHom (step : State → State → Prop) (allowed target : Set State) :
    Set State →o Set State where
  toFun current := target ∪ (allowed ∩ pre step current)
  monotone' _ _ smaller := Set.union_subset_union (Set.Subset.refl _)
    (Set.inter_subset_inter (Set.Subset.refl _)
      (fun _ ⟨next, edge, member⟩ => ⟨next, edge, smaller member⟩))

/-- A finite path of the displayed length, with every preterminal state allowed. -/
inductive Reaches (step : State → State → Prop) (allowed target : Set State) :
    ℕ → State → Prop
  | zero {state} : state ∈ target → Reaches step allowed target 0 state
  | succ {n state next} : state ∈ allowed → step state next →
      Reaches step allowed target n next → Reaches step allowed target (n + 1) state

theorem Reaches.mem_reach {n : ℕ} {state : State}
    (path : Reaches step allowed target n state) : state ∈ (guardedReachHom step allowed target).lfp := by
  induction path with
  | zero member =>
    rw [← (guardedReachHom step allowed target).map_lfp]
    exact Or.inl member
  | succ permitted edge _ ih =>
    rw [← (guardedReachHom step allowed target).map_lfp]
    exact Or.inr ⟨permitted, _, edge, ih⟩

theorem mem_reach_iff {state : State} :
    state ∈ (guardedReachHom step allowed target).lfp ↔ ∃ n, Reaches step allowed target n state := by
  constructor
  · intro member
    have smaller : (guardedReachHom step allowed target).lfp ⊆
        {state | ∃ n, Reaches step allowed target n state} := by
      apply (guardedReachHom step allowed target).lfp_le
      intro state reachOne
      rcases reachOne with final | ⟨permitted, next, edge, n, rest⟩
      · exact ⟨0, .zero final⟩
      · exact ⟨n + 1, .succ permitted edge rest⟩
    exact smaller member
  · rintro ⟨n, path⟩
    exact path.mem_reach

theorem Reaches.mono_target {n : ℕ} {state : State}
    (path : Reaches step allowed target n state) {other : Set State}
    (smaller : target ⊆ other) : Reaches step allowed other n state := by
  induction path with
  | zero member => exact .zero (smaller member)
  | succ permitted edge _ ih => exact .succ permitted edge ih

theorem Reaches.mem_allowed {n : ℕ} {state : State}
    (path : Reaches step allowed target n state) (closed : target ⊆ allowed) :
    state ∈ allowed := by
  cases path with
  | zero member => exact closed member
  | succ permitted _ _ => exact permitted

private theorem until_eq_guarded (step : State → State → Prop)
    (allowed visits current : Set State) :
    untilHom step allowed visits current =
      guardedReachHom step allowed (visits ∩ pre step current) := rfl

private theorem buchi_unfold (step : State → State → Prop)
    (allowed visits : Set State) :
    buchi step allowed visits =
      (guardedReachHom step allowed (visits ∩ pre step (buchi step allowed visits))).lfp :=
  (buchiHom step allowed visits).map_gfp.symm

private theorem buchi_finite {state : State}
    (member : state ∈ buchi step allowed visits) :
    ∃ n, Reaches step allowed (visits ∩ pre step (buchi step allowed visits)) n state := by
  apply mem_reach_iff.mp
  simpa only [← buchi_unfold] using member

private noncomputable def buchiRank (state : buchi step allowed visits) : ℕ :=
  Nat.find (buchi_finite state.property)

private theorem buchi_rank_path (state : buchi step allowed visits) :
    Reaches step allowed (visits ∩ pre step (buchi step allowed visits))
      (buchiRank state) state.val := Nat.find_spec (buchi_finite state.property)

private theorem buchi_rank_min (state : buchi step allowed visits) {n : ℕ}
    (path : Reaches step allowed (visits ∩ pre step (buchi step allowed visits)) n state.val) :
    buchiRank state ≤ n := Nat.find_min' (buchi_finite state.property) path

private theorem buchi_rank_zero (state : buchi step allowed visits)
    (zero : buchiRank state = 0) : state.val ∈ visits := by
  have path := buchi_rank_path state
  rw [zero] at path
  cases path with | zero member => exact member.1

private theorem buchi_next (state : buchi step allowed visits) :
    ∃ next : buchi step allowed visits,
      step state.val next.val ∧
      (buchiRank state ≠ 0 → buchiRank next < buchiRank state) := by
  have path := buchi_rank_path state
  cases rankEq : buchiRank state with
  | zero =>
    rw [rankEq] at path
    cases path with
    | zero member =>
      obtain ⟨next, edge, memberNext⟩ := member.2
      exact ⟨⟨next, memberNext⟩, edge, by simp⟩
  | succ n =>
    rw [rankEq] at path
    cases path with
    | @succ n state next permitted edge rest =>
      have nextMember : next ∈ buchi step allowed visits := by
        rw [buchi_unfold]
        exact rest.mem_reach
      refine ⟨⟨_, nextMember⟩, edge, fun _ => ?_⟩
      exact (buchi_rank_min _ rest).trans_lt (by omega)

private theorem eventual_zero {S : Type u} (next : S → S) (rank : S → ℕ)
    (decreases : ∀ x, rank x ≠ 0 → rank (next x) < rank x) (x : S) :
    ∃ n, rank (next^[n] x) = 0 := by
  induction h : rank x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases zero : rank x = 0
    · exact ⟨0, zero⟩
    · obtain ⟨k, hk⟩ := ih (rank (next x)) (by simpa only [← h] using decreases x zero)
        (next x) rfl
      exact ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩

/-- The nested ν/μ formula is equivalent to the existence of an actual
infinite path; no determinacy or finiteness assumption is involved. -/
theorem mem_buchi_iff (inside : visits ⊆ allowed) {state : State} :
    state ∈ buchi step allowed visits ↔ BuchiRun step allowed visits state := by
  classical
  constructor
  · intro member
    let S := buchi step allowed visits
    let next : S → S := fun x => (buchi_next x).choose
    have edge (x : S) : step x.val (next x).val := (buchi_next x).choose_spec.1
    have decreases (x : S) : buchiRank x ≠ 0 → buchiRank (next x) < buchiRank x :=
      (buchi_next x).choose_spec.2
    let start : S := ⟨state, member⟩
    let run : ℕ → S := fun n => next^[n] start
    refine ⟨fun n => (run n).val, rfl, ?_, ?_, ?_⟩
    · intro n
      exact (by simpa only [run, Function.iterate_succ_apply'] using edge (run n))
    · intro n
      exact (buchi_rank_path (run n)).mem_allowed (fun _ h => inside h.1)
    · intro n
      obtain ⟨k, hk⟩ := eventual_zero next buchiRank decreases (run n)
      refine ⟨k + n, Nat.le_add_left n k, ?_⟩
      apply buchi_rank_zero
      simpa only [run, Function.iterate_add_apply] using hk
  · rintro ⟨run, initial, edges, permitted, recurrent⟩
    have post : Set.range run ⊆ buchiHom step allowed visits (Set.range run) := by
      rintro _ ⟨n, rfl⟩
      obtain ⟨m, later, visiting⟩ := recurrent n
      have endpoint : run m ∈ visits ∩ pre step (Set.range run) :=
        ⟨visiting, run (m + 1), edges m, m + 1, rfl⟩
      have finitePath : ∀ k j, j + k = m →
          Reaches step allowed (visits ∩ pre step (Set.range run)) k (run j) := by
        intro k
        induction k with
        | zero =>
          intro j equal
          have same : j = m := by omega
          subst j
          exact .zero endpoint
        | succ k ih =>
          intro j equal
          exact .succ (permitted j) (edges j) (ih (j + 1) (by omega))
      exact (finitePath (m - n) n (by omega)).mem_reach
    have member := (buchiHom step allowed visits).le_gfp post
      (show run 0 ∈ Set.range run from ⟨0, rfl⟩)
    change run 0 ∈ buchi step allowed visits at member
    rwa [initial] at member

private theorem reach_eq_guarded (step : State → State → Prop) (target : Set State) :
    reachHom step target = guardedReachHom step Set.univ target := by
  ext current state
  change (state ∈ target ∨ state ∈ pre step current) ↔
    state ∈ target ∨ (state ∈ Set.univ ∧ state ∈ pre step current)
  simp only [Set.mem_univ, true_and]

theorem mem_reach_iff_path {state : State} :
    state ∈ reach step target ↔ ∃ n, Reaches step Set.univ target n state := by
  change state ∈ (reachHom step target).lfp ↔ _
  rw [reach_eq_guarded]
  exact mem_reach_iff

/-- Highest recurrent priority semantics of the finite-prefix/Büchi formula. -/
theorem mem_priorityRegion_iff {n : ℕ} (priority : State → Fin n) (p : Fin n)
    {state : State} :
    state ∈ priorityRegion step priority p ↔
      ∃ run : ℕ → State, run 0 = state ∧
        (∀ k, step (run k) (run (k + 1))) ∧
        (∀ N, ∃ k, N ≤ k ∧ priority (run k) = p) ∧
        ∃ N, ∀ k, N ≤ k → priority (run k) ≤ p := by
  constructor
  · intro member
    obtain ⟨length, path⟩ := mem_reach_iff_path.mp member
    clear member
    induction path with
    | zero final =>
      obtain ⟨run, initial, edges, permitted, recurrent⟩ :=
        (mem_buchi_iff (step := step)
          (allowed := {x | priority x ≤ p}) (visits := {x | priority x = p})
          (fun _ equal => le_of_eq equal)).mp final
      exact ⟨run, initial, edges, recurrent, 0, fun k _ => permitted k⟩
    | @succ length state next _ edge path ih =>
      obtain ⟨run, initial, edges, recurrent, N, cutoff⟩ := ih
      let extended : ℕ → State | 0 => state | k + 1 => run k
      refine ⟨extended, rfl, ?_, ?_, N + 1, ?_⟩
      · intro k
        cases k with
        | zero => simpa only [extended, initial] using edge
        | succ k => exact edges k
      · intro k
        obtain ⟨m, later, visiting⟩ := recurrent k
        exact ⟨m + 1, by omega, visiting⟩
      · intro k later
        cases k with
        | zero => omega
        | succ k => exact cutoff k (by omega)
  · rintro ⟨run, initial, edges, recurrent, N, cutoff⟩
    have tailMember : run N ∈ buchi step {x | priority x ≤ p} {x | priority x = p} := by
      apply (mem_buchi_iff (step := step)
          (allowed := {x | priority x ≤ p}) (visits := {x | priority x = p})
          (fun _ equal => le_of_eq equal)).mpr
      refine ⟨fun k => run (N + k), by simp, fun k => ?_, fun k => ?_, fun k => ?_⟩
      · simpa only [Nat.add_assoc] using edges (N + k)
      · exact cutoff (N + k) (by omega)
      · obtain ⟨m, later, visiting⟩ := recurrent (N + k)
        refine ⟨m - N, by omega, ?_⟩
        change priority (run (N + (m - N))) = p
        simpa only [Nat.add_sub_of_le (by omega : N ≤ m)] using visiting
    have finitePath : ∀ k j, j + k = N → Reaches step Set.univ
        (buchi step {x | priority x ≤ p} {x | priority x = p}) k (run j) := by
      intro k
      induction k with
      | zero =>
        intro j equal
        have same : j = N := by omega
        subst j
        exact .zero tailMember
      | succ k ih =>
        intro j equal
        exact .succ (Set.mem_univ _) (edges j) (ih (j + 1) (by omega))
    apply mem_reach_iff_path.mpr
    exact ⟨N, initial ▸ finitePath N 0 (by omega)⟩

end KFOL.InfiniteGames



