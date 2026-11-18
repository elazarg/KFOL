module

public import KFOL.Algebra.Semilattice
public import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.EquivFin

/-! # The greatest safe pool for an owned fold

A child violating a bound may remain in the pool exactly when another child
can absorb at that row. Universal child tests are in `base`. Existential
tests can be checked on the greatest pool one at a time.
-/

@[expose] public section
namespace KFOL.Core.OwnerFoldClosure

variable {Column Row Demand : Type*}

/-- Remove a column if one of its violated bounds has no repair in the
current pool. -/
def step (base : Set Column) (ok hit : Row → Column → Prop) :
    Set Column →o Set Column where
  toFun pool := {c | c ∈ base ∧ ∀ i, ¬ ok i c → ∃ d ∈ pool, hit i d}
  monotone' := by
    intro _ _ sub _ c
    exact ⟨c.1, fun i bad => let ⟨d, hd, h⟩ := c.2 i bad; ⟨d, sub hd, h⟩⟩

/-- The greatest pool all of whose members are safe together in the fold. -/
def greatestPool (base : Set Column) (ok hit : Row → Column → Prop) : Set Column :=
  (step base ok hit).gfp

theorem greatestPool_fixed (base : Set Column) (ok hit : Row → Column → Prop) :
    step base ok hit (greatestPool base ok hit) = greatestPool base ok hit :=
  (step base ok hit).map_gfp

theorem mem_greatestPool_iff (base : Set Column) (ok hit : Row → Column → Prop) (c : Column) :
    c ∈ greatestPool base ok hit ↔
      c ∈ base ∧ ∀ i, ¬ ok i c → ∃ d ∈ greatestPool base ok hit, hit i d := by
  rw [← Set.ext_iff.mp (greatestPool_fixed base ok hit) c]
  rfl

theorem subset_greatestPool {base : Set Column} {ok hit : Row → Column → Prop} {pool : Set Column}
    (safe : pool ⊆ step base ok hit pool) : pool ⊆ greatestPool base ok hit :=
  (step base ok hit).le_gfp safe

def respecting (base : Set Column) (ok : Row → Column → Prop) (required : Set Row) :
    Set Column :=
  {c | c ∈ base ∧ ∀ i ∈ required, ok i c}

def missing (hit : Row → Column → Prop) (pool : Set Column) : Set Row :=
  {i | ¬ ∃ c ∈ pool, hit i c}

private theorem respecting_antitone (base : Set Column) (ok : Row → Column → Prop) :
    Antitone (respecting base ok) :=
  fun _ _ sub _ c => ⟨c.1, fun i hi => c.2 i (sub hi)⟩

/-- Force each bound that no eligible child can repair. -/
def force (base : Set Column) (ok hit : Row → Column → Prop) : Set Row →o Set Row :=
  { toFun := fun rows => missing hit (respecting base ok rows)
    monotone' := by
      intro _ _ sub i none ⟨c, hc, h⟩
      exact none ⟨c, ⟨hc.1, fun j hj => hc.2 j (sub hj)⟩, h⟩ }

private theorem step_eq_respecting (base : Set Column) (ok hit : Row → Column → Prop)
    (pool : Set Column) : step base ok hit pool = respecting base ok (missing hit pool) := by
  classical
  ext c
  change (c ∈ base ∧ ∀ i, ¬ ok i c → ∃ d ∈ pool, hit i d) ↔
    (c ∈ base ∧ ∀ i, (¬ ∃ d ∈ pool, hit i d) → ok i c)
  refine and_congr_right fun _ => forall_congr' fun _ => ⟨?_, ?_⟩
  · intro repair none
    by_contra bad
    exact none (repair bad)
  · intro forced bad
    by_contra none
    exact bad (forced none)

/-- The greatest safe pool is obtained using the least closed set of rows
that must be checked on every child. -/
theorem greatestPool_eq_respecting (base : Set Column) (ok hit : Row → Column → Prop) :
    greatestPool base ok hit = respecting base ok (force base ok hit).lfp := by
  let S := (force base ok hit).lfp
  let P := greatestPool base ok hit
  have fixed : missing hit (respecting base ok S) = S := (force base ok hit).map_lfp
  have reqFixed : step base ok hit (respecting base ok S) = respecting base ok S := by
    rw [step_eq_respecting, fixed]
  have pFixed : respecting base ok (missing hit P) = P := by
    rw [← step_eq_respecting, greatestPool_fixed]
  have closed : force base ok hit (missing hit P) ⊆ missing hit P := by
    change missing hit (respecting base ok (missing hit P)) ⊆ missing hit P
    rw [pFixed]
  apply Set.Subset.antisymm
  · change P ⊆ respecting base ok S
    rw [← pFixed]
    exact respecting_antitone base ok ((force base ok hit).lfp_le closed)
  · exact subset_greatestPool reqFixed.ge

/-- The greatest pool decides all existential tests simultaneously.
Finiteness is required only for the lists of rows and demands, since at most
one repair per row, one witness per demand and one default child are needed
in addition to the prescribed finite set of children. -/
theorem exists_finset_pool_iff [Finite Row] [Finite Demand]
    (base : Set Column) (ok hit : Row → Column → Prop) (witness : Demand → Column → Prop)
    (required : Finset Column) :
    (∃ pool : Finset Column, pool.Nonempty ∧ (pool : Set Column) ⊆ base ∧
      required ⊆ pool ∧
      (∀ i, (∀ c ∈ pool, ok i c) ∨ ∃ c ∈ pool, hit i c) ∧
      (∀ j, ∃ c ∈ pool, witness j c)) ↔
    (greatestPool base ok hit).Nonempty ∧ (required : Set Column) ⊆ greatestPool base ok hit ∧
      ∀ j, ∃ c ∈ greatestPool base ok hit, witness j c := by
  classical
  let P := greatestPool base ok hit
  constructor
  · rintro ⟨pool, nonempty, sub, contains, good, existsTest⟩
    have contained : (pool : Set Column) ⊆ P := subset_greatestPool (by
      intro c hc
      exact ⟨sub hc, fun i bad => (good i).resolve_left (fun h => bad (h c hc))⟩)
    exact ⟨(Finset.coe_nonempty.mpr nonempty).mono contained,
      fun _ hc => contained (contains hc), fun j => by
      obtain ⟨c, hc, test⟩ := existsTest j
      exact ⟨c, contained hc, test⟩⟩
  · rintro ⟨⟨default, mem⟩, requiredSub, existsTest⟩
    let _ := Fintype.ofFinite Row
    let _ := Fintype.ofFinite Demand
    choose selected hselected using existsTest
    let R : Finset Row := Finset.univ.filter (fun i => ∃ c ∈ P, hit i c)
    let repair (i : Row) : Column :=
      if h : ∃ c ∈ P, hit i c then h.choose else default
    let witnesses : Finset Column := insert default (R.image repair ∪ Finset.univ.image selected)
    let pool : Finset Column := required ∪ witnesses
    have repair_spec {i : Row} (hi : i ∈ R) : repair i ∈ P ∧ hit i (repair i) := by
      have h := (Finset.mem_filter.mp hi).2
      simpa only [repair, dite_eq_left h] using h.choose_spec
    have witnessSub : (witnesses : Set Column) ⊆ P := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact mem
      rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
        exact (repair_spec hi).1
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
        exact (hselected j).1
    have poolSub : (pool : Set Column) ⊆ P := by
      intro col hc
      exact (Finset.mem_union.mp hc).elim (fun h => requiredSub h) (fun h => witnessSub h)
    have memPool : witnesses ⊆ pool := Finset.subset_union_right
    refine ⟨pool, ⟨default, memPool (Finset.mem_insert_self _ _)⟩, ?_,
      Finset.subset_union_left, ?_, ?_⟩
    · exact fun c hc => ((mem_greatestPool_iff base ok hit c).mp (poolSub hc)).1
    · intro i
      by_cases hi : i ∈ R
      · exact Or.inr ⟨repair i, memPool (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩))), (repair_spec hi).2⟩
      · refine Or.inl fun c hc => ?_
        by_contra bad
        have h := ((mem_greatestPool_iff base ok hit c).mp (poolSub hc)).2 i bad
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · intro j
      exact ⟨selected j, memPool (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))), (hselected j).2⟩

open WinnerSet
variable {Role : Type*}

theorem fold_bound_iff (r : Role) (pool : Finset Column) (hn : pool.Nonempty)
    (values : Column → WinnerSet Role) (allowed : Set Role) :
    (choiceFold r pool hn values).val ⊆ allowed ↔
      (∀ c ∈ pool, (values c).val ⊆ allowed) ∨
      ∃ c ∈ pool, r ∈ allowed ∧ values c = singleton r := by
  classical
  by_cases yes : ∃ c ∈ pool, values c = singleton r
  · rw [(choiceFold_eq_owner_iff r pool hn values).mpr yes]
    change ({r} : Set Role) ⊆ allowed ↔ _
    rw [Set.singleton_subset_iff]
    constructor
    · intro hr
      obtain ⟨c, hc, eq⟩ := yes
      exact Or.inr ⟨c, hc, hr, eq⟩
    · rintro (good | ⟨c, hc, hr, _⟩)
      · obtain ⟨c, hc, eq⟩ := yes
        exact good c hc (eq ▸ (show r ∈ (singleton r).val from rfl))
      · exact hr
  · have none : ∀ c ∈ pool, values c ≠ singleton r := fun c hc he => yes ⟨c, hc, he⟩
    constructor
    · intro bound
      exact Or.inl fun c hc k hk =>
        bound ((mem_choiceFold_of_no_owner r pool hn values none k).mpr ⟨c, hc, hk⟩)
    · rintro (all | ⟨c, hc, _, eq⟩) k hk
      · obtain ⟨c, hc, m⟩ := (mem_choiceFold_of_no_owner r pool hn values none k).mp hk
        exact all c hc m
      · exact (none c hc eq).elim

theorem fold_mem_iff (r : Role) (pool : Finset Column) (hn : pool.Nonempty)
    (values : Column → WinnerSet Role) (k : Role) :
    k ∈ (choiceFold r pool hn values).val ↔
      (∃ c ∈ pool, k ∈ (values c).val) ∧
      (r ≠ k → ∀ c ∈ pool, values c ≠ singleton r) := by
  classical
  by_cases yes : ∃ c ∈ pool, values c = singleton r
  · rw [(choiceFold_eq_owner_iff r pool hn values).mpr yes]
    change k = r ↔ _
    obtain ⟨c, hc, eq⟩ := yes
    constructor
    · rintro rfl
      exact ⟨⟨c, hc, eq ▸ (show k ∈ (singleton k).val from rfl)⟩, fun h => (h rfl).elim⟩
    · intro h
      by_contra diff
      exact h.2 (Ne.symm diff) c hc eq
  · have none : ∀ c ∈ pool, values c ≠ singleton r := fun c hc he => yes ⟨c, hc, he⟩
    rw [mem_choiceFold_of_no_owner r pool hn values none]
    exact ⟨fun h => ⟨h, fun _ => none⟩, And.left⟩

/-- Three successive owners suffice to take the union of a nonempty finite
family, regardless of the number of operands. -/
theorem val_union_three_folds (a b c : Role) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (pool : Finset Column) (hn : pool.Nonempty) (values : Column → WinnerSet Role) :
    (choiceFold a pool hn (fun i => choice b (values i) (choiceFold c pool hn values))).val =
      ⋃ i ∈ pool, (values i).val := by
  classical
  let U : Set Role := ⋃ i ∈ pool, (values i).val
  let inner := choiceFold c pool hn values
  let middle i := choice b (values i) inner
  have sub i (hi : i ∈ pool) : (values i).val ⊆ U :=
    fun k hk => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hk⟩⟩
  have innerSub : inner.val ⊆ U := (fold_bound_iff c pool hn values U).mpr (Or.inl sub)
  have midSub i (hi : i ∈ pool) : (middle i).val ⊆ U :=
    (choice_subset_union b _ _).trans (Set.union_subset (sub i hi) innerSub)
  have midRetains i (hi : i ∈ pool) : (values i).val ⊆ (middle i).val := by
    by_cases atom : values i = singleton b ∨ inner = singleton b
    · change (values i).val ⊆ (choice b (values i) inner).val
      rw [choice, ite_eq_left atom]
      rcases atom with eq | eq
      · rw [eq]
      · rw [(choiceFold_eq_other_iff c b bc.symm pool hn values).mp eq i hi]
    · change (values i).val ⊆ (choice b (values i) inner).val
      rw [choice, ite_eq_right atom]
      exact Set.subset_union_left
  change (choiceFold a pool hn middle).val = U
  apply Set.Subset.antisymm ((fold_bound_iff a pool hn middle U).mpr (Or.inl midSub))
  intro k hk
  obtain ⟨i, hi, mem⟩ := by simpa only [U, Set.mem_iUnion] using hk
  by_cases absorbs : ∃ j ∈ pool, middle j = singleton a
  · rw [(choiceFold_eq_owner_iff a pool hn middle).mpr absorbs]
    obtain ⟨j, _, h⟩ := absorbs
    have eq : inner = singleton a := (choice_eq_other_iff _ _ _ ab.symm).mp h |>.2
    rwa [(choiceFold_eq_other_iff c a ac.symm pool hn values).mp eq i hi] at mem
  · exact (mem_choiceFold_of_no_owner a pool hn middle
      (fun j hj eq => absorbs ⟨j, hj, eq⟩) k).mpr ⟨i, hi, midRetains i hi mem⟩

/-- Tests besides the ordinary winner-set upper bounds. -/
inductive Observation (Row Role : Type*)
  | atom (i : Row) (r : Role)
  | notAtom (i : Row) (r : Role)
  | winner (i : Row) (r : Role)

def Observation.holds : Observation Row Role → (Row → WinnerSet Role) → Prop
  | .atom i a, col => col i = singleton a
  | .notAtom i a, col => col i ≠ singleton a
  | .winner i a, col => a ∈ (col i).val

def Observation.onEvery (owner : Role) : Observation Row Role → (Row → WinnerSet Role) → Prop
  | .atom i a, col => owner ≠ a → col i = singleton a
  | .notAtom i a, col => owner = a → col i ≠ singleton a
  | .winner i a, col => owner ≠ a → col i ≠ singleton owner

def Observation.onSome (owner : Role) : Observation Row Role → (Row → WinnerSet Role) → Prop
  | .atom i a, col => owner = a → col i = singleton a
  | .notAtom i a, col => owner ≠ a → col i ≠ singleton a
  | .winner i a, col => a ∈ (col i).val

theorem fold_observation_iff (owner : Role) (pool : Finset (Row → WinnerSet Role))
    (nonempty : pool.Nonempty) (test : Observation Row Role) :
    test.holds (fun i => choiceFold owner pool nonempty (fun col => col i)) ↔
    (∀ col ∈ pool, test.onEvery owner col) ∧ ∃ col ∈ pool, test.onSome owner col := by
  classical
  cases test with
  | atom i a =>
    by_cases eq : owner = a
    · subst a
      simp only [Observation.holds, Observation.onEvery, Observation.onSome,
        choiceFold_eq_owner_iff, ne_eq, not_true_eq_false, false_implies, implies_true,
        true_implies, true_and]
    · rw [Observation.holds, choiceFold_eq_other_iff _ _ eq]
      simp [Observation.onEvery, Observation.onSome, eq]
      exact fun _ => nonempty
  | notAtom i a =>
    by_cases eq : owner = a
    · subst a
      simp [Observation.holds, Observation.onEvery, Observation.onSome,
        choiceFold_eq_owner_iff]
      exact fun _ => nonempty
    · simp [Observation.holds, Observation.onEvery, Observation.onSome,
        choiceFold_eq_other_iff _ _ eq, eq]
  | winner i a =>
    rw [Observation.holds, fold_mem_iff]
    simp only [Observation.onEvery, Observation.onSome]
    exact ⟨fun h => ⟨fun c hc diff => h.2 diff c hc, h.1⟩,
      fun h => ⟨h.2, fun diff c hc => h.1 c hc diff⟩⟩

/-- The fold test applies to arbitrary row values and signed atom tests.
Each required existential test is decided separately on the greatest pool. -/
theorem exists_observational_fold_iff [Finite Row] [Finite Demand]
    (owner : Role) (allowed : Row → Set Role) (tests : Demand → Observation Row Role)
    (available : Set (Row → WinnerSet Role)) (required : Finset (Row → WinnerSet Role)) :
    let B := {col ∈ available | ∀ j, (tests j).onEvery owner col}
    let ok i (col : Row → WinnerSet Role) := (col i).val ⊆ allowed i
    let hit i (col : Row → WinnerSet Role) := owner ∈ allowed i ∧ col i = singleton owner
    let P := greatestPool B ok hit
    (∃ (pool : Finset (Row → WinnerSet Role)) (ne : pool.Nonempty),
      (pool : Set (Row → WinnerSet Role)) ⊆ available ∧ required ⊆ pool ∧
      (∀ i, (choiceFold owner pool ne (fun col => col i)).val ⊆ allowed i) ∧
      (∀ j, (tests j).holds (fun i => choiceFold owner pool ne (fun col => col i)))) ↔
    P.Nonempty ∧ (required : Set (Row → WinnerSet Role)) ⊆ P ∧
      ∀ j, ∃ col ∈ P, (tests j).onSome owner col := by
  dsimp only
  rw [← exists_finset_pool_iff]
  constructor
  · rintro ⟨pool, hn, sub, contains, bounds, obs⟩
    refine ⟨pool, hn, ?_, contains, fun i => (fold_bound_iff owner pool hn _ _).mp (bounds i), ?_⟩
    · intro col hc
      exact ⟨sub hc, fun j => ((fold_observation_iff owner pool hn (tests j)).mp (obs j)).1 col hc⟩
    · exact fun j => ((fold_observation_iff owner pool hn (tests j)).mp (obs j)).2
  · rintro ⟨pool, hn, sub, contains, bounds, obs⟩
    refine ⟨pool, hn, fun _ hc => (sub hc).1, contains,
      fun i => (fold_bound_iff owner pool hn _ _).mpr (bounds i), fun j => ?_⟩
    exact (fold_observation_iff owner pool hn (tests j)).mpr
      ⟨fun col hc => (sub hc).2 j, obs j⟩

end KFOL.Core.OwnerFoldClosure
