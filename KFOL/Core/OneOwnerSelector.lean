module

public import KFOL.Core.ProfileBudgets.Folds
public import KFOL.Core.SingletonProfileAbsorption

/-! # A one-owner envelope and a selector for two groups

For budgets with one possible absorbing owner, a Horn closure computes
every possible output winner at every valuation. A selector switches
between two such group envelopes on its two designated singleton menus.
-/

@[expose] public section
namespace KFOL.Core.OneOwnerSelector

open ProfileBudgets WinnerSet

variable {Role V Row : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

omit [DecidableEq Role] in
private theorem nonatom_of_mem {r k : Role} (ne : k ≠ r) {m : WinnerSet Role}
    (h : k ∈ m.val) : m ≠ singleton r := by
  rintro rfl
  exact ne h

/-- Follow a chosen winner at an arbitrary valuation while pruning all
foreign gates. For a foreign winner keep the owner from absorbing in any
child where the original value was already nonabsorbing. -/
theorem prune_winner (r k : Role) (v : V → WinnerSet Role) (t : CoreTerm Role V) :
    ∃ p, Prunes r t p ∧
      (k ∈ (t.realize v).val → k ∈ (p.realize v).val) ∧
      (k ≠ r → t.realize v ≠ singleton r → p.realize v ≠ singleton r) := by
  induction t using induction_choice with
  | var i => exact ⟨.var i, .var i, id, fun _ => id⟩
  | choice d x y ihx ihy =>
    obtain ⟨u, xu, xk, xn⟩ := ihx
    obtain ⟨w, yw, yk, yn⟩ := ihy
    by_cases same : d = r
    · subst d
      refine ⟨choiceTerm r u w, .owned xu yw, ?_, ?_⟩
      · rw [realize_choice_winner, realize_choice_winner]
        by_cases kr : k = r
        · subst k
          simp only [mem_choice_owner]
          exact Or.imp xk yk
        · simp only [mem_choice_other _ _ (Ne.symm kr)]
          exact fun h => ⟨h.1.imp xk yk, xn kr h.2.1, yn kr h.2.2⟩
      · rw [realize_choice_winner, realize_choice_winner]
        simp only [ne_eq, choice_eq_owner_iff, not_or]
        exact fun kr h => ⟨xn kr h.1, yn kr h.2⟩
    · by_cases hit : k ∈ ((choiceTerm d x y).realize v).val
      · rcases choice_subset_union d _ _ hit with hx | hy
        · exact ⟨u, .left same xu, fun _ => xk hx, fun kr _ => nonatom_of_mem kr (xk hx)⟩
        · exact ⟨w, .right same yw, fun _ => yk hy, fun kr _ => nonatom_of_mem kr (yk hy)⟩
      · by_cases hx : x.realize v = WinnerSet.singleton r
        · refine ⟨w, .right same yw, fun h => (hit h).elim, fun kr h => yn kr ?_⟩
          intro hy
          exact h ((choice_eq_other_iff _ _ _ same).mpr ⟨hx, hy⟩)
        · exact ⟨u, .left same xu, fun h => (hit h).elim, fun kr _ => xn kr hx⟩

/-- The restriction on the support tested for the requested winner. -/
def eligible (r k : Role) (v : V → WinnerSet Role) : Set V :=
  {i | k = r ∨ v i ≠ singleton r}

/-- An individual winner is attainable under all budgets if and only if the
greatest safe support on the eligible inputs contains a source of it. -/
theorem winner_iff [Fintype V] (b : Row → Budget Role V) (r : Role)
    (mono : SingleAbsorber b r) (k : Role) (v : V → WinnerSet Role) :
    (∃ t : CoreTerm Role V, Satisfies b t ∧ k ∈ (t.realize v).val) ↔
      ∃ i ∈ greatestSupport b r (eligible r k v), k ∈ (v i).val := by
  classical
  constructor
  · rintro ⟨t, bounded, win⟩
    obtain ⟨p, pr, retains, _⟩ := prune_winner r k v t
    have hp := retains win
    have safe := pr.satisfies mono bounded
    obtain ⟨S, _, _, whereBound⟩ := pr.ownedFold.support
    have safeS : SafeSupport b r (S : Set V) := fun z => (whereBound _ _).mp (safe z)
    let without : Set Role := {q | q ≠ k}
    have no : ¬ ((p.realize v).val ⊆ without) := fun hh => hh hp rfl
    have alternatives := mt (whereBound v without).mpr no
    have source : ∃ i ∈ S, k ∈ (v i).val := by
      by_contra! missed
      apply alternatives (Or.inl ?_)
      intro i hi q hq e
      exact missed i hi (e ▸ hq)
    have valid : (S : Set V) ⊆ eligible r k v := by
      intro i hi
      by_cases kr : k = r
      · exact Or.inl kr
      · exact Or.inr (fun atom => alternatives (Or.inr ⟨Ne.symm kr, i, hi, atom⟩))
    obtain ⟨i, si, ki⟩ := source
    exact ⟨i, safeSupport_le_greatest b r safeS valid si, ki⟩
  · rintro ⟨i, usable, ki⟩
    let S := (greatestSupport b r (eligible r k v)).toFinset
    have mem : i ∈ S := Set.mem_toFinset.mpr usable
    obtain ⟨t, bits, bounded⟩ := exists_fold_support (Row := Row) r S ⟨i, mem⟩
    have own : profile r (fun j => decide (j = i)) t = true := by
      apply (bits r _).mpr
      simp only [ite_true, decide_eq_true_eq]
      exact ⟨i, mem, rfl⟩
    have safe : SafeSupport b r (S : Set V) := by
      simpa only [S, Set.coe_toFinset] using greatestSupport_safe b r (eligible r k v)
    refine ⟨t, bounded b safe, ?_⟩
    rcases eq_singleton_or_subset_of_profile_singleton t r i v own with atom | carries
    · by_cases kr : k = r
      · rw [atom, kr]; rfl
      · have flags := (winnerSet_eq_singleton_iff_profile t r v).mp atom
        obtain ⟨j, hj, hflag⟩ : ∃ j ∈ S, v j = singleton r := by
          simpa only [ite_true, decide_eq_true_eq] using (bits r _).mp flags
        have ok := greatestSupport_subset b r (eligible r k v) (Set.mem_toFinset.mp hj)
        exact (ok.elim kr (fun no => no hflag)).elim
    · exact carries ki

omit [DecidableEq Role] in
private theorem mem_union_list (three : Fin 3 ↪ Role) (base : CoreTerm Role V)
    (xs : List (CoreTerm Role V)) (v : V → WinnerSet Role) (k : Role) :
    k ∈ ((xs.foldr (unionTerm three) base).realize v).val ↔
      k ∈ (base.realize v).val ∨ ∃ t ∈ xs, k ∈ (t.realize v).val := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldr_cons, realize_union_winner, val_union, Set.mem_union, ih,
      List.mem_cons, exists_eq_or_imp]
    tauto

/-- One bounded term realizes all the computed winners at once. -/
theorem exists_envelope [Fintype Role] [Fintype V] (three : Fin 3 ↪ Role)
    (b : Row → Budget Role V) (r : Role) (mono : SingleAbsorber b r)
    (nonempty : ∃ t, Satisfies b t) :
    ∃ t : CoreTerm Role V, Satisfies b t ∧ ∀ v k, k ∈ (t.realize v).val ↔
      ∃ i ∈ greatestSupport b r (eligible r k v), k ∈ (v i).val := by
  classical
  obtain ⟨base, hb⟩ := nonempty
  let _ : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let I := (V → WinnerSet Role) × Role
  have pick (j : I) : ∃ t : CoreTerm Role V, Satisfies b t ∧
      ((∃ i ∈ greatestSupport b r (eligible r j.2 j.1), j.2 ∈ (j.1 i).val) →
       j.2 ∈ (t.realize j.1).val) := by
    by_cases yes : ∃ i ∈ greatestSupport b r (eligible r j.2 j.1), j.2 ∈ (j.1 i).val
    · obtain ⟨t, ht, win⟩ := (winner_iff b r mono j.2 j.1).mpr yes
      exact ⟨t, ht, fun _ => win⟩
    · exact ⟨base, hb, fun h => (yes h).elim⟩
  choose f good marked using pick
  let xs := Finset.univ.toList.map f
  let t := xs.foldr (unionTerm three) base
  have bound : Satisfies b t := by
    intro z k hk
    rcases (mem_union_list three base xs _ k).mp hk with h | ⟨w, mem, hit⟩
    · exact hb z h
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp mem
      exact good j z hit
  refine ⟨t, bound, fun v k => ⟨fun h => (winner_iff b r mono k v).mp ⟨t, bound, h⟩, ?_⟩⟩
  intro h
  exact (mem_union_list three base xs v k).mpr (Or.inr ⟨f (v, k),
    List.mem_map.mpr ⟨(v, k), by simp, rfl⟩, marked (v, k) h⟩)

/-- Remove every input that violates a row with no possible absorbing
input left in the pool. -/
noncomputable def sweep (b : Row → Budget Role V) (r : Role) (pool : Finset V) : Finset V := by
  classical
  exact pool.filter fun i => ∀ z, ((b z).values i).val ⊆ (b z).allowed ∨
    (r ∈ (b z).allowed ∧ ∃ j ∈ pool, (b z).values j = singleton r)

noncomputable def sweeps (b : Row → Budget Role V) (r : Role) :
    ℕ → Finset V → Finset V
  | 0, pool => pool
  | n + 1, pool => sweeps b r n (sweep b r pool)

omit [DecidableEq Role] in
private theorem survive (b : Row → Budget Role V) (r : Role) (S : Set V) (pool : Finset V)
    (sub : S ⊆ (pool : Set V)) (safe : SafeSupport b r S) : S ⊆ (sweep b r pool : Set V) := by
  classical
  intro i hi
  refine Finset.mem_filter.mpr ⟨sub hi, fun z => ?_⟩
  rcases safe z with all | ⟨ok, j, sj, atom⟩
  · exact Or.inl (all i hi)
  · exact Or.inr ⟨ok, j, sub sj, atom⟩

omit [DecidableEq Role] in
private theorem safe_of_fixed (b : Row → Budget Role V) (r : Role) (pool : Finset V)
    (fixed : sweep b r pool = pool) : SafeSupport b r (pool : Set V) := by
  classical
  intro z
  by_cases hit : r ∈ (b z).allowed ∧ ∃ j ∈ pool, (b z).values j = singleton r
  · exact Or.inr hit
  · exact Or.inl (fun i hi => ((Finset.mem_filter.mp
      (show i ∈ sweep b r pool by rw [fixed]; exact hi)).2 z).resolve_right hit)

omit [DecidableEq Role] in
private theorem sweeps_fixed (b : Row → Budget Role V) (r : Role) (pool : Finset V)
    (fixed : sweep b r pool = pool) (k : ℕ) : sweeps b r k pool = pool := by
  induction k with
  | zero => rfl
  | succ _ ih => simpa only [sweeps, fixed] using ih

omit [DecidableEq Role] in
/-- At most one sweep per eligible input computes the greatest safe support. -/
theorem sweeps_eq_greatest (b : Row → Budget Role V) (r : Role) (k : ℕ) (pool : Finset V)
    (fuel : pool.card ≤ k) : (sweeps b r k pool : Set V) = greatestSupport b r pool := by
  classical
  have sub : sweep b r pool ⊆ pool := Finset.filter_subset _ _
  by_cases fixed : sweep b r pool = pool
  · rw [sweeps_fixed b r pool fixed k]
    exact Set.Subset.antisymm (safeSupport_le_greatest b r (safe_of_fixed b r pool fixed) Set.Subset.rfl)
      (greatestSupport_subset b r _)
  · have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, fixed⟩)
    cases k with
    | zero => omega
    | succ k =>
      rw [sweeps, sweeps_eq_greatest b r k (sweep b r pool) (by omega)]
      exact Set.Subset.antisymm
        (safeSupport_le_greatest b r (greatestSupport_safe b r _)
          (Set.Subset.trans (greatestSupport_subset b r _) sub))
        (safeSupport_le_greatest b r (greatestSupport_safe b r _) (survive b r _ pool
          (greatestSupport_subset b r _) (greatestSupport_safe b r _)))
termination_by k

/-- Keep the selector in the output and suppress the other operand precisely
when the selector is the designated singleton. -/
noncomputable def mask (r : Role) (y z : WinnerSet Role) : WinnerSet Role :=
  y.union (choice r y z)

omit [DecidableEq Role] in
theorem mask_eq (r : Role) (y z : WinnerSet Role) :
    mask r y z = if y = singleton r then y else y.union z := by
  classical
  by_cases hm : y = singleton r
  · subst y
    simp [mask, choice]
  · by_cases hz : z = singleton r
    · simp [mask, choice, hm, hz]
    · apply Subtype.ext
      simp [mask, choice, hm, hz]

/-- The two group envelopes switched by a single selector. At other
selector menus both envelopes contribute. -/
noncomputable def select (a b : Role) (y A B : WinnerSet Role) : WinnerSet Role :=
  (mask b y A).union (mask a y B)

omit [DecidableEq Role] in
theorem select_eq (a b : Role) (ne : a ≠ b) (y A B : WinnerSet Role) :
    select a b y A B =
      if y = singleton a then y.union A else if y = singleton b then y.union B
      else y.union (A.union B) := by
  classical
  apply Subtype.ext
  by_cases ya : y = singleton a
  · simp [select, mask_eq, ya, ne, val_union, Set.union_comm]
  · by_cases yb : y = singleton b
    · simp [select, mask_eq, yb, Ne.symm ne, val_union, Set.union_comm]
    · simp only [select, mask_eq, ite_eq_right ya, ite_eq_right yb, val_union]
      ext k
      simp only [Set.mem_union]
      tauto

/-- The selector switch as a single core word. -/
def selectWord (three : Fin 3 ↪ Role) (a b : Role)
    (y A B : CoreTerm Role V) : CoreTerm Role V :=
  let guard (r : Role) (x : CoreTerm Role V) := unionTerm three y (choiceTerm r y x)
  unionTerm three (guard b A) (guard a B)

omit [DecidableEq Role] in
theorem realize_selectWord (three : Fin 3 ↪ Role) (a b : Role)
    (y A B : CoreTerm Role V) (v : V → WinnerSet Role) :
    (selectWord three a b y A B).realize v =
      select a b (y.realize v) (A.realize v) (B.realize v) := by
  simp only [selectWord, select, mask, realize_union_winner, realize_choice_winner]

end KFOL.Core.OneOwnerSelector
