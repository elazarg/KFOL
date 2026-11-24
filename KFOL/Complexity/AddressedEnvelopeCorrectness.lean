module

public import KFOL.Complexity.AddressedEnvelope
public import KFOL.Complexity.FullSparseSemantics
public import KFOL.Core.AddressedRecognition

/-! # Correctness of the polynomial-time addressed group machine -/

@[expose] public section
namespace KFOL.Complexity.AddressedEnvelope

open Core Core.ProfileBudgets Core.AddressedRectangle Core.AddressedLogicalGroups
open Core.AddressedRails WinnerSet
attribute [local instance] Equational.coreStructure

variable {L Row Role Track Bit : Type*}

/-- Every listed name represents a member of the set, and every member
occurs. Names may repeat. -/
def Lists (ids : L ↪ ℕ) (names : Names) (S : Set L) : Prop :=
  ∀ j, j ∈ names ↔ ∃ i ∈ S, ids i = j

theorem Lists.lookup {ids : L ↪ ℕ} {names : Names} {S : Set L}
    (listed : Lists ids names S) (i : L) : ids i ∈ names ↔ i ∈ S := by
  rw [listed]
  exact ⟨fun ⟨j,hj,eq⟩ => ids.injective eq ▸ hj, fun h => ⟨i,h,rfl⟩⟩

/-- One posted loss, with the same marked coordinate and posting set
as the corresponding logical row. -/
def RowMatches {B : Book L Track Bit} (ids : L ↪ ℕ) (R : Rows B Row) (z : Row) (p : Entry) : Prop :=
  p.1 = ids (R.mark z) ∧ ∀ f, ids f ∈ p.2 ↔ f ∈ R.posted z

/-- Row orders and repeated copies do not change a presentation. -/
structure RowPresentation {B : Book L Track Bit} (ids : L ↪ ℕ) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (A : L → Bool) (rd : RowData) : Prop where
  endpoint : ∀ f, ids f ∈ rd.1 ↔ A f = true
  sound : ∀ p ∈ rd.2, ∃ z, z ∈ S ∧ R.left z = side ∧ RowMatches ids R z p
  complete : ∀ z ∈ S, R.left z = side → ∃ p ∈ rd.2, RowMatches ids R z p

/-- All menu records are genuine, and each logical input occurs. -/
structure MenuPresentation {K : ℕ} (ids : L ↪ ℕ) (v : L → WinnerSet (Fin K))
    (menus : List Entry) : Prop where
  sound : ∀ p ∈ menus, ∃ f, p.1 = ids f ∧ FullSparseEvaluation.Represents p.2 (v f)
  complete : ∀ f, ∃ p ∈ menus, p.1 = ids f

/-- The columns record the violating inputs and the inputs whose
singleton can absorb the violation. -/
def RuleMatches (ids : L ↪ ℕ) (b : Budget Role L) (r : Role) (p : Rule) : Prop :=
  (∀ i, ids i ∈ p.1 ↔ ¬ (b.values i).val ⊆ b.allowed) ∧
  (∀ i, ids i ∈ p.2 ↔ r ∈ b.allowed ∧ b.values i = singleton r)

structure ListedRows (ids : L ↪ ℕ) (rules : List Rule) (b : Row → Budget Role L) (r : Role) : Prop where
  sound : ∀ u ∈ rules, ∃ z, RuleMatches ids (b z) r u
  complete : ∀ z, ∃ u ∈ rules, RuleMatches ids (b z) r u

private theorem sweep_lists {ids : L ↪ ℕ} {records : List Rule} {b : Row → Budget Role L} {r : Role}
    (rows : ListedRows ids records b r) {pool : Names} {P : Finset L}
    (hs : Lists ids pool P) : Lists ids (sweep records pool) (OneOwnerSelector.sweep b r P) := by
  classical
  have pass (i : L) : records.all (fun u => !member (ids i) u.1 || overlaps u.2 pool) = true ↔
      ∀ z, ((b z).values i).val ⊆ (b z).allowed ∨
        (r ∈ (b z).allowed ∧ ∃ j ∈ P, (b z).values j = singleton r) := by
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      overlaps_iff]
    constructor
    · intro h z
      obtain ⟨u,mem,violates,relieves⟩ := rows.complete z
      rcases h u mem with safe | ⟨n,hn,hp⟩
      · exact Or.inl (by_contra (fun bad => safe ((member_iff _ _).mpr ((violates i).mpr bad))))
      · obtain ⟨j,hj,rfl⟩ := (hs n).mp hp
        obtain ⟨inR,atom⟩ := (relieves j).mp hn
        exact Or.inr ⟨inR,j,hj,atom⟩
    · intro h u hu
      obtain ⟨z,violates,relieves⟩ := rows.sound u hu
      rcases h z with safe | ⟨inR,j,hj,atom⟩
      · exact Or.inl (fun hit => (violates i).mp ((member_iff _ _).mp hit) safe)
      · exact Or.inr ⟨ids j,(relieves j).mpr ⟨inR,atom⟩,(hs.lookup j).mpr hj⟩
  intro n
  rw [sweep, List.mem_filter]
  constructor
  · rintro ⟨hn,good⟩
    obtain ⟨i,hi,rfl⟩ := (hs n).mp hn
    exact ⟨i,Finset.mem_filter.mpr ⟨hi, (pass i).mp good⟩,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨base,good⟩ := Finset.mem_filter.mp hi
    exact ⟨(hs.lookup i).mpr base, (pass i).mpr good⟩

/-- The list loop computes exactly the greatest safe support. The clock is
the number of entries in the initial pool, including any duplicates. -/
theorem survivors_lists {ids : L ↪ ℕ} {records : List Rule} {b : Row → Budget Role L} {r : Role}
    (rows : ListedRows ids records b r) {pool : Names} {P : Finset L} (hs : Lists ids pool P) :
    Lists ids (survivors records pool) (greatestSupport b r P) := by
  classical
  have iter (m : ℕ) (xs : Names) (T : Finset L) (rep : Lists ids xs T) :
      Lists ids ((sweep records)^[m] xs) (OneOwnerSelector.sweeps b r m T) := by
    induction m generalizing xs T with
    | zero => exact rep
    | succ n ih =>
      rw [Function.iterate_succ_apply, OneOwnerSelector.sweeps]
      exact ih _ _ (sweep_lists rows rep)
  have same : P.map ids = pool.toFinset := by
    ext n
    simpa only [Finset.mem_map, Finset.mem_coe, List.mem_toFinset] using (hs n).symm
  have enough : P.card ≤ pool.length :=
    calc P.card = (P.map ids).card := (Finset.card_map ids).symm
      _ = pool.toFinset.card := congrArg Finset.card same
      _ ≤ pool.length := List.toFinset_card_le _
  simpa only [OneOwnerSelector.sweeps_eq_greatest b r _ P enough, survivors] using
    iter pool.length pool P hs

/-- Associate the canonical binary identifier of each logical variable with
its actual menu, and list active losses of the selected orientation. -/
def view (ids : L ↪ ℕ) (labels : List L) (losses : List Row) (mark : Row → L)
    (posted : Row → List L) (A : L → Bool) (value : L → Names) : Data :=
  (((labels.filter A).map ids, losses.map (fun z => (ids (mark z), (posted z).map ids))),
    labels.map (fun f => (ids f, value f)))

private theorem source_rep {K : ℕ} {val : Names} {v : WinnerSet (Fin K)}
    (rep : FullSparseEvaluation.Represents val v) (k : Fin K) : k.val ∈ val ↔ k ∈ v.val := by
  change k.val ∈ FullSparseEvaluation.asSet val ↔ _
  rw [rep]
  exact ⟨fun ⟨j,hj,e⟩ => (Fin.ext e) ▸ hj, fun h => ⟨k,h,rfl⟩⟩

private theorem MenuPresentation.value {K : ℕ} {ids : L ↪ ℕ} {v : L → WinnerSet (Fin K)}
    {menus : List Entry} (hm : MenuPresentation ids v menus) (f : L) :
    ∃ m, (ids f,m) ∈ menus ∧ FullSparseEvaluation.Represents m (v f) := by
  obtain ⟨⟨n,m⟩,mem,e⟩ := hm.complete f
  obtain ⟨g,tag,rep⟩ := hm.sound _ mem
  obtain rfl : g = f := ids.injective (tag.symm.trans e)
  exact ⟨m,e ▸ mem,rep⟩

private theorem eligible_iff {K : ℕ} (r k : Fin K) {m : Names} {v : WinnerSet (Fin K)}
    (rep : FullSparseEvaluation.Represents m v) :
    eligible (r.val,k.val) m = true ↔ k = r ∨ v ≠ WinnerSet.singleton r := by
  rw [eligible, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
  simp only [decide_eq_true_eq, Fin.val_inj]
  rw [eq_comm (a := r)]
  exact or_congr_right (not_congr (FullSparseEvaluation.singletonB_represents_iff r rep))

private theorem pool_presented {K : ℕ} (r k : Fin K) {ids : L ↪ ℕ} {data : Data}
    {v : L → WinnerSet (Fin K)} (hm : MenuPresentation ids v data.2) :
    Lists ids (pool ((r.val,k.val),data)) (OneOwnerSelector.eligible r k v) := by
  intro n
  simp only [pool, List.mem_map, List.mem_filter, Prod.exists]
  constructor
  · rintro ⟨_,m,⟨mem,good⟩,rfl⟩
    obtain ⟨f,eq,rep⟩ := hm.sound _ mem
    exact ⟨f,(eligible_iff r k rep).mp good,eq.symm⟩
  · rintro ⟨f,ok,rfl⟩
    obtain ⟨m, mem, rep⟩ := hm.value f
    exact ⟨ids f,m,⟨mem,(eligible_iff r k rep).mpr ok⟩,rfl⟩

private theorem sources_presented {K : ℕ} (r k : Fin K) {ids : L ↪ ℕ} {data : Data}
    {v : L → WinnerSet (Fin K)} (hm : MenuPresentation ids v data.2) :
    Lists ids (sources ((r.val,k.val),data)) {f | k ∈ (v f).val} := by
  intro n
  simp only [sources, List.mem_map, List.mem_filter, Prod.exists, member_iff]
  constructor
  · rintro ⟨_,m,⟨mem,hit⟩,rfl⟩
    obtain ⟨f,eq,rep⟩ := hm.sound _ mem
    exact ⟨f,(source_rep rep k).mp hit,eq.symm⟩
  · rintro ⟨f,hf,rfl⟩
    obtain ⟨m,mem,rep⟩ := hm.value f
    exact ⟨ids f,m,⟨mem,(source_rep rep k).mpr hf⟩,rfl⟩

private theorem input_violates {r : Role} {m : WinnerSet Role} :
    (¬ m.val ⊆ {s | s ≠ r}) ↔ r ∈ m.val := by
  constructor
  · intro bad
    by_contra miss
    apply bad
    intro k hk e
    exact miss (e ▸ hk)
  · exact fun hit ok => ok hit rfl

private theorem endpoint_atom [DecidableEq Role] (three : Fin 3 ↪ Role) (r : Role) (A : L → Bool)
    (i : L) : endpointValues three r A i = WinnerSet.singleton r ↔ A i = true := by
  rw [← congrFun (endpoint_flags three r A) i, decide_eq_true_eq]

private theorem row_atom [DecidableEq Role] {B : Book L Track Bit} (three : Fin 3 ↪ Role)
    (R : Rows B Row) (side : Bool) (z : Row) (s : R.left z = side) (i : L) :
    rawValues three R z i = WinnerSet.singleton (orient three side 0) ↔ i ∈ R.posted z := by
  classical
  subst side
  exact (MonochromaticCutObstruction.pure_atom three (three 2) (.var i) (R.mark z)
    (orient three (R.left z) 0) _ _ (fun f => decide (f ∈ R.posted z))
    (decide_eq_false (mark_off R z)) (primary_ne_aux three _)).trans (by simp [profile_var])

private theorem listed_rules {K : ℕ} {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (A : L → Bool)
    (ids : L ↪ ℕ) (data : Data) (v : L → WinnerSet (Fin K))
    (rd : RowPresentation ids R S side A data.1) (hm : MenuPresentation ids v data.2) :
    ListedRows ids (rules data) (bounds three R S side A) (orient three side 0) := by
  classical
  let r := orient three side 0
  let ep : Rule := ((data.2.map Prod.fst).filter (fun f => !member f data.1.1), data.1.1)
  let code (p : Entry) : Rule := ([p.1],p.2)
  have base : RuleMatches ids (bounds three R S side A none) r ep := by
    constructor
    · intro f
      have present : ids f ∈ data.2.map Prod.fst := by
        obtain ⟨p,hp,tag⟩ := hm.complete f
        exact List.mem_map.mpr ⟨p,hp,tag⟩
      change ids f ∈ (data.2.map Prod.fst).filter (fun j => !member j data.1.1) ↔ ¬ (endpointValues three r A f).val ⊆ {r}
      simp only [List.mem_filter, present, true_and, Bool.not_eq_true', Bool.eq_false_iff]
      apply not_congr
      exact ((member_iff _ _).trans (rd.endpoint f)).trans
        ((endpoint_atom three r A f).symm.trans ⟨fun h => by rw [h]; rfl, eq_singleton_of_subset _ _⟩)
    · intro f
      change ids f ∈ data.1.1 ↔ r ∈ {r} ∧ endpointValues three r A f = _
      simpa only [Set.mem_singleton_iff, true_and, endpoint_atom] using rd.endpoint f
  have loss (z : Row) (hz : z ∈ S ∧ R.left z = side) (p : Entry) (matchRow : RowMatches ids R z p) :
      RuleMatches ids (bounds three R S side A (some ⟨z,hz⟩)) r (code p) := by
    constructor
    · intro f
      change ids f ∈ [p.1] ↔ ¬ (rawValues three R z f).val ⊆ {s | s ≠ three 2}
      rw [input_violates,List.mem_singleton,matchRow.1]
      exact ids.injective.eq_iff.trans (Sources.mem_probe_iff _ _ _ _ _).symm
    · intro f
      change ids f ∈ p.2 ↔ r ≠ three 2 ∧ rawValues three R z f = _
      rw [row_atom three R side z hz.2, and_iff_right (primary_ne_aux three _)]
      exact matchRow.2 f
  change ListedRows ids (ep :: data.1.2.map code) _ _
  constructor
  · intro u hu
    rcases List.mem_cons.mp hu with eq | listed
    · exact ⟨none,eq ▸ base⟩
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp listed
      obtain ⟨z,hz,sidez,matchRow⟩ := rd.sound p hp
      exact ⟨some ⟨z,hz,sidez⟩,loss z ⟨hz,sidez⟩ p matchRow⟩
  · rintro (_ | ⟨z,hz⟩)
    · exact ⟨ep,List.mem_cons_self,base⟩
    · obtain ⟨p,hp,matchRow⟩ := rd.complete z hz.1 hz.2
      exact ⟨code p,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩),loss z hz p matchRow⟩

theorem evaluate_presented_good [Fintype L] {K : ℕ} {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (A : L → Bool) (k : Fin K)
    (ids : L ↪ ℕ) (data : Data) (v : L → WinnerSet (Fin K))
    (rd : RowPresentation ids R S side A data.1) (hm : MenuPresentation ids v data.2) :
    evaluate (((orient three side 0).val,k.val), data) = true ↔
      ∃ t : CoreTerm (Fin K) L, Good three R S side A t ∧ k ∈ (t.realize v).val := by
  classical
  let r := orient three side 0
  let b := bounds three R S side A
  let D := OneOwnerSelector.eligible r k v
  have ls : Lists ids (pool ((r.val,k.val),data)) (D.toFinset : Set L) := by
    simpa only [Set.coe_toFinset] using pool_presented r k hm
  have lv := survivors_lists (listed_rules three R S side A ids data v rd hm) ls
  rw [Set.coe_toFinset] at lv
  have src := sources_presented r k hm
  have spec := OneOwnerSelector.winner_iff b r (bounds_single three R S side A) k v
  simp only [satisfies_iff, b] at spec
  rw [spec, evaluate, overlaps_iff]
  constructor
  · rintro ⟨j,hj,hk⟩
    obtain ⟨i, hi, rfl⟩ := (lv j).mp hj
    exact ⟨i,hi,(src.lookup i).mp hk⟩
  · rintro ⟨i,hi,hk⟩
    exact ⟨ids i,(lv.lookup i).mpr hi,(src.lookup i).mpr hk⟩

/-- On a faithful listing of the chosen side's active rows, the machine's
answer is exactly the existence of a bounded logical word carrying the
requested owner at the supplied menu valuation. -/
theorem evaluate_iff_good [Fintype L] {K : ℕ} {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (A : L → Bool) (k : Fin K)
    (ids : L ↪ ℕ) (labels : List L) (cover : ∀ f, f ∈ labels)
    (losses : List Row) (listed : ∀ z, z ∈ losses ↔ z ∈ S ∧ R.left z = side)
    (posted : Row → List L) (posts : ∀ z f, f ∈ posted z ↔ f ∈ R.posted z)
    (value : L → Names) (v : L → WinnerSet (Fin K))
    (rep : ∀ f, FullSparseEvaluation.Represents (value f) (v f)) :
    evaluate (((orient three side 0).val,k.val), view ids labels losses R.mark posted A value) = true ↔
      ∃ t : CoreTerm (Fin K) L, Good three R S side A t ∧ k ∈ (t.realize v).val := by
  apply evaluate_presented_good three R S side A k ids _ v
  · constructor
    · intro f
      simp [view,cover]
    · intro p hp
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      exact ⟨z,((listed z).mp hz).1,((listed z).mp hz).2,rfl,fun f => by simpa using posts z f⟩
    · intro z hz sidez
      refine ⟨_,List.mem_map.mpr ⟨z,(listed z).mpr ⟨hz,sidez⟩,rfl⟩,rfl,fun f => ?_⟩
      simpa using posts z f
  · constructor
    · intro p hp
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hp
      exact ⟨f,rfl,rep f⟩
    · intro f
      exact ⟨_,List.mem_map.mpr ⟨f,cover f,rfl⟩,rfl⟩

open Core.AddressedRecognition Core.AddressedPadding

theorem evaluate_presented_group [Fintype L] {K : ℕ} {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (x y : L → Bool) (k : Fin K)
    (ids : L ⊕ Bool ↪ ℕ) (data : Data) (v : L ⊕ Bool → WinnerSet (Fin K))
    (rd : RowPresentation ids (extendRows R) S side (sideEndpoint side x y) data.1)
    (hm : MenuPresentation ids v data.2) :
    evaluate (((orient three side 0).val,k.val), data) = true ↔
      k ∈ ((group three R S side x y).realize v).val := by
  rw [evaluate_presented_good three (extendRows R) S side _ k ids data v rd hm]
  have env := group_spec three R S side x y
  exact ⟨fun ⟨t,ht,hit⟩ => env.2 t ht v hit, fun hit => ⟨_,env.1,hit⟩⟩

/-- The list machine computes exactly an entry of the concrete group used
in the addressed recognition table, for either orientation. -/
theorem evaluate_iff_group [Fintype L] {K : ℕ} {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (x y : L → Bool) (k : Fin K)
    (ids : L ⊕ Bool ↪ ℕ) (labels : List (L ⊕ Bool)) (cover : ∀ f, f ∈ labels)
    (losses : List Row) (listed : ∀ z, z ∈ losses ↔ z ∈ S ∧ R.left z = side)
    (posted : Row → List (L ⊕ Bool)) (posts : ∀ z f, f ∈ posted z ↔ f ∈ (extendRows R).posted z)
    (value : L ⊕ Bool → Names) (v : L ⊕ Bool → WinnerSet (Fin K))
    (rep : ∀ f, FullSparseEvaluation.Represents (value f) (v f)) :
    evaluate (((orient three side 0).val,k.val), view ids labels losses (extendRows R).mark posted
      (sideEndpoint side x y) value) = true ↔ k ∈ ((group three R S side x y).realize v).val := by
  rw [evaluate_iff_good three (extendRows R) S side _ k ids labels cover losses listed posted posts value v rep]
  have env := group_spec three R S side x y
  exact ⟨fun ⟨t,ht,hit⟩ => env.2 t ht v hit, fun hit => ⟨_,env.1, hit⟩⟩

end KFOL.Complexity.AddressedEnvelope
