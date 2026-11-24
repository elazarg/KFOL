module

public import KFOL.Complexity.AddressedPoint
public import KFOL.Complexity.AddressedEnvelopeCorrectness

/-! # Correctness of the addressed point evaluator -/

@[expose] public section
namespace KFOL.Complexity.AddressedPoint

open AddressedEnvelope FullSparseEvaluation Core.AddressedRails Core.AddressedRectangle
open Core.AddressedPadding Core.AddressedLogicalGroups Core.AddressedRecognition
open Core.AddressedTableExtraction Core.ProfileBudgets
attribute [local instance] Equational.coreStructure

variable {L Track Bit Row : Type*} {K : ℕ}

/-- Codes may repeat. Each listed label has exactly the rails of its address,
and every logical label occurs at least once. -/
structure CodePresentation (ids : L ↪ ℕ) (B : Book L Track Bit) (coord : Rail Track Bit → ℕ)
    (codes : Codes) : Prop where
  sound : ∀ p ∈ codes, ∃ f, p.1 = ids f ∧ ∀ j, j ∈ p.2 ↔ ∃ i, coord (B.rail f i) = j
  complete : ∀ f, ∃ p ∈ codes, p.1 = ids f

theorem represents_ext {xs : Names} {w : WinnerSet (Fin K)}
    (valid : ∀ j ∈ xs, j < K) (mem : ∀ r : Fin K, r.val ∈ xs ↔ r ∈ w.val) : Represents xs w := by
  ext j
  constructor
  · intro hj
    exact ⟨⟨j,valid j hj⟩,(mem _).mp hj,rfl⟩
  · rintro ⟨r,hw,rfl⟩
    exact (mem r).mpr hw

theorem represents_mem {xs : Names} {w : WinnerSet (Fin K)} (rep : Represents xs w) (r : Fin K) :
    r.val ∈ xs ↔ r ∈ w.val := by
  change r.val ∈ asSet xs ↔ _
  rw [rep]
  exact Fin.val_injective.mem_set_image

theorem represents_lt {xs : Names} {w : WinnerSet (Fin K)} (rep : Represents xs w)
    {n : ℕ} (mem : n ∈ xs) : n < K := by
  have h : n ∈ Fin.val '' w.val := rep ▸ mem
  obtain ⟨r,_,rfl⟩ := h
  exact r.isLt

theorem normalize_represents {xs : Names} {w : WinnerSet (Fin K)} (h : Represents xs w) :
    Represents (normalize K xs) w := by
  apply represents_ext
  · intro j hj
    exact List.mem_range.mp (List.mem_filter.mp hj).1
  · intro r
    simpa only [normalize,List.mem_filter,List.mem_range,r.isLt,true_and,member_iff] using represents_mem h r

variable [Fintype Bit] [Nonempty Bit]

/-- Address-fold evaluation permits duplicate or reordered physical positions. -/
theorem helper_represents (c : Fin K) (B : Book L Track Bit) (coord : Rail Track Bit → ℕ)
    (v : Menus) (x : Rail Track Bit → WinnerSet (Fin K))
    (input : ∀ u, Represents (v.getD (coord u) []) (x u)) (f : L) (addr : Names)
    (listed : ∀ j, j ∈ addr ↔ ∃ i, coord (B.rail f i) = j) :
    Represents (helper c.val v addr) (B.read c x f) := by
  classical
  let vals := addr.map fun j => v.getD j []
  have vals_mem (m : Names) : m ∈ vals ↔ ∃ i, v.getD (coord (B.rail f i)) [] = m := by
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,rfl⟩ := (listed j).mp hj
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact List.mem_map.mpr ⟨_,(listed _).mpr ⟨i,rfl⟩,rfl⟩
  have hit : vals.any (singletonB c.val) = true ↔ B.read c x f = WinnerSet.singleton c := by
    rw [List.any_eq_true,B.read_aux]
    constructor
    · rintro ⟨m,hm,atom⟩
      obtain ⟨i,rfl⟩ := (vals_mem m).mp hm
      exact ⟨i,(singletonB_represents_iff c (input _)).mp atom⟩
    · rintro ⟨i,atom⟩
      exact ⟨_,(vals_mem _).mpr ⟨i,rfl⟩,(singletonB_represents_iff c (input _)).mpr atom⟩
  change Represents (if vals.any (singletonB c.val) then [c.val] else vals.flatten) _
  by_cases atom : B.read c x f = WinnerSet.singleton c
  · rw [ite_eq_left (hit.mpr atom),atom]
    exact represents_singleton c
  · rw [ite_eq_right (fun h => atom (hit.mp h))]
    have clear : ∀ i, x (B.rail f i) ≠ WinnerSet.singleton c := fun i h => atom ((B.read_aux c x f).mpr ⟨i,h⟩)
    apply represents_ext
    · intro j hj
      obtain ⟨m,hm,hj⟩ := List.mem_flatten.mp hj
      obtain ⟨i,rfl⟩ := (vals_mem m).mp hm
      exact represents_lt (input _) hj
    · intro r
      rw [List.mem_flatten]
      have fold := WinnerSet.mem_choiceFold_of_no_owner c Finset.univ Finset.univ_nonempty
        (fun i => x (B.rail f i)) (fun i _ => clear i) r
      rw [Book.read,fold]
      simp only [Finset.mem_univ,true_and]
      constructor
      · rintro ⟨m,hm,hj⟩
        obtain ⟨i,rfl⟩ := (vals_mem m).mp hm
        exact ⟨i,(represents_mem (input _) r).mp hj⟩
      · rintro ⟨i,hi⟩
        exact ⟨_,(vals_mem _).mpr ⟨i,rfl⟩,(represents_mem (input _) r).mpr hi⟩

theorem logical_presentation (c : Fin K) {B : Book L Track Bit} {coord : Rail Track Bit → ℕ}
    {ids : L ↪ ℕ} {codes : Codes} (present : CodePresentation ids B coord codes)
    (v : Menus) (x : Rail Track Bit → WinnerSet (Fin K))
    (input : ∀ u, Represents (v.getD (coord u) []) (x u)) :
    MenuPresentation ids (B.read c x) (logical c.val codes v) := by
  constructor
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨f,idf,rails⟩ := present.sound q hq
    exact ⟨f,idf,helper_represents c B coord v x input f q.2 rails⟩
  · intro f
    obtain ⟨q,hq,idf⟩ := present.complete f
    exact ⟨_,List.mem_map.mpr ⟨q,hq,rfl⟩,idf⟩

omit [Fintype Bit] [Nonempty Bit] in
theorem group_represents [Fintype L] {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (x y : L → Bool) (ids : L ⊕ Bool ↪ ℕ)
    (rows : RowData) (values : List Entry) (v : L ⊕ Bool → WinnerSet (Fin K))
    (rd : RowPresentation ids (extendRows R) S side (sideEndpoint side x y) rows)
    (hm : MenuPresentation ids v values) :
    Represents (group K (Core.AddressedRectangle.orient three side 0).val rows values)
      ((Core.AddressedRecognition.group three R S side x y).realize v) := by
  apply represents_ext
  · intro j hj
    exact List.mem_range.mp (List.mem_filter.mp hj).1
  · intro r
    simpa only [group,List.mem_filter,List.mem_range,r.isLt,true_and] using
      evaluate_presented_group three R S side x y r ids (rows,values) v rd hm

theorem point_represents [Fintype L] {B : Book L Track Bit} (three : Fin 3 ↪ Fin K)
    (R : Rows B Row) (S : Finset Row) (x y : L → Bool) (ids : L ⊕ Bool ↪ ℕ)
    (coord : Rail (Track ⊕ Bool) Bit → ℕ) (layout : Layout)
    (codes : CodePresentation ids (extendBook B) coord layout.1)
    (left : RowPresentation ids (extendRows R) S true (sideEndpoint true x y) layout.2.1)
    (right : RowPresentation ids (extendRows R) S false (sideEndpoint false x y) layout.2.2)
    (v : Menus) (w : Option (Rail (Track ⊕ Bool) Bit) → WinnerSet (Fin K))
    (selector : Represents (v.getD 0 []) (w none))
    (rail : ∀ u, Represents (v.getD (coord u) []) (w (some u))) :
    Represents (point K (three 0).val (three 1).val (three 2).val layout v)
      (table three R S x y w) := by
  classical
  let B' := extendBook B
  let c := three 2
  let vals := logical c.val layout.1 v
  let read := B'.read c (fun u => w (some u))
  have menus : MenuPresentation ids read vals := logical_presentation c codes v _ rail
  have cap_hit : vals.all (fun p => singletonB c.val p.2) = true ↔
      cap B' (fun u => decide (w (some u) = WinnerSet.singleton c)) = true := by
    simp only [List.all_eq_true,cap,decide_eq_true_eq]
    constructor
    · intro every f
      obtain ⟨p,hp,hid⟩ := menus.complete f
      obtain ⟨g,hg,hv⟩ := menus.sound p hp
      have eq : g = f := ids.injective (hg.symm.trans hid)
      subst g
      obtain ⟨i,hi⟩ := (B'.read_aux c _ f).mp ((singletonB_represents_iff c hv).mp (every p hp))
      exact ⟨i,hi⟩
    · intro all p hp
      obtain ⟨f,_,hv⟩ := menus.sound p hp
      obtain ⟨i,hi⟩ := all f
      exact (singletonB_represents_iff c hv).mpr ((B'.read_aux c _ f).mpr ⟨i,hi⟩)
  have hl := group_represents three R S true x y ids layout.2.1 vals read left menus
  have hr := group_represents three R S false x y ids layout.2.2 vals read right menus
  change Represents (if vals.all (fun p => singletonB c.val p.2) then [c.val] else _)
    (if cap B' _ then WinnerSet.singleton c else _)
  by_cases capOn : cap B' (fun u => decide (w (some u) = WinnerSet.singleton c)) = true
  · rw [ite_eq_left capOn,ite_eq_left (cap_hit.mpr capOn)]
    exact represents_singleton c
  · rw [ite_eq_right capOn, ite_eq_right (fun h => capOn (cap_hit.mp h))]
    apply normalize_represents
    exact represents_union (represents_union selector (represents_choice (three 1) selector hl))
      (represents_union selector (represents_choice (three 0) selector hr))

end KFOL.Complexity.AddressedPoint
