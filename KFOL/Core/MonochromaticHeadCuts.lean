module

public import KFOL.Core.MonochromaticLosses
public import KFOL.Core.AcyclicSourceQueries
public import Mathlib.Order.Extension.Linear

/-! # Safe fold deletion and monochromatic cycles of negative observations

With one row per head, a safe word exists exactly when the postings of
some owner contain a directed cycle. Each word omitting all rows contains
such a cycle on its own inputs.
-/

@[expose] public section

namespace KFOL.Core.Sources

open ProfileBudgets AcyclicSourceQueries

universe u v w
variable {Role : Type u} {Var : Type v} {Row : Type w}
attribute [local instance] Equational.coreStructure

private theorem posting_ne_observer (q : ProbeIndex Role Var) (j : Var) :
    posting q j ≠ some q.1 := by
  classical
  by_cases hj : j ≠ q.2.1
  · cases he : q.2.2 ⟨j,hj⟩ with
    | neutral => simp [posting,hj,he,Passive.color]
    | atom a => simpa [posting,hj,he,Passive.color] using a.property
  · simp [posting,hj]

private theorem probeAt_eq_atom_iff_posted (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var)
    (j : Var) {r : Role} (ne : r ≠ q.1) :
    probeAt three q j = WinnerSet.singleton r ↔ posting q j = some r := by
  classical
  by_cases hj : j = q.2.1
  · subst j
    simp [probeAt,posting,WinnerSet.singleton_inj,Ne.symm ne]
  · rw [probeAt,probe_other three q.1 q.2.1 q.2.2 j hj,
      representative_atom_iff three q.1 _ ⟨r,ne⟩]
    cases he : q.2.2 ⟨j,hj⟩ with
    | neutral => simp [posting,hj,he,Passive.color]
    | atom a => simp [posting,hj,he,Passive.color,Subtype.ext_iff]

variable [DecidableEq Role]

/-- Exact effect on one isolated mark of attaching all the projections in
`xs` by owned choice. A foreign owner can absorb on either the attached
inputs or the original term. The support can be empty or have repetitions. -/
theorem mem_fold_projections_probe_iff (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var)
    (r : Role) (xs : List Var) (t : CoreTerm Role Var) :
    q.1 ∈ ((foldTerm r (xs.map (.var ·)) t).realize (probeAt three q)).val ↔
      (q.1 ∈ (t.realize (probeAt three q)).val ∨ q.2.1 ∈ xs) ∧
      (r = q.1 ∨ t.realize (probeAt three q) ≠ WinnerSet.singleton r) ∧
      ∀ i ∈ xs, posting q i ≠ some r := by
  classical
  by_cases hr : r = q.1
  · subst r
    simp only [true_or,
      and_iff_left (show ∀ i ∈ xs, posting q i ≠ some q.1 from fun i _ => posting_ne_observer q i)]
    induction xs with
    | nil => simp [foldTerm]
    | cons i xs ih =>
      change q.1 ∈ (WinnerSet.choice q.1 (probeAt three q i)
        ((foldTerm q.1 (xs.map (.var ·)) t).realize (probeAt three q))).val ↔ _
      rw [WinnerSet.mem_choice_owner,ih]
      simp only [probeAt,mem_probe_iff,List.mem_cons]
      grind
  · simp only [hr,false_or]
    have atom (ys : List Var) :
        (foldTerm r (ys.map (.var ·)) t).realize (probeAt three q) = WinnerSet.singleton r ↔
          t.realize (probeAt three q) = WinnerSet.singleton r ∨ ∃ i ∈ ys, posting q i = some r := by
      induction ys with
      | nil => simp [foldTerm]
      | cons i ys ih =>
        change WinnerSet.choice r (probeAt three q i)
          ((foldTerm r (ys.map (.var ·)) t).realize (probeAt three q)) = _ ↔ _
        rw [WinnerSet.choice_eq_owner_iff,ih,probeAt_eq_atom_iff_posted three q i hr]
        simp only [List.mem_cons,exists_eq_or_imp]
        tauto
    induction xs with
    | nil =>
      simp only [List.map_nil,foldTerm,List.foldr_nil,List.not_mem_nil,or_false,
        false_implies,implies_true,and_true,iff_self_and]
      intro hm he
      rw [he] at hm
      exact hr hm.symm
    | cons i xs ih =>
      change q.1 ∈ (WinnerSet.choice r (probeAt three q i)
        ((foldTerm r (xs.map (.var ·)) t).realize (probeAt three q))).val ↔ _
      rw [WinnerSet.mem_choice_other r q.1 hr]
      have operand : q.1 ∈ (probeAt three q i).val ↔ i = q.2.1 :=
        mem_probe_iff three q.1 q.2.1 q.2.2 i
      simp only [ih,ne_eq,atom xs,probeAt_eq_atom_iff_posted three q i hr,not_or,not_exists,
        not_and,List.mem_cons,forall_eq_or_imp,operand]
      grind

omit [DecidableEq Role] in
/-- A row with no owner posting in the candidate support allows its head
to be pruned without losing any safe sub-support. -/
theorem erase_unhit_head_preserves_safe_subsets [DecidableEq Var]
    (neg : Row → ProbeIndex Role Var) (r : Role) (U S : Finset Var) (z : Row)
    (unhit : ∀ i ∈ U, posting (neg z) i ≠ some r)
    (safe : ∀ y, (neg y).2.1 ∈ S → ∃ i ∈ S, posting (neg y) i = some r) :
    S ⊆ U.erase (neg z).2.1 ↔ S ⊆ U := by
  refine ⟨fun h => h.trans (Finset.erase_subset _ _), ?_⟩
  intro sub j hj
  refine Finset.mem_erase.mpr ⟨?_,sub hj⟩
  rintro rfl
  obtain ⟨i,hi,post⟩ := safe z hj
  exact unhit i (sub hi) post

/-- A safe fold avoiding the positive coloring deletes all rows it hits.
The last term in the displayed fold can be any witness for the residual
rows. The rows and the positive may use arbitrary passive colors. -/
theorem safe_fold_lifts_mark (three : Fin 3 ↪ Role) (neg : Row → ProbeIndex Role Var)
    (p : ProbeIndex Role Var) (r : Role) (S : Finset Var)
    (safe : ∀ z, (neg z).2.1 ∈ S → ∃ i ∈ S, posting (neg z) i = some r)
    (avoid : ∀ i ∈ S, posting p i ≠ some r)
    (t : CoreTerm Role Var) (positive : p.1 ∈ (t.realize (probeAt three p)).val)
    (residual : ∀ z, (∀ i ∈ S, posting (neg z) i ≠ some r) →
      (neg z).1 ∉ (t.realize (probeAt three (neg z))).val) :
    let lifted := foldTerm r (S.toList.map (.var ·)) t
    p.1 ∈ (lifted.realize (probeAt three p)).val ∧
      ∀ z, (neg z).1 ∉ (lifted.realize (probeAt three (neg z))).val := by
  classical
  dsimp only
  constructor
  · apply (mem_fold_projections_probe_iff three p r S.toList t).mpr
    refine ⟨Or.inl positive, or_iff_not_imp_left.mpr (fun ne he => ?_), ?_⟩
    · rw [he] at positive
      exact ne positive.symm
    · simpa only [Finset.mem_toList] using avoid
  · intro z hm
    obtain ⟨hmark,_,unhit⟩ := (mem_fold_projections_probe_iff three (neg z) r S.toList t).mp hm
    simp only [Finset.mem_toList] at unhit hmark
    obtain hit | head := hmark
    · exact residual z unhit hit
    · obtain ⟨i, hi, post⟩ := safe z head
      exact unhit i hi post

/-- Removing every negative row hit by a safe fold preserves feasibility of
any marked observation whose positive coloring the fold avoids. -/
theorem mark_feasible_iff_after_fold_deletion (three : Fin 3 ↪ Role)
    (neg : Row → ProbeIndex Role Var) (p : ProbeIndex Role Var) (r : Role) (S : Finset Var)
    (safe : ∀ z, (neg z).2.1 ∈ S → ∃ i ∈ S, posting (neg z) i = some r)
    (avoid : ∀ i ∈ S, posting p i ≠ some r) :
    (∃ t : CoreTerm Role Var, p.1 ∈ (t.realize (probeAt three p)).val ∧
      ∀ z, (neg z).1 ∉ (t.realize (probeAt three (neg z))).val) ↔
    ∃ t : CoreTerm Role Var, p.1 ∈ (t.realize (probeAt three p)).val ∧
      ∀ z, (∀ i ∈ S, posting (neg z) i ≠ some r) →
        (neg z).1 ∉ (t.realize (probeAt three (neg z))).val := by
  constructor
  · rintro ⟨t,hp,hn⟩
    exact ⟨t,hp,fun z _ => hn z⟩
  · rintro ⟨t,hp,hn⟩
    exact ⟨_,safe_fold_lifts_mark three neg p r S safe avoid t hp hn⟩

private theorem exists_surviving_head_of_comparisons (three : Fin 3 ↪ Role)
    (row : Var → ProbeIndex Role Var) (head : ∀ j, (row j).2.1 = j)
    (le : Role → Var → Var → Prop) (total : ∀ r i j, le r i j ∨ le r j i)
    (trans : ∀ r i j k, le r i j → le r j k → le r i k)
    (down : ∀ j i r, posting (row j) i = some r → ¬le r j i)
    (t : CoreTerm Role Var) : ∃ j, (row j).1 ∈ (t.realize (probeAt three (row j))).val := by
  classical
  let tracks (x : CoreTerm Role Var) (j : Var) := ∀ r A, profile r A x = true →
    ∃ i, A i = true ∧ le r j i
  let live (x : CoreTerm Role Var) (j : Var) :=
    (row j).1 ∈ (x.realize (probeAt three (row j))).val
  have step (r : Role) (x y : CoreTerm Role Var) (j k : Var)
      (xRank : tracks x j) (yRank : tracks y k) (xLive : live x j) (first : le r j k) :
      tracks (choiceTerm r x y) j ∧ live (choiceTerm r x y) j := by
    constructor
    · intro s A h
      by_cases same : r = s
      · subst s
        have children : profile r A x = true ∨ profile r A y = true := by
          simpa only [profile_choice,ite_true,Bool.or_eq_true] using h
        obtain left | right := children
        · exact xRank r A left
        · obtain ⟨i,hi,hki⟩ := yRank r A right
          exact ⟨i,hi,trans r j k i first hki⟩
      · have children : profile s A x = true ∧ profile s A y = true := by
          simpa only [profile_choice,same,ite_false,Bool.and_eq_true] using h
        exact xRank s A children.1
    · change (row j).1 ∈ (WinnerSet.choice r (x.realize _) (y.realize _)).val
      by_cases same : r = (row j).1
      · subst r
        exact (WinnerSet.mem_choice_owner _ _ _).mpr (Or.inl xLive)
      · apply (WinnerSet.mem_choice_other r (row j).1 same _ _).mpr
        refine ⟨Or.inl xLive, ?_, ?_⟩
        · intro atom
          change (row j).1 ∈ (x.realize (probeAt three (row j))).val at xLive
          rw [atom] at xLive
          exact same xLive.symm
        · intro atom
          have wins := (winnerSet_eq_singleton_iff_profile y r _).mp atom
          obtain ⟨i,hi,hki⟩ := yRank r _ wins
          have post := (probeAt_eq_atom_iff_posted three (row j) i same).mp (of_decide_eq_true hi)
          exact down j i r post (trans r j k i first hki)
  suffices ∃ j, tracks t j ∧ live t j by
    obtain ⟨j,_,hj⟩ := this
    exact ⟨j,hj⟩
  induction t using induction_choice with
  | var i =>
    refine ⟨i,fun r _ h => ⟨i,h,(total r i i).elim id id⟩,?_⟩
    exact (mem_probe_iff three _ _ _ i).mpr (head i).symm
  | choice r x y hx hy =>
    obtain ⟨j,hj,livej⟩ := hx
    obtain ⟨k,hk,livek⟩ := hy
    rcases total r j k with first | second
    · exact ⟨j,step r x y j k hj hk livej first⟩
    · obtain ⟨h,h'⟩ := step r y x k j hk hj livek second
      refine ⟨k,fun s A yes => h s A ?_,?_⟩
      · simpa only [profile_choice,Bool.or_comm,Bool.and_comm] using yes
      · change (row k).1 ∈ (WinnerSet.choice r (x.realize _) (y.realize _)).val
        rw [WinnerSet.choice_comm]
        exact h'

/-- Give each owner a rank that decreases along its postings. Even for
mixed-color rows, every core term supplies the mark on at least one of
the chosen rows, one for each head. -/
theorem exists_surviving_head_of_ranked_postings (three : Fin 3 ↪ Role)
    (row : Var → ProbeIndex Role Var) (head : ∀ j, (row j).2.1 = j)
    (rank : Role → Var → ℕ)
    (down : ∀ j i r, posting (row j) i = some r → rank r i < rank r j)
    (t : CoreTerm Role Var) : ∃ j, (row j).1 ∈ (t.realize (probeAt three (row j))).val :=
  exists_surviving_head_of_comparisons three row head (fun r i j => rank r i ≤ rank r j)
    (fun _ _ _ => Nat.le_total ..) (fun _ _ _ _ => Nat.le_trans)
    (fun j i r h => Nat.not_le_of_gt (down j i r h)) t

private theorem reverse_comparison_of_acyclic (edge : Var → Var → Prop)
    (acyclic : ∀ j, ¬Relation.TransGen edge j j) :
    ∃ le : Var → Var → Prop, IsLinearOrder Var le ∧ ∀ j i, edge j i → ¬le j i := by
  let reach (x y : Var) := Relation.ReflTransGen edge y x
  let : IsPartialOrder Var reach := {
    refl := fun _ => .refl
    trans := fun _ _ _ h₁ h₂ => h₂.trans h₁
    antisymm := fun x y xy yx => by
      by_contra hne
      have p := (Relation.reflTransGen_iff_eq_or_transGen.mp xy).resolve_left hne
      have z := (Relation.reflTransGen_iff_eq_or_transGen.mp yx).resolve_left (Ne.symm hne)
      exact acyclic y (p.trans z) }
  obtain ⟨le,order,included⟩ := extend_partialOrder reach
  let := order
  refine ⟨le,order,fun j i post forward => ?_⟩
  have eq : j = i := antisymm forward (included i j (.single post))
  subst i
  exact acyclic j (.single post)

private theorem support_of_path {edge : Var → Var → Prop} {x y : Var}
    (p : Relation.TransGen edge x y) :
    ∃ S : Finset Var, x ∈ S ∧ ∀ j ∈ S, ∃ i, (i ∈ S ∨ i = y) ∧ edge j i := by
  classical
  induction p with
  | single h =>
    refine ⟨{x},Finset.mem_singleton_self _,?_⟩
    intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨_,Or.inr rfl,h⟩
  | @tail u v _ step ih =>
    obtain ⟨S,hx,walk⟩ := ih
    refine ⟨insert u S,Finset.mem_insert_of_mem hx,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | old
    · exact ⟨v,Or.inr rfl,step⟩
    · obtain ⟨i,hi,edgeji⟩ := walk j old
      exact ⟨i,Or.inl (Finset.mem_insert.mpr hi.symm),edgeji⟩

/-- One arbitrary negative row per head has a simultaneous omitting word
exactly when its posting graph contains a nonempty cycle of one color.
The cycle yields a finite fold even when the input type is infinite. -/
theorem exists_safe_word_iff_monochromatic_cycle (three : Fin 3 ↪ Role)
    (row : Var → ProbeIndex Role Var) (head : ∀ j, (row j).2.1 = j) :
    (∃ t : CoreTerm Role Var, ∀ j, (row j).1 ∉ (t.realize (probeAt three (row j))).val) ↔
      ∃ r j, Relation.TransGen (fun x y => posting (row x) y = some r) j j := by
  classical
  constructor
  · rintro ⟨t,safe⟩
    by_contra! noCycle
    choose le order down using fun r =>
      reverse_comparison_of_acyclic (fun x y => posting (row x) y = some r) (noCycle r)
    obtain ⟨j,hit⟩ := exists_surviving_head_of_comparisons three row head le
      (fun r => (order r).total) (fun r => (order r).trans) (fun j i r => down r j i) t
    exact safe j hit
  · rintro ⟨r,x,cycle⟩
    obtain ⟨S,hx,walk⟩ := support_of_path cycle
    refine ⟨foldTerm r (S.toList.map (.var ·)) (.var x),fun j hit => ?_⟩
    obtain ⟨mark,_,unhit⟩ := (mem_fold_projections_probe_iff three (row j) r S.toList (.var x)).mp hit
    simp only [FirstOrder.Language.Term.realize_var,probeAt,mem_probe_iff,
      Finset.mem_toList,head] at mark
    have hj : j ∈ S := mark.elim (fun eq => eq ▸ hx) id
    obtain ⟨i,hi,post⟩ := walk j hj
    exact unhit i (Finset.mem_toList.mpr (hi.elim id (fun eq => eq ▸ hx))) post

/-- Each safe word contains a monochromatic cycle on its own inputs. -/
theorem exists_monochromatic_cycle_on_support [DecidableEq Var] (three : Fin 3 ↪ Role)
    (observer : Var → Role) (p : ∀ j, Pattern (observer j) j) (t : CoreTerm Role Var)
    (safe : ∀ j, observer j ∉ (t.realize (probe three (observer j) j (p j))).val) :
    ∃ (r : Role) (j : t.varFinset), Relation.TransGen
      (fun x y : t.varFinset => posting ⟨observer x.val,x.val,p x.val⟩ y.val = some r) j j := by
  classical
  let rows (j : t.varFinset) : ProbeIndex Role t.varFinset :=
    ⟨observer j.val,j,fun i => p j.val ⟨i.val.val,fun h => i.property (Subtype.ext h)⟩⟩
  have restricted (j i : t.varFinset) :
      probeAt three (rows j) i = probe three (observer j.val) j.val (p j.val) i.val := by
    by_cases h : i = j
    · subst i
      simp [rows,probeAt]
    · have hv : i.val ≠ j.val := fun eq => h (Subtype.ext eq)
      simp [rows,probeAt,probe,h,hv]
  have samePosting (j i : t.varFinset) :
      posting (rows j) i = posting ⟨observer j.val,j.val,p j.val⟩ i.val := by
    by_cases h : i = j
    · subst i
      simp [rows,posting]
    · have hv : i.val ≠ j.val := fun eq => h (Subtype.ext eq)
      simp [rows,posting,h,hv]
  have omits (j : t.varFinset) :
      (rows j).1 ∉ ((t.restrictVar id).realize (probeAt three (rows j))).val := by
    rw [FirstOrder.Language.Term.realize_restrictVar (f := id) _ (restricted j)]
    exact safe j.val
  obtain ⟨r,j,cycle⟩ := (exists_safe_word_iff_monochromatic_cycle three rows (fun _ => rfl)).mp
    ⟨t.restrictVar id,omits⟩
  exact ⟨r,j,by simpa only [samePosting] using cycle⟩

/-- If a chosen loss at every head has strictly decreasing rank at every
same-owner posting, these losses alone exclude every core word. The
ranking can ignore all cross-owner edges. -/
theorem not_exists_safe_word_of_ranked_postings [DecidableEq Var]
    (three : Fin 3 ↪ Role) (observer owner : Var → Role)
    (p : ∀ j, Pattern (observer j) j)
    (mono : ∀ j i q, p j i = .atom q → q.val = owner j)
    (rank : Var → ℕ)
    (decreases : ∀ j (i : {i // i ≠ j}), p j i ≠ .neutral →
      owner i.val = owner j → rank i.val < rank j) :
    ¬∃ t : CoreTerm Role Var, ∀ j, observer j ∉ (t.realize (probe three (observer j) j (p j))).val := by
  rintro h
  obtain ⟨r,S,nonempty,howner,succ⟩ :=
    (exists_safe_word_iff_posted_successors three observer owner p mono).mp h
  obtain ⟨j,hj,least⟩ := S.exists_min_image rank nonempty
  obtain ⟨i,hi,post⟩ := succ j hj
  exact (Nat.not_lt_of_ge (least i.val hi))
    (decreases j i post ((howner i.val hi).trans (howner j hj).symm))

end KFOL.Core.Sources
