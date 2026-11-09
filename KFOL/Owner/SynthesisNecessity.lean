module

public import KFOL.Owner.Synthesis

/-! Necessity of saturation for an independently given term realization. -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} [DecidableEq Role]

theorem root_guard_mem (t : Term Role Var) (observer : Role) :
    (⟨t.root, [], []⟩ : Guard Var) ∈ t.guards observer := by
  induction t using induction_owner with
  | var j => exact List.mem_singleton_self _
  | step s t _ ht => exact List.mem_append_left _ ht
  | guarded r x y z hx _ _ => exact List.mem_append_left _ hx

/-- Every nonroot contribution tests ambiguity at the independently defined root. -/
theorem root_mem_guard_many (t : Term Role Var) (observer : Role) (q : Guard Var)
    (hq : q ∈ t.guards observer) (hne : q.source ≠ t.root) : t.root ∈ q.many := by
  induction t using induction_owner generalizing q with
  | var j =>
    have he := List.mem_singleton.mp hq
    cases he
    exact False.elim (hne rfl)
  | step s t hs ht =>
    rcases List.mem_append.mp hq with hq | hq
    · exact ht q hq hne
    · obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
      exact List.mem_cons_self ..
  | guarded r x y z hx _ _ =>
    rcases List.mem_append.mp hq with hq | hq
    · exact hx q hq hne
    · obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
      exact List.mem_cons_self ..

end Term

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

private def Admissible {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer : Role) (t : Term Role Var) (S : SaturationState Var) : Prop :=
  ∀ q ∈ t.guards observer, T.Permitted q.source (S.many ∪ q.many.toFinset) (S.outside ∪ q.outside.toFinset)

private theorem admissible_mono {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer : Role) (t : Term Role Var) {S R : SaturationState Var} (h : S.Below R)
    (ht : T.Admissible observer t S) : T.Admissible observer t R := by
  intro q hq
  apply T.permitted_mono q.source ⟨S.many ∪ q.many.toFinset, S.outside ∪ q.outside.toFinset⟩
    ⟨R.many ∪ q.many.toFinset, R.outside ∪ q.outside.toFinset⟩ ?_ (ht q hq)
  constructor
  · exact Finset.union_subset_union h.1 (Finset.Subset.refl _)
  · intro i hi
    simp only [Finset.mem_union] at hi ⊢
    rcases hi with (hi | hi) | (hi | hi)
    · rcases Finset.mem_union.mp (h.2 (Finset.mem_union_left _ hi)) with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inr (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · rcases Finset.mem_union.mp (h.2 (Finset.mem_union_right _ hi)) with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)

private theorem admissible_root {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer : Role) (t : Term Role Var) (S : SaturationState Var)
    (ht : T.Admissible observer t S) : T.Permitted t.root S.many S.outside := by
  simpa only [List.toFinset_nil, Finset.union_empty] using ht _ (t.root_guard_mem observer)

private theorem admissible_step_right {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer : Role) (s t : Term Role Var) (S : SaturationState Var)
    (ht : T.Admissible observer (Term.step s t) S) : T.Admissible observer t S := by
  intro q hq
  exact ht q (List.mem_append_left _ hq)

private theorem admissible_step_left {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer : Role) (s t : Term Role Var) (S : SaturationState Var)
    (ht : T.Admissible observer (Term.step s t) S) :
    T.Admissible observer s ⟨insert t.root S.many, S.outside⟩ := by
  intro q hq
  have hp := ht (q.addMany t.root) (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  simpa only [Guard.addMany, List.toFinset_cons, Finset.union_insert, Finset.insert_union] using hp

private theorem admissible_guarded_first {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer owner : Role) (x y z : Term Role Var) (S : SaturationState Var)
    (ht : T.Admissible observer (Term.guarded owner x y z) S) : T.Admissible observer x S := by
  intro q hq
  exact ht q (List.mem_append_left _ hq)

private theorem admissible_guarded_sides {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (observer owner : Role) (hne : owner ≠ observer) (x y z : Term Role Var) (S : SaturationState Var)
    (ht : T.Admissible observer (Term.guarded owner x y z) S) :
    T.Admissible observer y ⟨insert x.root S.many, S.outside ∪ {y.root, z.root}⟩ ∧
    T.Admissible observer z ⟨insert x.root S.many, S.outside ∪ {y.root, z.root}⟩ := by
  have hside : ∀ t : Term Role Var, (∀ q ∈ t.guards observer, q ∈ y.guards observer ++ z.guards observer) →
      T.Admissible observer t ⟨insert x.root S.many, S.outside ∪ {y.root, z.root}⟩ := by
    intro t hmem q hq
    have hp := ht (((q.addOutside y.root).addOutside z.root).addMany x.root) (by
      rw [Term.guards_guarded, ite_eq_right hne]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, List.mem_map.mpr
        ⟨_, List.mem_map.mpr ⟨q, hmem q hq, rfl⟩, rfl⟩, rfl⟩))
    simpa only [Guard.addMany, Guard.addOutside, List.toFinset_cons, Finset.union_insert,
      Finset.insert_union, Finset.union_singleton, Finset.insert_comm, Finset.union_assoc] using hp
  exact ⟨hside y (fun _ hq => List.mem_append_left _ hq), hside z (fun _ hq => List.mem_append_right _ hq)⟩

/-- A term realizing the independent candidate semantics makes each of its
raw occurrence guards permitted. The named three roles witness all statuses. -/
private theorem realizes_admissible {Role : Type u} [DecidableEq Role]
    (T : GuardTable Var) (owner observer background : Role)
    (hko : observer ≠ owner) (hkb : observer ≠ background) (hob : owner ≠ background)
    (t : Term Role Var) (ht : T.Realizes owner t) (S : SaturationState Var) :
    T.Admissible observer t S := by
  intro q hq
  let v := minimalVal observer owner background q
  have heval : observer ∈ (t.eval v).val := by
    apply (t.guard_semantics observer owner (t.owners_mono _ _ ht.2.1 (fun r hr => Or.inr hr)) v).mpr
    exact (eval_minimalVal observer owner background hko hkb hob q _).mpr
      ⟨q, hq, rfl, (fun _ h => h), fun _ h => Or.inr (Or.inl h)⟩
  obtain ⟨j, g, hg, hm, hn, hj⟩ := (ht.2.2 observer hko v).mp heval
  have hje : j = q.source := (minimalVal_marker observer owner background hko hkb q j).mp hj
  subst j
  refine ⟨g, hg, ?_, ?_⟩
  · intro i hi
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      ((minimalVal_ambiguous observer owner background hko hob q i).mp (hm hi)))
  · intro i hi
    have hstatus := (minimalVal_outside observer owner background hko hob q i).mp (hn hi)
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_singleton]
    rcases hstatus with h | h | h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr h

/-- A closed state absorbs the root of a nonterminal reset path. -/
private theorem closed_reset (T : GuardTable Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (hc : T.Closed j g S) (w : Var) (hw : w ∈ g.many)
    (hp : T.Permitted w S.many S.outside) : w ∈ S.many := by
  have hext : T.Permitted w S.many (S.outside ∪ {w, w}) :=
    T.permitted_mono w S ⟨S.many, S.outside ∪ {w, w}⟩
      ⟨Finset.Subset.refl _, Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_left⟩ hp
  have hf := hc w hw w (Finset.mem_union_left _ (Finset.mem_union_left _ hw)) hext hext
  rw [← hf]
  exact Finset.mem_insert_self ..

private theorem side_state_below (S : SaturationState Var) (w z : Var)
    (hw : w ∈ S.many) (hz : z ∈ S.many ∪ S.outside) :
    (⟨S.many, S.outside ∪ {w, z}⟩ : SaturationState Var).Below S := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro i hi
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hi | hi | rfl | rfl
  · exact Finset.mem_union_left _ hi
  · exact Finset.mem_union_right _ hi
  · exact Finset.mem_union_left _ hw
  · exact hz

/-- The path-descent argument: any admitted target occurrence below a root
already in C reaches one of the two finishing alternatives at a closed state. -/
private theorem admissible_finish {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (owner observer : Role) (hko : observer ≠ owner) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (hc : T.Closed j g S) (t : Term Role Var)
    (hown : t.OwnersIn (fun x => x = owner)) (had : T.Admissible observer t S)
    (hr : t.root ∈ S.many) (q : Guard Var) (hq : q ∈ t.guards observer) (hs : q.source = j)
    (hm : ∀ i ∈ q.many, i ∈ g.many) (hn : ∀ i ∈ q.outside, i ∈ target j g) :
    T.Finish j g S := by
  induction t using Term.induction_owner generalizing q with
  | var i =>
    have he := List.mem_singleton.mp hq
    cases he
    exact Or.inl (hs ▸ T.admissible_root observer (.var i) S had)
  | step s t ihs iht =>
    rcases List.mem_append.mp hq with hq | hq
    · exact iht hown.2 (T.admissible_step_right observer s t S had) hr q hq hs hm hn
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      have hs' : q'.source = j := hs
      have hm' : ∀ i ∈ q'.many, i ∈ g.many := fun i hi => hm i (List.mem_cons_of_mem _ hi)
      have htroot : t.root ∈ S.many := hr
      have hads := T.admissible_step_left observer s t S had
      have hads' : T.Admissible observer s S := by
        simpa only [Finset.insert_eq_of_mem htroot] using hads
      have hp := T.admissible_root observer s S hads'
      by_cases he : s.root = j
      · exact Or.inl (he ▸ hp)
      · have hw : s.root ∈ g.many := hm' _ (s.root_mem_guard_many observer q' hq' (by simpa only [hs'] using Ne.symm he))
        exact ihs hown.1 hads' (T.closed_reset j g S hc s.root hw hp) q' hq' hs' hm' hn
  | guarded a x y z ihx ihy ihz =>
    obtain ⟨rfl, hx, hy, hz⟩ := hown
    rw [Term.guards_guarded, ite_eq_right hko.symm] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihx hx (T.admissible_guarded_first observer a x y z S had) hr q hq hs hm hn
    · obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq
      obtain ⟨q2, hq2, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq2
      have hs' : q'.source = j := hs
      have hm' : ∀ i ∈ q'.many, i ∈ g.many := fun i hi => hm i (List.mem_cons_of_mem _ hi)
      have hn' : ∀ i ∈ q'.outside, i ∈ target j g := fun i hi => hn i
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))
      have hyU : y.root ∈ target j g := hn _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hzU : z.root ∈ target j g := hn _ (List.mem_cons_self ..)
      obtain ⟨hady, hadz⟩ := T.admissible_guarded_sides observer a hko.symm x y z S had
      have hrx : x.root ∈ S.many := hr
      simp only [Finset.insert_eq_of_mem hrx] at hady hadz
      have hpy := T.admissible_root observer y _ hady
      have hpz := T.admissible_root observer z _ hadz
      rcases List.mem_append.mp hq' with hq' | hq'
      · by_cases he : y.root = j
        · exact Or.inr ⟨z.root, hzU, he ▸ hpy, by simpa only [he] using hpz⟩
        · have hw : y.root ∈ g.many := hm' _ (y.root_mem_guard_many observer q' hq' (by simpa only [hs'] using Ne.symm he))
          have hf := hc y.root hw z.root hzU hpy hpz
          have hwC : y.root ∈ S.many := by
            rw [← hf]
            exact Finset.mem_insert_self ..
          have hzCD : z.root ∈ S.many ∪ S.outside := by
            rw [← hf, SaturationState.update_union]
            exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          exact ihy hy (T.admissible_mono observer y (side_state_below S y.root z.root hwC hzCD) hady)
            hwC q' hq' hs' hm' hn'
      · have hadz' : T.Admissible observer z ⟨S.many, S.outside ∪ {z.root, y.root}⟩ := by
          simpa only [Finset.pair_comm z.root y.root] using hadz
        have hpz' := T.admissible_root observer z _ hadz'
        have hpy' : T.Permitted y.root S.many (S.outside ∪ {z.root, y.root}) := by
          simpa only [Finset.pair_comm z.root y.root] using hpy
        by_cases he : z.root = j
        · exact Or.inr ⟨y.root, hyU, he ▸ hpz', by simpa only [he] using hpy'⟩
        · have hw : z.root ∈ g.many := hm' _ (z.root_mem_guard_many observer q' hq' (by simpa only [hs'] using Ne.symm he))
          have hf := hc z.root hw y.root hyU hpz' hpy'
          have hwC : z.root ∈ S.many := by
            rw [← hf]
            exact Finset.mem_insert_self ..
          have hyCD : y.root ∈ S.many ∪ S.outside := by
            rw [← hf, SaturationState.update_union]
            exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          exact ihz hz (T.admissible_mono observer z (side_state_below S z.root y.root hwC hyCD) hadz')
            hwC q' hq' hs' hm' hn'

/-- Every guard in a canonical independently realized table passes the
actual bounded saturation program. The proof follows the supplying raw
occurrence through the original term, and needs no assumed pruning theorem. -/
theorem realizes_accepts {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (owner observer background : Role) (hko : observer ≠ owner)
    (hkb : observer ≠ background) (hob : owner ≠ background)
    (hcan : T.Canonical) (positions : List Var) (j : Var) (g : GuardPair Var)
    (hg : g ∈ T.guards j) (hcover : target j g ⊆ positions.toFinset)
    (t : Term Role Var) (ht : T.Realizes owner t) : T.accepts positions j g = true := by
  classical
  unfold accepts
  rw [decide_eq_true_eq]
  by_cases hj : j = T.root
  · exact Or.inl hj
  · right
    let targetGuard : Guard Var := ⟨j, g.many.toList, g.outside.toList⟩
    let v := minimalVal observer owner background targetGuard
    have heval : observer ∈ (t.eval v).val := by
      apply (ht.2.2 observer hko v).mpr
      refine ⟨j, g, hg, ?_, ?_, ?_⟩
      · intro i hi
        apply (minimalVal_ambiguous observer owner background hko hob targetGuard i).mpr
        exact Finset.mem_toList.mpr hi
      · intro i hi
        apply (minimalVal_outside observer owner background hko hob targetGuard i).mpr
        exact Or.inr (Or.inl (Finset.mem_toList.mpr hi))
      · exact (minimalVal_marker observer owner background hko hkb targetGuard j).mpr rfl
    have hguards := (t.guard_semantics observer owner
      (t.owners_mono _ _ ht.2.1 (fun r hr => Or.inr hr)) v).mp heval
    obtain ⟨q, hq, hdom⟩ := (eval_minimalVal observer owner background hko hkb hob targetGuard _).mp hguards
    have hrA := ((hcan.2.2 j hj).1 g hg).1
    have hfixed := T.run_fixed positions j g hrA hcover
    have hclosed := (T.next_eq_none_iff positions j g _ hcover).mp hfixed
    have hroot : t.root ∈ (T.run positions j g (2 * positions.length)).1.many := by
      rw [ht.1]
      exact (T.initial_le_run positions j g _).1 (Finset.mem_singleton_self _)
    apply T.admissible_finish owner observer hko j g _ hclosed t ht.2.1
      (T.realizes_admissible owner observer background hko hkb hob t ht _) hroot q hq hdom.1
    · intro i hi
      exact Finset.mem_toList.mp (hdom.2.1 i hi)
    · intro i hi
      rcases hdom.2.2 i hi with hm | hn | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_toList.mp hm))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_toList.mp hn))
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr he)

/-- Full semantic recognition: on canonical listed input the executable
checker accepts exactly the tables realized by native one-owner terms. -/
theorem check_iff_realizable {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (owner observer background : Role) (hko : observer ≠ owner)
    (hkb : observer ≠ background) (hob : owner ≠ background)
    (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions) :
    T.check positions = true ↔ ∃ t : Term Role Var, T.Realizes owner t := by
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((T.synthesize_isSome owner positions).mpr hc)
    exact ⟨t, (T.synthesize_spec owner positions ht).1⟩
  · rintro ⟨t, ht⟩
    apply (T.check_iff positions).mpr
    refine ⟨hcan, hlisted, ?_⟩
    intro p hp
    exact T.realizes_accepts owner observer background hko hkb hob hcan positions p.1 p.2
      ((T.mem_guards ..).mpr hp) (hlisted.2 p hp) t ht

/-- The successful native construction has the independent intended semantics
and an explicit bound on its entire expanded tree. -/
theorem synthesis_iff {Role : Type u} [DecidableEq Role] (T : GuardTable Var)
    (owner observer background : Role) (hko : observer ≠ owner)
    (hkb : observer ≠ background) (hob : owner ≠ background)
    (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions) :
    (∃ t : Term Role Var, T.Realizes owner t) ↔
      ∃ t : Term Role Var, T.synthesize owner positions = some t ∧ T.Realizes owner t ∧
        t.size ≤ 1 + T.entries.length * (10 * positions.length + 7) := by
  constructor
  · intro hr
    have hc := (T.check_iff_realizable owner observer background hko hkb hob positions hcan hlisted).mpr hr
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((T.synthesize_isSome owner positions).mpr hc)
    exact ⟨t, ht, T.synthesize_spec owner positions ht⟩
  · rintro ⟨t, _, ht, _⟩
    exact ⟨t, ht⟩

end GuardTable
end KFOL.Owner
