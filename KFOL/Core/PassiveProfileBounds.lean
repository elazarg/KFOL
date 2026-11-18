module

public import KFOL.Core.ProfileCompletion
public import KFOL.Core.SingleSourceCompletion
public import Mathlib.Order.Preorder.Finite

/-! # Singleton profiles with several uncolored source heads

Across the excluded observations, passive inputs can post singletons but
never carry a mark. For a rainbow or a same-owner profile gap, a safe word
exists precisely when an eligible projection can suppress each of its marks
using a qualifying posted passive input.
-/

@[expose] public section

namespace KFOL.Core.PassiveProfileBounds

open ProfileBounds
open scoped Classical

universe u v w
variable {Role : Type u} {Var : Type v} {Row : Type w}
attribute [local instance] Equational.coreStructure

abbrev Word (Role : Type u) (Var : Type v) := Equational.Term (Equational.CoreSymbol Role) Var

/-- A rainbow or gap in the profile relation, or a possible winner at one valuation. -/
inductive Demand (Role : Type u) (Var : Type v) where
  | rainbow (A : Role → Var → Bool)
  | gap (owner : Role) (A B : Var → Bool)
  | win (owner : Role) (v : Var → WinnerSet Role)

/-- An eligible projection meets the demand by itself. -/
def Eligible : Demand Role Var → Var → Prop
  | .rainbow A, i => ∀ r, A r i = true
  | .gap _ A B, i => A i = true ∧ B i = false
  | .win k v, i => k ∈ (v i).val

/-- Attaching this input by choice at this owner preserves the demand. -/
def Helper : Demand Role Var → Role → Var → Prop
  | .rainbow A, q, i => ∀ r, r ≠ q → A r i = true
  | .gap r A B, q, i => if q = r then B i = false else A i = true
  | .win k v, q, i => q = k ∨ v i ≠ WinnerSet.singleton q

def Meets [DecidableEq Role] : Demand Role Var → Word Role Var → Prop
  | .rainbow A, t => ∀ r, profile r (A r) t = true
  | .gap r A B, t => profile r A t = true ∧ profile r B t = false
  | .win k v, t => k ∈ (t.realize v).val

/-- The term omits the prescribed observer at every row. -/
def Safe (values : Row → Var → WinnerSet Role) (mark : Row → Role) (t : Word Role Var) : Prop :=
  ∀ z, mark z ∉ (t.realize (values z)).val

/-- Every input used as a singleton helper is free of the mark at every row. -/
def PassiveAtoms (values : Row → Var → WinnerSet Role) (mark : Row → Role) : Prop :=
  ∀ z i q, values z i = WinnerSet.singleton q → ∀ y, mark y ∉ (values y i).val

/-- At every row whose mark this projection carries, a posted helper is available. -/
def LeafCondition (values : Row → Var → WinnerSet Role) (mark : Row → Role)
    (d : Demand Role Var) : Prop :=
  ∃ i, Eligible d i ∧ ∀ z, mark z ∈ (values z i).val →
    ∃ q a, values z a = WinnerSet.singleton q ∧ Helper d q a

private theorem meets_var [DecidableEq Role] (d : Demand Role Var) (i : Var) :
    Meets d (.var i) ↔ Eligible d i := by cases d <;> rfl

private theorem meets_child [DecidableEq Role] (d : Demand Role Var) (q : Role) (s t : Word Role Var)
    (h : Meets d (choiceTerm q s t)) : Meets d s ∨ Meets d t := by
  cases d with
  | win k v => exact WinnerSet.choice_subset_union q _ _ h
  | rainbow A =>
    have own : profile q (A q) s = true ∨ profile q (A q) t = true := by
      simpa [profile_choice] using h q
    have other (r : Role) (hr : r ≠ q) :
        profile r (A r) s = true ∧ profile r (A r) t = true := by
      simpa [profile_choice, Ne.symm hr] using h r
    rcases own with hs | ht
    · left
      intro r
      by_cases he : r = q
      · simpa [he] using hs
      · exact (other r he).1
    · right
      intro r
      by_cases he : r = q
      · simpa [he] using ht
      · exact (other r he).2
  | gap r A B =>
    obtain ⟨ha,hb⟩ := h
    by_cases he : q = r
    · simp [profile_choice, he] at ha hb
      exact ha.elim (fun hs => Or.inl ⟨hs,hb.1⟩) (fun ht => Or.inr ⟨ht,hb.2⟩)
    · simp only [profile_choice, ite_eq_right he, Bool.and_eq_true, Bool.and_eq_false_iff] at ha hb
      exact hb.elim (fun hs => Or.inl ⟨ha.1,hs⟩) (fun ht => Or.inr ⟨ha.2,ht⟩)

private theorem meets_attach [DecidableEq Role] (d : Demand Role Var) (q : Role) (t : Word Role Var)
    (a : Var) (h : Meets d t) (ha : Helper d q a) : Meets d (choiceTerm q t (.var a)) := by
  cases d with
  | win k v =>
    rcases ha with eq | hn
    · subst q; exact (WinnerSet.mem_choice_owner k _ _).mpr (Or.inl h)
    · by_cases he : q = k
      · subst q
        exact (WinnerSet.mem_choice_owner k _ _).mpr (Or.inl h)
      · refine (WinnerSet.mem_choice_other q k he _ _).mpr ⟨Or.inl h, ?_, hn⟩
        intro atom
        have hk : k ∈ (t.realize v).val := h
        change t.realize v = WinnerSet.singleton q at atom
        rw [atom] at hk
        exact he hk.symm
  | rainbow A =>
    intro r
    by_cases he : q = r
    · simp [profile_choice, he, h r]
    · simp [profile_choice, he, h r, ha r (Ne.symm he)]
  | gap r A B =>
    obtain ⟨hA,hB⟩ := h
    by_cases he : q = r <;> simp_all [Meets, Helper, profile_choice]

private theorem singleton_helper [DecidableEq Role] [Fintype Role] (d : Demand Role Var)
    (t : Word Role Var) (v : Var → WinnerSet Role) (q : Role)
    (h : Meets d t) (he : t.realize v = WinnerSet.singleton q) :
    ∃ a, v a = WinnerSet.singleton q ∧ Helper d q a := by
  have bound : (t.realize v).val ⊆ {q} := by rw [he]; rfl
  cases d with
  | win k w =>
    have hv := (winnerSet_eq_singleton_iff_profile t q v).mp he
    by_cases eq : q = k
    · obtain ⟨i, hi⟩ := profile_common_source (fun _ : Unit => q) (by intro a b _; cases a; cases b; rfl)
        (fun _ i => decide (v i = WinnerSet.singleton q)) t (fun _ => hv)
      exact ⟨i, of_decide_eq_true (hi ()), Or.inl eq⟩
    · by_contra none
      have mono (i : Var) (hv : decide (v i = WinnerSet.singleton q) = true) :
          decide (w i = WinnerSet.singleton q) = true := by
        apply decide_eq_true
        by_contra hn
        exact none ⟨i, of_decide_eq_true hv, Or.inr hn⟩
      have atom := (winnerSet_eq_singleton_iff_profile t q w).mpr (profile_mono q _ _ mono t hv)
      have hk : k ∈ (t.realize w).val := h
      rw [atom] at hk
      exact eq hk.symm
  | rainbow A =>
    have hr := (rainbowSafe_iff Finset.univ A v {q}).mpr ⟨t, fun r _ => h r, bound⟩
    rcases hr.2 with ⟨i, hA, hsub⟩ | ⟨s, _, hsq, i, hi, hA⟩
    · exact ⟨i, WinnerSet.eq_singleton_of_subset _ _ hsub, fun r _ => hA r (Finset.mem_univ _)⟩
    · have eq : s = q := hsq
      subst s
      exact ⟨i, hi, fun r hr => hA r (Finset.mem_univ _) hr⟩
  | gap r A B =>
    have hg := (pairSafe_iff r A B v {q}).mpr ⟨t,h.1,h.2,bound⟩
    rcases hg with ⟨i, hA, hB, hsub⟩ | ⟨hrq, _, i, hi, hB⟩ |
      ⟨_, s, hsq, hsr, i, hA, hi⟩
    · exact ⟨i, WinnerSet.eq_singleton_of_subset _ _ hsub, by simp [Helper]; split <;> assumption⟩
    · have eq : r = q := hrq
      subst r
      exact ⟨i,hi,by simp [Helper,hB]⟩
    · have eq : s = q := hsq
      subst s
      exact ⟨i,hi,by simp [Helper,hsr,hA]⟩

/-- Simultaneous negative observations with passive helpers admit an exact
projection-and-spine test for a rainbow, a gap, or a single positive winner. -/
theorem exists_safe_meeting_iff [DecidableEq Role] [Fintype Role] [Fintype Row]
    (values : Row → Var → WinnerSet Role) (mark : Row → Role) (passive : PassiveAtoms values mark)
    (d : Demand Role Var) :
    (∃ t : Word Role Var, Meets d t ∧ Safe values mark t) ↔ LeafCondition values mark d := by
  classical
  let helped (z : Row) := ∃ q a, values z a = WinnerSet.singleton q ∧ Helper d q a
  constructor
  · rintro ⟨t, hd, safe⟩
    have descend (u : Word Role Var) (hu : Meets d u)
        (quiet : ∀ z, ¬helped z → mark z ∉ (u.realize (values z)).val) : LeafCondition values mark d := by
      induction u using induction_choice with
      | var i =>
        exact ⟨i, (meets_var d i).mp hu, fun z hz => by_contra fun hn => quiet z hn hz⟩
      | choice q s t ihs iht =>
        have both (z : Row) (hn : ¬helped z) :
            mark z ∉ (s.realize (values z)).val ∧ mark z ∉ (t.realize (values z)).val := by
          have noatom : (choiceTerm q s t).realize (values z) ≠ WinnerSet.singleton q := by
            intro he
            obtain ⟨a, ha, ok⟩ := singleton_helper d _ _ q hu he
            exact hn ⟨q,a,ha,ok⟩
          have nc : ¬(s.realize (values z) = WinnerSet.singleton q ∨
              t.realize (values z) = WinnerSet.singleton q) :=
            fun h => noatom ((WinnerSet.choice_eq_owner_iff _ _ q).mpr h)
          have h := quiet z hn
          change mark z ∉ (WinnerSet.choice q _ _).val at h
          simpa [WinnerSet.choice,nc] using h
        exact (meets_child d q s t hu).elim (fun hs => ihs hs (fun z hn => (both z hn).1))
          (fun ht => iht ht (fun z hn => (both z hn).2))
    exact descend t hd fun z _ => safe z
  · rintro ⟨i, hi, chooseHelper⟩
    have build (S : Finset Row) : ∃ t : Word Role Var, Meets d t ∧ ∀ z,
        (mark z ∉ (values z i).val ∨ z ∈ S) → mark z ∉ (t.realize (values z)).val := by
      induction S using Finset.induction_on with
      | empty => exact ⟨.var i,(meets_var d i).mpr hi,fun z h => h.resolve_right (Finset.notMem_empty z)⟩
      | insert z S _ ih =>
        obtain ⟨t,hd,old⟩ := ih
        by_cases hit : mark z ∈ (values z i).val
        · obtain ⟨q,a,ha,ok⟩ := chooseHelper z hit
          refine ⟨choiceTerm q t (.var a), meets_attach d q t a hd ok, fun y h => ?_⟩
          by_cases hy : y = z
          · subst y
            change mark z ∉ (WinnerSet.choice q _ (values z a)).val
            have hp := passive z a q ha z
            simpa [WinnerSet.choice, ha] using hp
          · have hn := old y (h.imp_right (fun hyS => (Finset.mem_insert.mp hyS).resolve_left hy))
            exact fun hh => ((WinnerSet.choice_subset_union q _ _ hh).elim hn (passive z a q ha y))
        · refine ⟨t,hd,fun y h => old y ?_⟩
          rcases h with no | hy
          · exact Or.inl no
          · rcases Finset.mem_insert.mp hy with rfl | hy
            · exact Or.inl hit
            · exact Or.inr hy
    obtain ⟨t,hd,h⟩ := build Finset.univ
    exact ⟨t,hd,fun z => h z (Or.inr (Finset.mem_univ _))⟩

/-- Every winning rainbow and every positive/negative pair admits an eligible
projection passing the tests at all of its marked rows. -/
def ProfileTests (values : Row → Var → WinnerSet Role) (mark : Row → Role)
    (Φ : Role → (Var → Bool) → Bool) : Prop :=
  (∀ A, (∀ r, Φ r (A r) = true) → LeafCondition values mark (.rainbow A)) ∧
  ∀ r A B, Φ r A = true → Φ r B = false → LeafCondition values mark (.gap r A B)

/-- The rainbow and gap tests characterize joint attainment of the full
singleton profile by a word omitting every specified mark. -/
theorem exists_safe_profiles_iff [DecidableEq Role] [Fintype Role] [Fintype Var] [Fintype Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role) (mark : Row → Role)
    (passive : PassiveAtoms values mark) (Φ : Role → (Var → Bool) → Bool)
    (top : ∀ r, Φ r (fun _ => true) = true) :
    (∃ t : Word Role Var, (∀ r A, profile r A t = Φ r A) ∧ Safe values mark t) ↔
      ProfileTests values mark Φ := by
  classical
  constructor
  · rintro ⟨t, he, hs⟩
    exact ⟨fun A h => (exists_safe_meeting_iff values mark passive (.rainbow A)).mp
        ⟨t, fun r => (he r _).trans (h r), hs⟩,
      fun r A B ha hb => (exists_safe_meeting_iff values mark passive (.gap r A B)).mp
        ⟨t, ⟨(he r A).trans ha, (he r B).trans hb⟩, hs⟩⟩
  · intro tests
    let vec (t : Word Role Var) (i : Role × (Var → Bool)) := profile i.1 i.2 t
    let R : Set ((Role × (Var → Bool)) → Bool) := {p | ∃ t, Safe values mark t ∧ vec t = p}
    have closed : ProfileRelations.ChoiceClosed Prod.fst R := by
      rintro q _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      refine ⟨choiceTerm q s t, fun z hit =>
        (WinnerSet.choice_subset_union q _ _ hit).elim (hs z) (ht z), ?_⟩
      funext ⟨r,A⟩
      by_cases he : q = r
      · subst q; simp [vec,profile_choice,ProfileRelations.mixedChoice]
      · simp [vec,profile_choice,ProfileRelations.mixedChoice,he,Ne.symm he]
    let φ (i : Role × (Var → Bool)) := Φ i.1 i.2
    have member (t : Word Role Var) (hs : Safe values mark t) : vec t ∈ R := ⟨t,hs,rfl⟩
    have attained : φ ∈ R := by
      apply (closed.mem_iff_constraints Prod.fst three φ).mpr
      refine ⟨?_,?_,?_⟩
      · rintro ⟨r,B⟩ all
        cases hb : Φ r B with
        | true => exact hb
        | false =>
          obtain ⟨t, ⟨_, hB⟩, hs⟩ := (exists_safe_meeting_iff values mark passive _).mpr
            (tests.2 r _ B (top r) hb)
          exact Bool.noConfusion ((all _ (member t hs)).symm.trans hB)
      · rintro ⟨r,A⟩ ⟨s,B⟩ he all hA
        change r = s at he
        subst s
        cases hb : Φ r B with
        | true => exact hb
        | false =>
          obtain ⟨t, ⟨ha,hB⟩, hs⟩ := (exists_safe_meeting_iff values mark passive _).mpr
            (tests.2 r A B hA hb)
          exact Bool.noConfusion ((all _ (member t hs) ha).symm.trans hB)
      · intro S rainbow forbidden hit
        have pick (r : Role) : ∃ A : Var → Bool, Φ r A = true ∧ ∀ B, (r,B) ∈ S → A = B := by
          by_cases h : ∃ A : Var → Bool, (r,A) ∈ S
          · obtain ⟨A, hA⟩ := h
            exact ⟨A, hit _ hA, fun B hB => congrArg Prod.snd (rainbow _ hA _ hB rfl)⟩
          · exact ⟨fun _ => true,top r,fun B hB => (h ⟨B,hB⟩).elim⟩
        choose A hA hmatch using pick
        obtain ⟨t, meet, hs⟩ := (exists_safe_meeting_iff values mark passive _).mpr (tests.1 A hA)
        apply forbidden _ (member t hs)
        rintro ⟨r,B⟩ hB
        change profile r B t = true
        rw [← hmatch r B hB]
        exact meet r
    obtain ⟨t, hs, eq⟩ := attained
    exact ⟨t, fun r A => congrFun eq (r,A), hs⟩

/-- Several requested winners may be synthesized together with the full
profile and all the omissions. The positives may use arbitrary valuations.
Each needs one eligible source with helpers, and the profile must permit it. -/
theorem exists_safe_profile_hits_iff [DecidableEq Role] [Fintype Role] [Fintype Var] [Fintype Row]
    {Pos : Type*} [Fintype Pos] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (mark : Row → Role) (passive : PassiveAtoms values mark)
    (Φ : Role → (Var → Bool) → Bool) (top : ∀ r, Φ r (fun _ => true) = true)
    (positive : Pos → Var → WinnerSet Role) (wanted : Pos → Role) :
    (∃ t : Word Role Var, (∀ r A, profile r A t = Φ r A) ∧ Safe values mark t ∧
      ∀ p, wanted p ∈ (t.realize (positive p)).val) ↔
      ProfileTests values mark Φ ∧ ∀ p,
        LeafCondition values mark (.win (wanted p) (positive p)) ∧
        ∀ r, Φ r (atomicBits r (positive p)) = true → r = wanted p := by
  classical
  constructor
  · rintro ⟨t, hφ, safe, hit⟩
    refine ⟨(exists_safe_profiles_iff three values mark passive Φ top).mp ⟨t,hφ,safe⟩,
      fun p => ⟨(exists_safe_meeting_iff values mark passive _).mp ⟨t,hit p,safe⟩, ?_⟩⟩
    intro r hr
    have yes : profile r (atomicBits r (positive p)) t = true := (hφ r _).trans hr
    have atom := (winnerSet_eq_singleton_iff_profile t r _).mpr yes
    have hk := hit p
    rw [atom] at hk
    exact hk.symm
  · rintro ⟨tests, requests⟩
    obtain ⟨base, hbase, hsafe⟩ := (exists_safe_profiles_iff three values mark passive Φ top).mpr tests
    have build (S : Finset Pos) : ∃ t : Word Role Var, (∀ r A, profile r A t = Φ r A) ∧
        Safe values mark t ∧ ∀ p ∈ S, wanted p ∈ (t.realize (positive p)).val := by
      induction S using Finset.induction_on with
      | empty => exact ⟨base,hbase,hsafe,by simp⟩
      | insert p S _ ih =>
        obtain ⟨t, hφ, ht, old⟩ := ih
        obtain ⟨s, hit, hs⟩ := (exists_safe_meeting_iff values mark passive _).mpr (requests p).1
        obtain ⟨e, profiles, eval⟩ := exists_profile_reset three s t
        refine ⟨e, fun r A => (profiles r A).trans (hφ r A), ?_, ?_⟩
        · intro z
          rw [eval, WinnerSet.mem_reset]
          exact fun h => h.elim (ht z) (fun extra => hs z extra.2)
        · intro q hq
          rw [eval, WinnerSet.mem_reset]
          rcases Finset.mem_insert.mp hq with rfl | hq
          · by_cases amb : (t.realize (positive q)).Ambiguous
            · exact Or.inr ⟨amb,hit⟩
            · obtain ⟨r, hr⟩ : ∃ r, t.realize (positive q) = WinnerSet.singleton r := by
                simpa only [WinnerSet.Ambiguous, not_forall, not_not] using amb
              have yes := (winnerSet_eq_singleton_iff_profile t r _).mp hr
              have eq := (requests q).2 r ((hφ r _).symm.trans yes)
              exact Or.inl (by simp [hr,eq])
          · exact Or.inl (old q hq)
    obtain ⟨t,hφ,hs,hit⟩ := build Finset.univ
    exact ⟨t,hφ,hs,fun p => hit p (Finset.mem_univ p)⟩

open Sources

/-- Mark a source with the full menu, preserving the passive postings and
leaving every singleton flag at the head false. -/
noncomputable def uncoloredValues (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var) : Var → WinnerSet Role :=
  Function.update (probeAt three q) q.2.1 ⟨Set.univ, ⟨three 0, trivial⟩⟩

private theorem marked_iff (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var) (i : Var) :
    q.1 ∈ (uncoloredValues three q i).val ↔ i = q.2.1 := by
  by_cases he : i = q.2.1
  · simp [uncoloredValues,he]
  · simpa only [uncoloredValues, Function.update_of_ne he, probeAt] using mem_probe_iff three q.1 q.2.1 q.2.2 i

private theorem no_observer_atom (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var) (i : Var) :
    uncoloredValues three q i ≠ WinnerSet.singleton q.1 := by
  intro atom
  have hit : q.1 ∈ (uncoloredValues three q i).val := by rw [atom]; rfl
  obtain rfl := (marked_iff three q i).mp hit
  obtain ⟨r, hr, _⟩ := exists_role_outside_pair three q.1 q.1
  have member : r ∈ (uncoloredValues three q q.2.1).val := by simp [uncoloredValues]
  rw [atom] at member
  exact hr member

/-- Reading the source using a full-menu mark agrees with its canonical
singleton-mark probe. -/
theorem mem_uncolored_iff (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var) (t : Word Role Var) :
    q.1 ∈ (t.realize (uncoloredValues three q)).val ↔ q.1 ∈ (t.realize (probeAt three q)).val := by
  rw [← Equational.Core.eval_decode, membership_iff_source three _ (Equational.Core.isCore_decode t)]
  have hp : pattern q.1 q.2.1 (uncoloredValues three q) = q.2.2 := by
    rw [← pattern_probe three q.1 q.2.1 q.2.2]
    funext i
    change passive q.1 (uncoloredValues three q i.val) = passive q.1 (probeAt three q i.val)
    rw [uncoloredValues,Function.update_of_ne i.property]
  simp only [marked_iff, exists_eq_left, hp, Equational.Core.eval_decode, probeAt]

private theorem no_empty_win (Φ : Role → (Var → Bool) → Bool) (hΦ : AdmissibleProfiles Φ)
    (r : Role) : Φ r (fun _ => false) = false := by
  cases hr : Φ r (fun _ => false) with
  | false => rfl
  | true =>
    let A (s : Role) (_ : Var) := decide (s ≠ r)
    obtain ⟨i, hi⟩ := hΦ.common_source A fun s => by
      by_cases he : s = r
      · simpa [he,A] using hr
      · simpa [he,A] using hΦ.top s
    simpa [A] using hi r

/-- For one head, omitting the minimal forbidden posting sets is equivalent
to omitting every forbidden observation. This applies across different
observers at that head and to any chosen subdomain of colorings. -/
theorem omit_iff_minimal_zeros [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role) (j : Var)
    (Z : Set (ProfileSourceFiber.Observation Role j)) (t : Word Role Var) :
    (∀ q ∈ Z, q.1 ∉ (t.realize (probe three q.1 j q.2)).val) ↔
      ∀ q ∈ Z, Minimal (· ∈ SingleSourceCompletion.postings '' Z) (SingleSourceCompletion.postings q) →
        q.1 ∉ (t.realize (probe three q.1 j q.2)).val := by
  classical
  refine ⟨fun omitAll q hq _ => omitAll q hq, ?_⟩
  intro omitMin q hq hit
  have member : SingleSourceCompletion.postings q ∈ SingleSourceCompletion.postings '' Z := ⟨q,hq,rfl⟩
  obtain ⟨S, hle, hm⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ SingleSourceCompletion.postings '' Z) _ member
  obtain ⟨p, hp, rfl⟩ := hm.prop
  have down := SingleSourceCompletion.supplies_downward (j := j) three (Equational.Core.decode t)
    (Equational.Core.isCore_decode t) p q hle
  simp only [ProfileSourceFiber.Supplies, Equational.Core.eval_decode] at down
  exact omitMin p hp hm (down hit)

/-- On genuine source probes, the positive-winner test only asks that no
negative coloring at that head has all its atom postings present. The
singleton-profile test at each positive reads the postings with its head
uncolored. The finite lists may include all positive and negative probes
of complete coefficient families. -/
theorem uncolored_heads_iff [DecidableEq Role] [Fintype Role] [Fintype Var] [Fintype Row]
    {Pos : Type*} [Fintype Pos] (three : Fin 3 ↪ Role) (neg : Row → ProbeIndex Role Var)
    (pos : Pos → ProbeIndex Role Var)
    (passive : ∀ z i r, uncoloredValues three (neg z) i = WinnerSet.singleton r →
      ∀ y, i ≠ (neg y).2.1)
    (Φ : Role → (Var → Bool) → Bool) (admissible : AdmissibleProfiles Φ) :
    (∃ t : Word Role Var, (∀ r A, profile r A t = Φ r A) ∧
      (∀ z, (neg z).1 ∉ (t.realize (probeAt three (neg z))).val) ∧
      ∀ p, (pos p).1 ∈ (t.realize (probeAt three (pos p))).val) ↔
      ProfileTests (fun z => uncoloredValues three (neg z)) (fun z => (neg z).1) Φ ∧
      ∀ p, (∀ r, Φ r (atomicBits r (uncoloredValues three (pos p))) = false) ∧
        ∀ z, (pos p).2.1 = (neg z).2.1 →
          ∃ r i, uncoloredValues three (neg z) i = WinnerSet.singleton r ∧
            uncoloredValues three (pos p) i ≠ WinnerSet.singleton r := by
  classical
  let V := fun z => uncoloredValues three (neg z)
  let W := fun p => uncoloredValues three (pos p)
  let mark := fun z => (neg z).1
  let k := fun p => (pos p).1
  have safe : PassiveAtoms V mark := fun z i r hr y hit =>
    passive z i r hr y ((marked_iff three (neg y) i).mp hit)
  have tests := exists_safe_profile_hits_iff three V mark safe Φ admissible.top W k
  simp only [Safe, V, mark, W, k, mem_uncolored_iff] at tests
  rw [tests]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  have leaf : LeafCondition V mark (.win (k p) (W p)) ↔ ∀ z, (pos p).2.1 = (neg z).2.1 →
      ∃ r i, V z i = WinnerSet.singleton r ∧ W p i ≠ WinnerSet.singleton r := by
    constructor
    · rintro ⟨i, hi, atLoss⟩ z eq
      have ei := (marked_iff three (pos p) i).mp hi
      obtain ⟨r,a,ha,ok⟩ := atLoss z ((marked_iff three (neg z) i).mpr (ei.trans eq))
      exact ⟨r,a,ha,ok.elim (fun eq => eq ▸ no_observer_atom three (pos p) a) id⟩
    · intro h
      refine ⟨(pos p).2.1,(marked_iff three (pos p) _).mpr rfl,fun z hit => ?_⟩
      obtain ⟨r,i,hr,hn⟩ := h z ((marked_iff three (neg z) _).mp hit)
      exact ⟨r,i,hr,Or.inr hn⟩
  have permit : (∀ r, Φ r (atomicBits r (W p)) = true → r = k p) ↔
      ∀ r, Φ r (atomicBits r (W p)) = false := by
    constructor
    · intro h r
      cases bit : Φ r (atomicBits r (W p)) with
      | false => rfl
      | true =>
        have eq := h r bit
        have empty : atomicBits r (W p) = fun _ => false := by
          funext i
          simp [atomicBits,W,k,eq,no_observer_atom]
        rw [empty,no_empty_win Φ admissible r] at bit
        cases bit
    · intro h r hr
      exact Bool.noConfusion (hr.symm.trans (h r))
  exact (and_congr leaf permit).trans and_comm

end KFOL.Core.PassiveProfileBounds
