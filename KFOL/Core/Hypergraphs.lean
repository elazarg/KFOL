module

public import KFOL.Definitions.CoreHypergraphs
public import KFOL.Core.OwnerEliminationComplete
public import KFOL.Core.SourceCertificates
public import KFOL.Core.SourcePeeling
public import KFOL.Core.SourceCompatibility

/-! # A complete relational basis specified by colored hypergraph cuts

An indexed clutter is admissible by boundary incidences and the no-trap
subset condition alone. Its clause relation is core-invariant, and every
finite core-invariant relation has such a presentation.
-/

@[expose] public section
namespace KFOL.Core.Hypergraphs
open WinnerSet OwnerElimination
universe u v
variable {Row : Type u} {Role : Type v}
variable [DecidableEq Row] [DecidableEq Role] [Fintype Row] [Fintype Role]

private def clauses (D : Diagram Row Role) : Finset (Clause Row Role) :=
  Finset.univ.biUnion fun p => (D.heads p).image (Clause.mk p)

private theorem mem_clauses (D : Diagram Row Role) (C : Clause Row Role) :
    C ∈ clauses D ↔ C.head ∈ D.heads C.premise := by
  simp only [clauses, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨p,H,hH,hC⟩
    cases hC
    exact hH
  · intro h
    exact ⟨C.premise,C.head,h,by cases C; rfl⟩

private theorem models_iff (D : Diagram Row Role) (x : Row → Set Role) :
    D.Models x ↔ SatisfiesSets (clauses D) x := by
  constructor
  · intro h C hC
    exact h C.premise C.head ((mem_clauses D C).mp hC)
  · intro h p H hH
    exact h ⟨p,H⟩ ((mem_clauses D _).mpr hH)

private theorem supports_iff {D : Diagram Row Role} (hb : D.Boundary)
    (C : Clause Row Role) : supports (clauses D) C = true ↔ D.Supports C.premise C.head := by
  simp only [supports, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (ht | ⟨E,hE,hsub⟩)
    · cases hp : C.premise with
      | none => simp [Clause.tautology,hp] at ht
      | some p => exact hp ▸ hb.2.2 p C.head (by simpa [Clause.tautology,hp] using ht)
    · have he : D.Supports E.premise C.head :=
        ⟨E.head,(mem_clauses D E).mp hE,hsub.2⟩
      rcases hsub.1 with hn | hs
      · rw [hn] at he
        cases hp : C.premise with
        | none => exact hp ▸ he
        | some p => exact hp ▸ hb.2.1 p C.head he
      · exact hs ▸ he
  · rintro ⟨H,hH,hHC⟩
    right
    exact ⟨⟨C.premise,H⟩,(mem_clauses D _).mpr hH,Or.inr rfl,hHC⟩

private theorem blocker_iff {D : Diagram Row Role} (hb : D.Boundary)
    (p : Option (Atom Row Role)) (H S : Finset (Atom Row Role)) (r : Role) (i : Row) :
    checkBlocker (clauses D) ⟨p,H⟩ r S i = true ↔ D.Blocker p r S i := by
  cases p with
  | none => exact supports_iff hb _
  | some a =>
    by_cases ha : a.2 = r
    · simpa [checkBlocker,Diagram.Blocker,ha] using
        (supports_iff hb (⟨none,blockHead S i r⟩ : Clause Row Role))
    · simp only [checkBlocker,Diagram.Blocker,ha,ite_false,decide_eq_true_eq]
      constructor
      · intro h s hs
        exact (supports_iff hb _).mp (h s (by simp [hs]))
      · intro h s hs
        exact (supports_iff hb _).mpr (h s (Finset.mem_erase.mp hs).1)

private theorem admissible_orders {D : Diagram Row Role} (hd : D.Admissible) :
    ∃ orders, checkFamily (clauses D) orders = true := by
  classical
  have step (C : Clause Row Role) (hC : C ∈ clauses D) (r : Role)
      (S : Finset (Atom Row Role)) (hi : initial C r ⊆ S) (hS : S ⊆ C.head) :
      ∃ order, checkSteps (clauses D) C r S order = true := by
    generalize hn : (C.head \ S).card = n
    induction n using Nat.strong_induction_on generalizing S with
    | h n ih =>
      by_cases he : S = C.head
      · subst S
        refine ⟨[],(supports_iff hd.1 C).mpr ?_⟩
        exact ⟨C.head,(mem_clauses D C).mp hC,Finset.Subset.refl _⟩
      · have hproper : S ⊂ C.head := Finset.ssubset_iff_subset_ne.mpr ⟨hS,he⟩
        obtain ⟨a,ha,haS,hblock⟩ := hd.2 C.premise C.head
          ((mem_clauses D C).mp hC) r S hi hproper
        have har : a.2 ≠ r := by
          intro heq
          exact haS (hi (Finset.mem_filter.mpr ⟨ha,heq⟩))
        have hlt : (C.head \ insert a S).card < n := by
          rw [Finset.sdiff_insert,← hn]
          exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨ha,haS⟩)
        obtain ⟨rest,hr⟩ := ih _ hlt (insert a S)
          (fun p hp => Finset.mem_insert_of_mem (hi hp))
          (Finset.insert_subset ha hS) rfl
        refine ⟨a :: rest, ?_⟩
        simp only [checkSteps,Bool.and_eq_true,decide_eq_true_eq]
        exact ⟨⟨⟨ha,haS,har⟩,(blocker_iff hd.1 _ _ _ _ _).mpr hblock⟩,hr⟩
  have ex (C : Clause Row Role) (r : Role) :
      ∃ order, C ∈ clauses D → checkSteps (clauses D) C r (initial C r) order = true := by
    by_cases hC : C ∈ clauses D
    · obtain ⟨order,ho⟩ := step C hC r (initial C r) (Finset.Subset.refl _) (Finset.filter_subset _ _)
      exact ⟨order,fun _ => ho⟩
    · exact ⟨[],fun h => (hC h).elim⟩
  choose orders ho using ex
  exact ⟨orders,by simpa only [checkFamily,decide_eq_true_eq] using
    (show ∀ C ∈ clauses D, ∀ r, checkSteps (clauses D) C r (initial C r) (orders C r) = true
      from fun C hC r => ho C r hC)⟩

/-- Every relation specified by the closed clutter axioms is core-invariant. -/
theorem admissible_choiceClosed {D : Diagram Row Role} (hd : D.Admissible) :
    ChoiceClosed (fun x : Row → WinnerSet Role => D.Models (fun i => (x i).val)) := by
  obtain ⟨orders,ho⟩ := admissible_orders hd
  intro r x y hx hy
  exact (models_iff D _).mpr (choice_preserves ho ((models_iff D _).mp hx)
    ((models_iff D _).mp hy) r)

private noncomputable def validHeads (R : (Row → WinnerSet Role) → Prop)
    (p : Option (Atom Row Role)) : Finset (Finset (Atom Row Role)) := by
  classical
  exact Finset.univ.filter (fun H => ∀ x, R x → (Clause.mk p H).Holds x)

private noncomputable def canonical (R : (Row → WinnerSet Role) → Prop) : Diagram Row Role where
  heads p := (validHeads R p).filter fun H =>
    ∀ J ∈ validHeads R p, J ⊆ H → H ⊆ J
  antichain := by
    classical
    intro p H hH J hJ hHJ
    exact Finset.Subset.antisymm hHJ ((Finset.mem_filter.mp hJ).2 H
      (Finset.mem_filter.mp hH).1 hHJ)

private theorem canonical_support (R : (Row → WinnerSet Role) → Prop)
    (p : Option (Atom Row Role)) (H : Finset (Atom Row Role)) :
    (canonical R).Supports p H ↔ ∀ x, R x → (Clause.mk p H).Holds x := by
  classical
  constructor
  · rintro ⟨J,hJ,hJH⟩ x hx hp
    have hv := (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2 x hx hp
    obtain ⟨a,ha,hm⟩ := hv
    exact ⟨a,hJH ha,hm⟩
  · intro hv
    let below := (validHeads R p).filter (fun J => J ⊆ H)
    have hh : H ∈ below := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,Finset.Subset.refl _⟩
    obtain ⟨J,hJ,hmin⟩ := Finset.exists_min_image below (fun J => J.card) ⟨H,hh⟩
    refine ⟨J,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hJ).1,?_⟩,
      (Finset.mem_filter.mp hJ).2⟩
    intro L hL hLJ
    have hLb : L ∈ below := Finset.mem_filter.mpr ⟨hL,
      hLJ.trans (Finset.mem_filter.mp hJ).2⟩
    exact Finset.eq_of_subset_of_card_le hLJ (hmin L hLb) |>.symm.le

private theorem canonical_boundary (R : (Row → WinnerSet Role) → Prop) :
    (canonical R).Boundary := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro i
    apply (canonical_support R _ _).mpr
    intro x _ _
    obtain ⟨r,hr⟩ := (x i).property
    exact ⟨(i,r),Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,hr⟩
  · intro p H h
    apply (canonical_support R _ _).mpr
    intro x hx _
    exact (canonical_support R _ _).mp h x hx trivial
  · intro p H hp
    apply (canonical_support R _ _).mpr
    intro x _ hm
    exact ⟨p,hp,hm⟩

private theorem canonical_complete (R : (Row → WinnerSet Role) → Prop) :
    CompleteFor (clauses (canonical R)) R := by
  intro C
  exact (supports_iff (canonical_boundary R) C).trans
    (by cases C; exact canonical_support R _ _)

private theorem canonical_admissible {R : (Row → WinnerSet Role) → Prop}
    (hc : ChoiceClosed R) : (canonical R).Admissible := by
  classical
  refine ⟨canonical_boundary R,?_⟩
  intro p H hH r S hi hS
  have hvalid : ∀ x, R x → (Clause.mk p H).Holds x :=
    (canonical_support R p H).mp ⟨H,hH,Finset.Subset.refl _⟩
  obtain ⟨order,ho⟩ := exists_checked_order hc (canonical_complete R) ⟨p,H⟩ hvalid r S hi
  cases order with
  | nil =>
    have hsupp := (supports_iff (canonical_boundary R) ⟨p,S⟩).mp ho
    obtain ⟨J,hJ,hJS⟩ := hsupp
    have he := (canonical R).antichain p J hJ H hH (hJS.trans (Finset.ssubset_iff_subset_ne.mp hS).1)
    exact ((Finset.ssubset_iff_subset_ne.mp hS).2
      (Finset.Subset.antisymm (Finset.ssubset_iff_subset_ne.mp hS).1 (he ▸ hJS))).elim
  | cons a rest =>
    simp only [checkSteps,Bool.and_eq_true,decide_eq_true_eq] at ho
    exact ⟨a,ho.1.1.1,ho.1.1.2.1,
      (blocker_iff (canonical_boundary R) p H S r a.1).mp ho.1.2⟩

/-- Every finite core-invariant relation has a presentation by the two closed
colored-clutter conditions. The equality includes raw empty row coordinates. -/
theorem choiceClosed_iff_hypergraphs (three : Fin 3 ↪ Role)
    (R : (Row → WinnerSet Role) → Prop) :
    ChoiceClosed R ↔ ∃ D : Diagram Row Role, D.Admissible ∧
      ∀ x : Row → Set Role,
        (∃ y : Row → WinnerSet Role, R y ∧ ∀ i, (y i).val = x i) ↔ D.Models x := by
  constructor
  · intro hc
    let D := canonical R
    have hd : D.Admissible := canonical_admissible hc
    refine ⟨D,hd,?_⟩
    intro x
    constructor
    · rintro ⟨y,hy,he⟩
      apply (models_iff D x).mpr
      intro C hC
      have hv := (canonical_complete R C).mp
        ((supports_iff hd.1 C).mpr ⟨C.head,(mem_clauses D C).mp hC,Finset.Subset.refl _⟩) y hy
      simpa only [Clause.HoldsSets,Clause.Holds,Clause.Premise,Clause.Head,← he] using hv
    · intro hx
      have hne (i : Row) : (x i).Nonempty := by
        obtain ⟨H,hH,hHE⟩ := hd.1.1 i
        obtain ⟨a,ha,hm⟩ := hx none H hH trivial
        obtain ⟨r,_,he⟩ := Finset.mem_image.mp (hHE ha)
        subst a
        exact ⟨r,hm⟩
      let y : Row → WinnerSet Role := fun i => ⟨x i,hne i⟩
      refine ⟨y,?_,fun _ => rfl⟩
      apply (complete_family_models (canonical_complete R) ?_ (hc.union three) y).mpr
      · exact (models_iff D x).mp hx
      · intro C hC
        exact (canonical_complete R C).mp
          ((supports_iff hd.1 C).mpr ⟨C.head,(mem_clauses D C).mp hC,Finset.Subset.refl _⟩)
  · rintro ⟨D,hd,hm⟩ r x y hx hy
    have lift (z : Row → WinnerSet Role) : R z ↔ D.Models (fun i => (z i).val) := by
      rw [← hm]
      constructor
      · intro hz; exact ⟨z,hz,fun _ => rfl⟩
      · rintro ⟨w,hw,he⟩
        have hwz : w = z := funext (fun i => Subtype.ext (he i))
        exact hwz ▸ hw
    exact (lift _).mpr (admissible_choiceClosed hd r x y ((lift x).mp hx) ((lift y).mp hy))

/-- Universal preservation of the explicitly specified colored-hypergraph
schemas recognizes finite raw tables, including empty values and no variables. -/
theorem finite_sample_iff_hypergraphs {Var : Type*} (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (target : Row → Set Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ i, (t.eval (values i)).val = target i) ↔
      ∀ D : Diagram Row Role, D.Admissible →
        (∀ j, D.Models (fun i => (values i j).val)) → D.Models target := by
  constructor
  · rintro ⟨t,ht,he⟩ D hd hcolumns
    obtain ⟨orders,ho⟩ := admissible_orders hd
    have hh := core_preserves ho (fun j i => values i j)
      (fun j => (models_iff D _).mp (hcolumns j)) t ht
    apply (models_iff D target).mpr
    have hhraw : SatisfiesSets (clauses D) (fun i => (t.eval (values i)).val) := hh
    simpa only [he] using hhraw
  · intro h
    let R : (Row → WinnerSet Role) → Prop := fun x =>
      ∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = x i
    have hc : ChoiceClosed R := by
      rintro r x y ⟨s,hs,hes⟩ ⟨t,ht,het⟩
      exact ⟨.choice r s t,⟨hs,ht⟩,fun i => by simp only [Term.eval,hes,het]⟩
    obtain ⟨D,hd,hm⟩ := (choiceClosed_iff_hypergraphs three R).mp hc
    have ht := h D hd (fun j => (hm _).mp
      ⟨fun i => values i j,⟨.var j,trivial,fun _ => rfl⟩,fun _ => rfl⟩)
    obtain ⟨y,⟨t,ht,he⟩,hy⟩ := (hm target).mpr ht
    exact ⟨t,ht,fun i => by rw [he i,hy i]⟩

/-- The clutters specified by the two closed set axioms form a complete
relational basis for all finite-arity core operations. -/
theorem operation_iff_hypergraphs {Var : Type*} [Fintype Var]
    (three : Fin 3 ↪ Role) (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔
      ∀ m : ℕ, ∀ D : Diagram (Fin m) Role, D.Admissible →
        ∀ values : Fin m → Var → WinnerSet Role,
          (∀ j, D.Models (fun i => (values i j).val)) →
            D.Models (fun i => (f (values i)).val) := by
  classical
  constructor
  · rintro ⟨t,ht,he⟩ m D hd values hcolumns
    exact (finite_sample_iff_hypergraphs three values (fun i => (f (values i)).val)).mp
      ⟨t,ht,fun i => congrArg Subtype.val (he (values i))⟩ D hd hcolumns
  · intro h
    let e := Fintype.equivFin (Var → WinnerSet Role)
    let values : Fin (Fintype.card (Var → WinnerSet Role)) → Var → WinnerSet Role := e.symm
    obtain ⟨t,ht,he⟩ :=
      (finite_sample_iff_hypergraphs three values (fun i => (f (values i)).val)).mpr
        (fun D hd hcolumns => h _ D hd values hcolumns)
    refine ⟨t,ht,fun v => Subtype.ext ?_⟩
    simpa only [values,Equiv.symm_apply_apply] using he (e v)

/-- A positive observation has a witness avoiding the given negative atoms
exactly when no admissible clutter supports the contrary persistence clause. -/
theorem membership_query_iff_hypergraphs {Var : Type*}
    (values : Row → Var → WinnerSet Role) (p : Atom Row Role)
    (negative : Finset (Atom Row Role)) :
    (∃ t : Term Role Var, t.IsCore ∧ p.2 ∈ (t.eval (values p.1)).val ∧
      ∀ a ∈ negative, a.2 ∉ (t.eval (values a.1)).val) ↔
      ∀ D : Diagram Row Role, D.Admissible →
        (∀ j, D.Models (fun i => (values i j).val)) →
          ¬D.Supports (some p) negative := by
  constructor
  · rintro ⟨t,ht,hp,hn⟩ D hd hcolumns hs
    obtain ⟨orders,ho⟩ := admissible_orders hd
    have hmodels := core_preserves ho (fun j i => values i j)
      (fun j => (models_iff D _).mp (hcolumns j)) t ht
    have hc := supports_sound ((supports_iff hd.1 ⟨some p,negative⟩).mpr hs) hmodels
    obtain ⟨a,ha,hm⟩ := hc hp
    exact hn a ha hm
  · intro h
    let R : (Row → WinnerSet Role) → Prop := fun x =>
      ∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = x i
    have hc : ChoiceClosed R := by
      rintro r x y ⟨s,hs,hes⟩ ⟨t,ht,het⟩
      exact ⟨.choice r s t,⟨hs,ht⟩,fun i => by simp only [Term.eval,hes,het]⟩
    have hcolumns (j : Var) : (canonical R).Models (fun i => (values i j).val) := by
      intro stem H hH
      exact (canonical_support R stem H).mp ⟨H,hH,Finset.Subset.refl _⟩
        (fun i => values i j) ⟨.var j,trivial,fun _ => rfl⟩
    have hn := h (canonical R) (canonical_admissible hc) hcolumns
    by_contra hnone
    apply hn
    apply (canonical_support R (some p) negative).mpr
    rintro x ⟨t,ht,he⟩ hp
    by_contra hhead
    apply hnone
    refine ⟨t,ht,?_,?_⟩
    · simpa only [Clause.Premise,he] using hp
    · intro a ha hm
      exact hhead ⟨a,ha,by simpa only [he] using hm⟩

end KFOL.Core.Hypergraphs

namespace KFOL.Core.Sources
open WinnerSet Hypergraphs
open scoped Classical
variable {Role Var : Type*}

/-- Canonical guard tables satisfy a complete universal family of closed
colored-hypergraph schemas. Raw empty probe values are included. -/
theorem guard_table_iff_hypergraphs [Fintype Role] [DecidableEq Role]
    [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧
      ∀ D : Diagram (ProbeIndex Role Var) Role, D.Admissible →
        (∀ j, D.Models (fun q => (probeAt three q j).val)) →
          D.Models (fun q => meaning G (probeAt three q)) := by
  classical
  rw [guard_table_iff_checked_clauses]
  apply and_congr_right
  intro _
  exact (OwnerElimination.finite_sample_sets_iff_checked_clauses three
    (fun q : ProbeIndex Role Var => probeAt three q)
    (fun q => meaning G (probeAt three q))).symm.trans
      (finite_sample_iff_hypergraphs three _ _)

/-- Closed persistence conditions on the guards' own positive and negative
source observations. There are no auxiliary orders, witnesses, or closures
in the right side; the only existential asks for a positive guard bit. -/
theorem guard_table_iff_hypergraph_persistence [Fintype Role] [DecidableEq Role]
    [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧
      (∃ q : ProbeIndex Role Var, coefficients G q.1 q.2.1 q.2.2) ∧
      ∀ q : ProbeIndex Role Var, coefficients G q.1 q.2.1 q.2.2 →
        ∀ D : Diagram (ProbeIndex Role Var) Role, D.Admissible →
          (∀ j, D.Models (fun z => (probeAt three z j).val)) →
            ¬D.Supports (some (q,q.1))
              ((negativeProbes G).image (fun z => (z,z.1))) := by
  classical
  let N := (negativeProbes G).image (fun z => (z,z.1))
  have bounded (t : Term Role Var)
      (hn : ∀ a ∈ N, a.2 ∉ (t.eval (probeAt three a.1)).val) :
      Interpolation.Bounded (negativeProbes G) exclusionBounds
        (fun q => t.eval (probeAt three q)) := by
    intro q hq r hr he
    subst r
    exact hn (q,q.1) (Finset.mem_image.mpr ⟨q,hq,rfl⟩) hr
  constructor
  · rintro ⟨t,ht,hnf⟩
    have hc := ((guard_table_iff_hypergraphs three G).mp ⟨t,ht,hnf⟩).1
    have he (q : ProbeIndex Role Var) :
        q.1 ∈ (t.eval (probeAt three q)).val ↔ coefficients G q.1 q.2.1 q.2.2 := by
      rw [← hnf]
      exact coefficient_iff_guard three t q.1 q.2.1 q.2.2
    obtain ⟨k,j,p,hpos⟩ := exists_positive_probe three t ht
    refine ⟨hc,⟨⟨k,j,p⟩,(he ⟨k,j,p⟩).mp hpos⟩,?_⟩
    intro q hq
    apply (membership_query_iff_hypergraphs (fun z => probeAt three z) (q,q.1) N).mp
    refine ⟨t,ht,(he q).mpr hq,?_⟩
    intro a ha
    obtain ⟨z,hz,hza⟩ := Finset.mem_image.mp ha
    subst a
    intro hm
    have hn : ¬coefficients G z.1 z.2.1 z.2.2 := by
      simpa only [negativeProbes,Finset.mem_filter,Finset.mem_univ,true_and] using hz
    exact hn ((he z).mp hm)
  · rintro ⟨hc,⟨q0,hq0⟩,hpersist⟩
    have witness (q : ProbeIndex Role Var) (hq : coefficients G q.1 q.2.1 q.2.2) :
        ∃ t : Term Role Var, t.IsCore ∧
          Interpolation.Bounded (negativeProbes G) exclusionBounds
            (fun z => t.eval (probeAt three z)) ∧ q.1 ∈ (t.eval (probeAt three q)).val := by
      obtain ⟨t,ht,hp,hn⟩ :=
        (membership_query_iff_hypergraphs (fun z => probeAt three z) (q,q.1) N).mpr
          (hpersist q hq)
      exact ⟨t,ht,bounded t hn,hp⟩
    apply (guard_table_iff_negative_peels three G).mpr
    refine ⟨hc,?_,?_⟩
    · obtain ⟨t,ht,hb,_⟩ := witness q0 hq0
      apply (Interpolation.peels_iff three _ _ _ _ _).mpr
      exact ⟨t,ht,hb,by intro d hd; exact (Finset.notMem_empty _ hd).elim,trivial⟩
    · intro q hq
      obtain ⟨t,ht,hb,hp⟩ := witness q hq
      apply (Interpolation.peels_iff three _ _ _ _ _).mpr
      exact ⟨t,ht,hb,by intro d hd; exact (Finset.notMem_empty _ hd).elim,hp⟩

end KFOL.Core.Sources
