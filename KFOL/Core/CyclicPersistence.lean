module

public import KFOL.Definitions.CoreCrown
public import KFOL.Definitions.AtomicObserver
public import KFOL.Core.RoleRestriction
public import KFOL.Core.StatusModel
public import KFOL.Algebra.Views
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases

/-! # Cyclic persistence of a possible winner

The observer's quotient expands into a finite union of lattice polynomials
on the chain b < a < c. At a cyclic row, a is the derivative between a
singleton and an adjacent pair. Finite permutation orbits cannot support
only the oppositely directed derivatives.
-/

@[expose] public section
namespace KFOL.Core.Crown

open WinnerSet WinnerSet.StatusModel

private inductive LatticeExpr (Var : Type*) where
  | var (j : Var)
  | inf (s t : LatticeExpr Var)
  | sup (s t : LatticeExpr Var)
  deriving DecidableEq

private def LatticeExpr.eval {Var : Type*} (v : Var → Fin 3) : LatticeExpr Var → Fin 3
  | .var j => v j
  | .inf s t => min (s.eval v) (t.eval v)
  | .sup s t => max (s.eval v) (t.eval v)

-- Chain indices 0,1,2 mean b,a,c; actual role indices mean a,b,c.
private def decode (i : Fin 3) : Fin 3 := ![1, 0, 2] i

private theorem decode_decode (i : Fin 3) : decode (decode i) = i := by
  fin_cases i <;> rfl

private def viewCode (A : Value (Fin 3)) : Bool × Bool × Bool :=
  (decide (0 ∈ A.val), decide (A = Value.singleton 1), decide (A = Value.singleton 2))

private def pairValue (op : Fin 3 → Fin 3 → Fin 3) (A B : Value (Fin 3)) : Value (Fin 3) :=
  ⟨(A.val ×ˢ B.val).image (fun p => decode (op (decode p.1) (decode p.2))),
    (A.property.product B.property).image _⟩

private theorem viewCode_sound {A B : Value (Fin 3)} (h : viewCode A = viewCode B) :
    SameView 0 A.toWinner B.toWinner := by
  have h0 : (0 ∈ A.val) ↔ 0 ∈ B.val := by
    have hh := congrArg Prod.fst h
    simpa only [viewCode, Prod.fst, decide_eq_decide] using hh
  have h1 : (A = Value.singleton 1) ↔ B = Value.singleton 1 := by
    have hh := congrArg (fun x => x.2.1) h
    simpa only [viewCode, decide_eq_decide] using hh
  have h2 : (A = Value.singleton 2) ↔ B = Value.singleton 2 := by
    have hh := congrArg (fun x => x.2.2) h
    simpa only [viewCode, decide_eq_decide] using hh
  refine ⟨h0, ?_⟩
  intro r hr
  fin_cases r
  · exact (hr rfl).elim
  · simpa [← Value.toWinner_singleton, Value.toWinner_injective.eq_iff] using h1
  · simpa [← Value.toWinner_singleton, Value.toWinner_injective.eq_iff] using h2

set_option maxRecDepth 100000 in
private theorem finite_tables : ∀ A B : Value (Fin 3),
    viewCode (Value.choice 0 A B) = viewCode (Value.union A B) ∧
    viewCode (Value.choice 1 A B) = viewCode (pairValue min A B) ∧
    viewCode (Value.choice 2 A B) = viewCode (pairValue max A B) := by
  decide +kernel

private theorem sameView_trans {Role : Type*} {r : Role} {A B C : WinnerSet Role}
    (h : SameView r A B) (h' : SameView r B C) : SameView r A C :=
  ⟨h.1.trans h'.1, fun k hk => (h.2 k hk).trans (h'.2 k hk)⟩

private noncomputable def familyValue {Var : Type*} (H : Finset (LatticeExpr Var))
    (hH : H.Nonempty) (v : Var → Fin 3) : Value (Fin 3) :=
  ⟨H.image (fun e => decode (e.eval v)), hH.image _⟩

private theorem family_union {Var : Type*} [DecidableEq Var] (H J : Finset (LatticeExpr Var))
    (hH : H.Nonempty) (hJ : J.Nonempty) (v : Var → Fin 3) :
    familyValue (H ∪ J) (hH.mono Finset.subset_union_left) v =
      Value.union (familyValue H hH v) (familyValue J hJ v) := by
  classical
  apply Subtype.ext
  exact Finset.image_union _ _

private theorem family_product {Var : Type*} [DecidableEq Var] (H J : Finset (LatticeExpr Var))
    (hH : H.Nonempty) (hJ : J.Nonempty) (v : Var → Fin 3)
    (op : Fin 3 → Fin 3 → Fin 3) (combine : LatticeExpr Var → LatticeExpr Var → LatticeExpr Var)
    (hc : ∀ e f, (combine e f).eval v = op (e.eval v) (f.eval v)) :
    familyValue ((H ×ˢ J).image (fun p => combine p.1 p.2))
      ((hH.product hJ).image _) v = pairValue op (familyValue H hH v) (familyValue J hJ v) := by
  classical
  apply Subtype.ext
  ext z
  simp only [familyValue, pairValue, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨e, ⟨f, g, ⟨hf, hg⟩, rfl⟩, rfl⟩
    exact ⟨decode (f.eval v), decode (g.eval v),
      ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩, by simp only [decode_decode, hc]⟩
  · rintro ⟨x, y, ⟨⟨e, he, rfl⟩, ⟨f, hf, rfl⟩⟩, rfl⟩
    exact ⟨combine e f, ⟨e, f, ⟨he, hf⟩, rfl⟩,
      by simp only [decode_decode, hc]⟩

private theorem lattice_expansion {Var : Type*} (t : Term (Fin 3) Var) (ht : t.IsCore) :
    ∃ H : Finset (LatticeExpr Var), ∃ hH : H.Nonempty, ∀ v : Var → Fin 3,
      SameView 0 (t.eval (fun j => singleton (decode (v j)))) (familyValue H hH v).toWinner := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j =>
    refine ⟨{.var j}, Finset.singleton_nonempty _, ?_⟩
    intro v
    have he : (familyValue {.var j} (Finset.singleton_nonempty _) v).toWinner =
        singleton (decode (v j)) := by
      apply Subtype.ext
      simp [familyValue, Value.toWinner, LatticeExpr.eval]
    rw [he]
    exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
  | choice r t u iht ihu =>
    obtain ⟨H, hH, hte⟩ := iht ht.1
    obtain ⟨J, hJ, hue⟩ := ihu ht.2
    fin_cases r
    · refine ⟨H ∪ J, hH.mono Finset.subset_union_left, ?_⟩
      intro v
      have h := SameView.choice (hte v) (hue v) 0
      have hh := viewCode_sound (finite_tables (familyValue H hH v) (familyValue J hJ v)).1
      rw [Value.toWinner_choice] at hh
      rw [family_union H J hH hJ v]
      exact sameView_trans h hh
    · let K := (H ×ˢ J).image (fun p => LatticeExpr.inf p.1 p.2)
      refine ⟨K, (hH.product hJ).image _, ?_⟩
      intro v
      have h := SameView.choice (hte v) (hue v) 1
      have hh := viewCode_sound (finite_tables (familyValue H hH v) (familyValue J hJ v)).2.1
      rw [Value.toWinner_choice] at hh
      rw [family_product H J hH hJ v min LatticeExpr.inf (fun _ _ => rfl)]
      exact sameView_trans h hh
    · let K := (H ×ˢ J).image (fun p => LatticeExpr.sup p.1 p.2)
      refine ⟨K, (hH.product hJ).image _, ?_⟩
      intro v
      have h := SameView.choice (hte v) (hue v) 2
      have hh := viewCode_sound (finite_tables (familyValue H hH v) (familyValue J hJ v)).2.2
      rw [Value.toWinner_choice] at hh
      rw [family_product H J hH hJ v max LatticeExpr.sup (fun _ _ => rfl)]
      exact sameView_trans h hh

private def LatticeExpr.predicate {Var : Type*} (S : Set Var) : LatticeExpr Var → Prop
  | .var j => j ∈ S
  | .inf s t => s.predicate S ∧ t.predicate S
  | .sup s t => s.predicate S ∨ t.predicate S

private theorem predicate_mono {Var : Type*} (e : LatticeExpr Var)
    {S T : Set Var} (h : S ⊆ T) : e.predicate S → e.predicate T := by
  induction e with
  | var j => exact fun hj => h hj
  | inf s t ihs iht => exact fun hp => ⟨ihs hp.1, iht hp.2⟩
  | sup s t ihs iht => exact fun hp => hp.elim (fun hs => Or.inl (ihs hs)) (fun ht => Or.inr (iht ht))

private theorem threshold {Var : Type*} (e : LatticeExpr Var) (v : Var → Fin 3) (k : Fin 3) :
    k ≤ e.eval v ↔ e.predicate {j | k ≤ v j} := by
  induction e with
  | var j => rfl
  | inf s t ihs iht => simp only [LatticeExpr.eval, le_min_iff, ihs, iht, LatticeExpr.predicate]
  | sup s t ihs iht => simp only [LatticeExpr.eval, le_max_iff, ihs, iht, LatticeExpr.predicate]

private theorem eval_eq_middle {Var : Type*} (e : LatticeExpr Var) (v : Var → Fin 3) :
    e.eval v = 1 ↔ e.predicate {j | 1 ≤ v j} ∧ ¬e.predicate {j | 2 ≤ v j} := by
  rw [← threshold, ← threshold]
  generalize e.eval v = x
  fin_cases x <;> decide

private def negativeChain {Var : Type*} [DecidableEq Var] (next : Equiv.Perm Var)
    (i j : Var) : Fin 3 := if j = i then 2 else if j = next i then 1 else 0

private def positiveChain {Var : Type*} [DecidableEq Var] (next : Equiv.Perm Var)
    (i j : Var) : Fin 3 := if j = i then 1 else if j = next i then 2 else 0

private theorem negative_cuts {Var : Type*} [DecidableEq Var] (next : Equiv.Perm Var) (i : Var) :
    {j | 1 ≤ negativeChain next i j} = {i, next i} ∧
      {j | 2 ≤ negativeChain next i j} = {i} := by
  constructor <;> ext j <;> by_cases h : j = i <;> by_cases h' : j = next i <;>
    simp_all [negativeChain]

private theorem positive_cuts {Var : Type*} [DecidableEq Var] (next : Equiv.Perm Var)
    (i : Var) (hi : next i ≠ i) :
    {j | 1 ≤ positiveChain next i j} = {i, next i} ∧
      {j | 2 ≤ positiveChain next i j} = {next i} := by
  constructor <;> ext j <;> by_cases h : j = i <;> by_cases h' : j = next i <;>
    simp_all [positiveChain]

private theorem finite_reverse_shift {Var : Type*} [Finite Var] (next : Equiv.Perm Var)
    (P : Var → Prop) (h : ∀ j, P (next j) → P j) : ∀ j, P j → P (next j) := by
  let f : {j // P j} → {j // P j} := fun j =>
    ⟨next.symm j.val, h _ (by simpa only [next.apply_symm_apply] using j.property)⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact next.symm.injective (congrArg Subtype.val he)
  intro j hj
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hf ⟨j, hj⟩
  have he : next.symm x.val = j := congrArg Subtype.val hx
  have hxj : x.val = next j := by simpa only [next.apply_symm_apply] using congrArg next he
  exact hxj ▸ x.property

private theorem lattice_persistence {Var : Type*} [Finite Var] [DecidableEq Var]
    (e : LatticeExpr Var) (next : Equiv.Perm Var) (i : Var) (hi : next i ≠ i)
    (h : ∀ j, e.eval (negativeChain next j) ≠ 1) :
    e.eval (positiveChain next i) ≠ 1 := by
  have hp (j : Var) : e.predicate {j, next j} → e.predicate {j} := by
    intro hpair
    by_contra hs
    apply h j
    rw [eval_eq_middle, (negative_cuts next j).1, (negative_cuts next j).2]
    exact ⟨hpair, hs⟩
  have hshift (j : Var) : e.predicate {next j} → e.predicate {j} := by
    intro hs
    apply hp j
    apply predicate_mono e (S := {next j}) (T := {j, next j}) _ hs
    intro x hx
    exact Or.inr hx
  have hreverse := finite_reverse_shift next (fun j => e.predicate {j}) hshift
  intro he
  have he' := (eval_eq_middle e _).mp he
  rw [(positive_cuts next i hi).1, (positive_cuts next i hi).2] at he'
  exact he'.2 (hreverse i (hp i he'.1))

private theorem mem_familyValue {Var : Type*} (H : Finset (LatticeExpr Var))
    (hH : H.Nonempty) (v : Var → Fin 3) :
    (0 : Fin 3) ∈ (familyValue H hH v).toWinner.val ↔
      ∃ e ∈ H, e.eval v = 1 := by
  have hd (x : Fin 3) : decode x = 0 ↔ x = 1 := by fin_cases x <;> decide
  simp only [familyValue, Value.toWinner, Finset.mem_coe, Finset.mem_image, hd]

private theorem predicate_bot {Var : Type*} (e : LatticeExpr Var) :
    ¬e.predicate ∅ := by
  induction e with
  | var j => simp [LatticeExpr.predicate]
  | inf s t ihs iht => exact fun h => ihs h.1
  | sup s t ihs iht => exact fun h => h.elim ihs iht

private theorem predicate_top {Var : Type*} (e : LatticeExpr Var) :
    e.predicate Set.univ := by
  induction e with
  | var j => trivial
  | inf s t ihs iht => exact ⟨ihs, iht⟩
  | sup s t ihs iht => exact Or.inl ihs

/-- On atomic three-role inputs, an observer trace is a nonempty finite union
of derivatives of monotone nonconstant Boolean functions. -/
theorem atomic_trace_expansion {Var : Type*} [Fintype Var]
    (t : Term (Fin 3) Var) (ht : t.IsCore) :
    ∃ H : Finset (Finset Var → Bool), H.Nonempty ∧
      (∀ φ ∈ H, Monotone φ ∧ φ ∅ = false ∧ φ Finset.univ = true) ∧
      ∀ L U, L ⊆ U →
        ((0 : Fin 3) ∈ (t.eval (AtomicObserver.values
          (Function.Embedding.refl (Fin 3)) L U)).val ↔
          ∃ φ ∈ H, φ L = false ∧ φ U = true) := by
  classical
  obtain ⟨J, hJ, he⟩ := lattice_expansion t ht
  let f (e : LatticeExpr Var) (S : Finset Var) : Bool := decide (e.predicate S)
  refine ⟨J.image f, hJ.image _, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hφ
    refine ⟨?_, ?_, ?_⟩
    · intro S T hST
      apply Bool.le_iff_imp.mpr
      intro hS
      have hh : e.predicate (S : Set Var) := by simpa [f] using hS
      simpa [f] using predicate_mono e (by simpa using hST) hh
    · simpa [f] using predicate_bot e
    · simpa [f] using predicate_top e
  · intro L U hLU
    let v : Var → Fin 3 := fun j => if j ∈ L then 2 else if j ∈ U then 1 else 0
    have hv : AtomicObserver.values (Function.Embedding.refl (Fin 3)) L U =
        fun j => WinnerSet.singleton (decode (v j)) := by
      funext j
      by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
        simp [AtomicObserver.values, v, hL, hU, decode]
    have h1 : {j | (1 : Fin 3) ≤ v j} = (U : Set Var) := by
      ext j
      have hj : j ∈ L → j ∈ U := fun h => hLU h
      by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
        simp_all [v]
    have h2 : {j | (2 : Fin 3) ≤ v j} = (L : Set Var) := by
      ext j
      by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
        simp [v, hL, hU]
    rw [hv, (he v).1, mem_familyValue]
    simp only [Finset.mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨e, heJ, heval⟩
      have hh := (eval_eq_middle e v).mp heval
      rw [h1, h2] at hh
      exact ⟨e, heJ, by simpa [f] using hh.2, by simpa [f] using hh.1⟩
    · rintro ⟨e, heJ, hL, hU⟩
      refine ⟨e, heJ, (eval_eq_middle e v).mpr ?_⟩
      rw [h1, h2]
      exact ⟨by simpa [f] using hU, by simpa [f] using hL⟩

private theorem negative_eq_chain {Var : Type*} [DecidableEq Var]
    (next : Equiv.Perm Var) (i : Var) :
    negative (Function.Embedding.refl (Fin 3)) next i =
      fun j => singleton (decode (negativeChain next i j)) := by
  funext j
  by_cases h : j = i <;> by_cases h' : j = next i <;>
    simp_all [negative, negativeChain, decode]

private theorem positive_eq_chain {Var : Type*} [DecidableEq Var]
    (next : Equiv.Perm Var) (i : Var) :
    positive (Function.Embedding.refl (Fin 3)) next i =
      fun j => singleton (decode (positiveChain next i j)) := by
  funext j
  by_cases h : j = i <;> by_cases h' : j = next i <;>
    simp_all [positive, positiveChain, decode]

private theorem small_persistence {Var : Type*} [Finite Var] (next : Equiv.Perm Var)
    (i : Var) (hi : next i ≠ i) (t : Term (Fin 3) Var) (ht : t.IsCore) :
    (0 : Fin 3) ∈ (t.eval (positive (Function.Embedding.refl _) next i)).val →
      ∃ j, (0 : Fin 3) ∈ (t.eval (negative (Function.Embedding.refl _) next j)).val := by
  classical
  obtain ⟨H, hH, he⟩ := lattice_expansion t ht
  intro hq
  rw [positive_eq_chain] at hq
  have hq' := ((he (positiveChain next i)).1).mp hq
  obtain ⟨e, heH, heq⟩ := (mem_familyValue H hH _).mp hq'
  by_contra hn
  have hnegative (j : Var) : e.eval (negativeChain next j) ≠ 1 := by
    intro hj
    apply hn
    refine ⟨j, ?_⟩
    rw [negative_eq_chain]
    exact ((he _).1).mpr ((mem_familyValue H hH _).mpr ⟨e, heH, hj⟩)
  exact lattice_persistence e next i hi hnegative heq

/-- A possible a-winner at an oppositely oriented cyclic row forces an
 a-winner at some forward row. Every finite permutation is allowed. -/
theorem persistence {Role Var : Type*} [Finite Var] (three : Fin 3 ↪ Role)
    (next : Equiv.Perm Var) (i : Var) (hi : next i ≠ i)
    (t : Term Role Var) (ht : t.IsCore) :
    three 0 ∈ (t.eval (positive three next i)).val →
      ∃ j, three 0 ∈ (t.eval (negative three next j)).val := by
  classical
  obtain ⟨s, hs, he⟩ := Core.exists_role_restriction three
    (Function.Embedding.refl (Fin 3)) t ht
  have hn (j : Var) : negative three next j = fun x =>
      expand (fun r => singleton (three r)) (negative (Function.Embedding.refl _) next j x) := by
    funext x
    by_cases h : x = j <;> by_cases h' : x = next j <;> simp_all [negative]
  have hp : positive three next i = fun x =>
      expand (fun r => singleton (three r)) (positive (Function.Embedding.refl _) next i x) := by
    funext x
    by_cases h : x = i <;> by_cases h' : x = next i <;> simp_all [positive]
  intro hq
  have hsmall : (0 : Fin 3) ∈ (s.eval (positive (Function.Embedding.refl _) next i)).val := by
    apply (mem_expand_embedding three _ 0).mp
    rw [← he, ← hp]
    exact hq
  obtain ⟨j, hj⟩ := small_persistence next i hi s hs hsmall
  refine ⟨j, ?_⟩
  rw [hn, he]
  exact (mem_expand_embedding three _ 0).mpr hj

end KFOL.Core.Crown
