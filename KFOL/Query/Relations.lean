module

public import KFOL.Definitions.Queries
public import KFOL.Algebra.ChoiceSupport
public import KFOL.Core.ChoiceUnion.Laws
public import KFOL.Algebra.SemilatticeTrace
public import KFOL.Reset.Basic
public import Mathlib.Logic.Relation

/-! # Relational representation and expressive boundaries for winner queries -/

@[expose] public section
namespace KFOL.Query
universe u v
variable {Role : Type u}

/-- Separately union-preserving owned choice is determined by its atomic
columns. The family of inputs can be infinite. -/
theorem mem_choice_columns (owner : Role) (A B : WinnerSet Role) (k : Role) :
    k ∈ (WinnerSet.choice owner A B).val ↔
      ∃ b ∈ B.val, k ∈ (WinnerSet.choice owner A (WinnerSet.singleton b)).val := by
  classical
  by_cases ha : A = WinnerSet.singleton owner
  · subst A
    simp only [WinnerSet.choice, true_or, ite_true, WinnerSet.val_singleton,
      Set.mem_singleton_iff]
    constructor
    · intro h; obtain ⟨b,hb⟩ := B.property; exact ⟨b,hb,h⟩
    · rintro ⟨_,_,h⟩; exact h
  by_cases hb : B = WinnerSet.singleton owner
  · subst B
    simp only [WinnerSet.val_singleton, Set.mem_singleton_iff, exists_eq_left]
  have hn : ¬(A = WinnerSet.singleton owner ∨ B = WinnerSet.singleton owner) := not_or.mpr ⟨ha,hb⟩
  rw [WinnerSet.choice, ite_eq_right hn]
  constructor
  · rintro (hk | hk)
    · obtain ⟨b,hb,hbo⟩ := WinnerSet.exists_mem_ne_of_ne_singleton owner B hb
      refine ⟨b,hb,?_⟩
      simp only [WinnerSet.choice, ha, WinnerSet.singleton_inj, hbo, or_self, ite_false,
        WinnerSet.val_union, WinnerSet.val_singleton, Set.mem_union]
      exact Or.inl hk
    · refine ⟨k,hk,?_⟩
      by_cases hko : k = owner
      · subst k
        simp [WinnerSet.choice]
      · simp only [WinnerSet.choice, ha, WinnerSet.singleton_inj, hko, or_self, ite_false,
          WinnerSet.val_union, WinnerSet.val_singleton, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inr trivial
  · rintro ⟨b,hb,hk⟩
    rcases WinnerSet.choice_subset_union owner A (WinnerSet.singleton b) hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr ((Set.mem_singleton_iff.mp hk) ▸ hb)

theorem relation_injective (owner : Role) : Function.Injective (relation owner) := by
  intro A B equal
  apply Subtype.ext
  ext r
  exact Iff.of_eq (congrFun (congrFun equal none) (some r))

theorem relation_union (owner : Role) (A B : WinnerSet Role) :
    relation owner (A.union B) = fun x y => relation owner A x y ∨ relation owner B x y := by
  funext x y
  cases y with
  | none => simp only [relation, or_self]
  | some y =>
    cases x with
    | none => rfl
    | some x =>
      change (y ∈ (WinnerSet.choice owner (A.union B) (WinnerSet.singleton x)).val) = _
      rw [WinnerSet.choice_comm, Dissemilattice.winner_mul_add]
      simp only [WinnerSet.val_union, Set.mem_union,
        WinnerSet.choice_comm (WinnerSet.singleton x), relation]

theorem relation_choice (owner : Role) (A B : WinnerSet Role) :
    relation owner (WinnerSet.choice owner A B) = Relation.Comp (relation owner A) (relation owner B) := by
  funext x y
  apply propext
  cases y with
  | none =>
    change False ↔ ∃ middle, relation owner A x middle ∧ False
    simp only [and_false, exists_false]
  | some k =>
    have middle (C : WinnerSet Role) :
        (∃ mid : Option Role, (match mid with | none => False | some j => j ∈ C.val) ∧
          relation owner B mid (some k)) ↔
        ∃ j ∈ C.val, k ∈ (WinnerSet.choice owner B (WinnerSet.singleton j)).val := by
      constructor
      · rintro ⟨mid,hm,hk⟩
        cases mid with
        | none => cases hm
        | some j => exact ⟨j,hm,hk⟩
      · rintro ⟨j,hj,hk⟩; exact ⟨some j,hj,hk⟩
    cases x with
    | none =>
      change k ∈ (WinnerSet.choice owner A B).val ↔ _
      rw [WinnerSet.choice_comm A B, mem_choice_columns]
      exact (middle A).symm
    | some i =>
      change k ∈ (WinnerSet.choice owner (WinnerSet.choice owner A B) (WinnerSet.singleton i)).val ↔ _
      have equal : WinnerSet.choice owner (WinnerSet.choice owner A B) (WinnerSet.singleton i) =
          WinnerSet.choice owner B (WinnerSet.choice owner A (WinnerSet.singleton i)) := by
        rw [WinnerSet.choice_comm A B, WinnerSet.choice_assoc]
      rw [equal, mem_choice_columns]
      exact (middle (WinnerSet.choice owner A (WinnerSet.singleton i))).symm

theorem relational_representation (owner : Role) :
    Function.Injective (relation owner) ∧
    (∀ A B : WinnerSet Role, relation owner (A.union B) =
      fun x y => relation owner A x y ∨ relation owner B x y) ∧
    ∀ A B : WinnerSet Role, relation owner (WinnerSet.choice owner A B) =
      Relation.Comp (relation owner A) (relation owner B) :=
  ⟨relation_injective owner, relation_union owner, relation_choice owner⟩

private theorem pair_ambiguous (a b : Role) (different : a ≠ b) :
    ((WinnerSet.singleton a).union (WinnerSet.singleton b)).Ambiguous := by
  intro r equal
  obtain ⟨ha,hb⟩ := (WinnerSet.union_eq_singleton_iff _ _ _).mp equal
  exact different ((WinnerSet.singleton_inj.mp ha).trans (WinnerSet.singleton_inj.mp hb).symm)

theorem reset_not_distributive (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (WinnerSet.singleton c).reset ((WinnerSet.singleton a).union (WinnerSet.singleton b)) ≠
      ((WinnerSet.singleton c).reset (WinnerSet.singleton a)).union
        ((WinnerSet.singleton c).reset (WinnerSet.singleton b)) := by
  rw [WinnerSet.reset_of_ambiguous _ _ (pair_ambiguous a b hab),
    WinnerSet.reset_singleton, WinnerSet.reset_singleton]
  intro equal
  have present : c ∈ ((WinnerSet.singleton c).union
      ((WinnerSet.singleton a).union (WinnerSet.singleton b))).val := Or.inl rfl
  rw [equal] at present
  exact present.elim (fun h => hac (Set.mem_singleton_iff.mp h).symm)
    (fun h => hbc (Set.mem_singleton_iff.mp h).symm)

/-- A failure of distributivity rules out every faithful union/composition
representation, not only the particular regular representation above. -/
theorem no_reset_relational_representation (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Node : Type v) :
    ¬∃ encode : WinnerSet Role → Node → Node → Prop, Function.Injective encode ∧
      (∀ A B, encode (A.union B) = fun x y => encode A x y ∨ encode B x y) ∧
      ∀ A B, encode (A.reset B) = Relation.Comp (encode A) (encode B) := by
  rintro ⟨encode, injective, add, mul⟩
  apply reset_not_distributive a b c hab hac hbc
  apply injective
  simp only [mul, add]
  funext x y
  apply propext
  simp only [Relation.Comp, and_or_left, exists_or]

/-- Even a promise that the intersection is nonempty does not make it
expressible by a full term, with constants and arbitrary role switches. -/
theorem no_intersection (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 2), ∀ valuation : Fin 2 → WinnerSet Role,
      ((valuation 0).val ∩ (valuation 1).val).Nonempty →
        (t.eval valuation).val = (valuation 0).val ∩ (valuation 1).val := by
  classical
  rintro ⟨t, correct⟩
  have diagonal (A : WinnerSet Role) : t.eval (fun _ => A) = A := by
    apply Subtype.ext
    simpa only [Set.inter_self] using correct (fun _ => A) (by
      obtain ⟨a,ha⟩ := A.property; exact ⟨a,ha,ha⟩)
  obtain ⟨core,hcore,equal⟩ := (t.idempotent_iff_core three).mp diagonal
  let a := three 0
  let b := three 1
  let c := three 2
  have hab : a ≠ b := three.injective.ne (by decide)
  have hac : a ≠ c := three.injective.ne (by decide)
  have hbc : b ≠ c := three.injective.ne (by decide)
  let A := (WinnerSet.singleton a).union (WinnerSet.singleton b)
  let B := (WinnerSet.singleton b).union (WinnerSet.singleton c)
  let valuation : Fin 2 → WinnerSet Role := fun i => if i = 0 then A else B
  have ambiguous (i : Fin 2) : (valuation i).Ambiguous := by
    dsimp [valuation]; split
    · exact pair_ambiguous a b hab
    · exact pair_ambiguous b c hbc
  have overlap : ((valuation 0).val ∩ (valuation 1).val).Nonempty := by
    refine ⟨b,?_,?_⟩ <;> simp [valuation,A,B,WinnerSet.union,WinnerSet.singleton]
  have intersection : (valuation 0).val ∩ (valuation 1).val = {b} := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    ext r
    simp only [valuation, ite_true, h10, ite_false, A, B, WinnerSet.val_union,
      WinnerSet.val_singleton, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha | hb, hb' | hc⟩
      · exact (hab (ha.symm.trans hb')).elim
      · exact (hac (ha.symm.trans hc)).elim
      · exact hb
      · exact hb
    · rintro rfl; exact ⟨Or.inr rfl,Or.inl rfl⟩
  have atomic : core.eval valuation = WinnerSet.singleton b := by
    apply Subtype.ext
    rw [equal valuation, correct valuation overlap, intersection]
    rfl
  exact core.eval_ambiguous_of_no_winner hcore.not_hasWinner valuation ambiguous b atomic

end KFOL.Query
