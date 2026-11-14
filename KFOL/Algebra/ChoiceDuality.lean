module

public import KFOL.Definitions.ChoiceDuality
public import Mathlib.Tactic
public import KFOL.Audit.Namespace

/-! # Complement duality and functional completeness of literal mixed choice -/

@[expose] public section
namespace KFOL.ChoiceDuality
universe u v
variable {Role : Type u} {Var : Type v}

@[simp] theorem own_empty_left (r : Role) (S : Set Role) : own r ∅ S = S := by
  classical
  by_cases h : S = {r} <;> simp [own, h]

@[simp] theorem own_empty_right (r : Role) (S : Set Role) : own r S ∅ = S := by
  classical
  by_cases h : S = {r} <;> simp [own, h]

@[simp] theorem own_self (r : Role) (S : Set Role) : own r S S = S := by
  classical
  by_cases h : S = {r} <;> simp [own, h]

theorem own_val (r : Role) (S T : WinnerSet Role) :
    own r S.val T.val = (WinnerSet.choice r S T).val := by
  classical
  have hs : S.val = {r} ↔ S = WinnerSet.singleton r :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have ht : T.val = {r} ↔ T = WinnerSet.singleton r :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [own, WinnerSet.choice, hs, ht]
  split <;> rfl

theorem own_comm (r : Role) (S T : Set Role) : own r S T = own r T S := by
  classical
  simp only [own, or_comm, Set.union_comm]

theorem own_assoc (r : Role) (S T U : Set Role) :
    own r (own r S T) U = own r S (own r T U) := by
  rcases Set.eq_empty_or_nonempty S with rfl | hs
  · simp
  rcases Set.eq_empty_or_nonempty T with rfl | ht
  · simp
  rcases Set.eq_empty_or_nonempty U with rfl | hu
  · simp
  simpa only [← own_val] using congrArg Subtype.val
    (WinnerSet.choice_assoc ⟨S, hs⟩ ⟨T, ht⟩ r ⟨U, hu⟩)

theorem dual_formula (r : Role) (S T : Set Role) :
    dual r S T = if S = ({r} : Set Role)ᶜ ∨ T = ({r} : Set Role)ᶜ
      then ({r} : Set Role)ᶜ else S ∩ T := by
  classical
  have hs : Sᶜ = {r} ↔ S = ({r} : Set Role)ᶜ := by
    constructor <;> intro h <;>
      simpa only [compl_compl] using congrArg (fun A : Set Role => Aᶜ) h
  have ht : Tᶜ = {r} ↔ T = ({r} : Set Role)ᶜ := by
    constructor <;> intro h <;>
      simpa only [compl_compl] using congrArg (fun A : Set Role => Aᶜ) h
  simp only [dual, own, hs, ht]
  split <;> simp

@[simp] theorem dual_univ_left (r : Role) (S : Set Role) : dual r Set.univ S = S := by
  simp [dual]

@[simp] theorem dual_self (r : Role) (S : Set Role) : dual r S S = S := by
  simp [dual]

theorem dual_comm (r : Role) (S T : Set Role) : dual r S T = dual r T S := by
  rw [dual, dual, own_comm]

theorem dual_assoc (r : Role) (S T U : Set Role) :
    dual r (dual r S T) U = dual r S (dual r T U) := by
  simp only [dual, compl_compl, own_assoc]

theorem neutral_union (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (S T : Set Role) : own c (own a S T) (own b S T) = S ∪ T := by
  rcases Set.eq_empty_or_nonempty S with rfl | hs
  · simp
  rcases Set.eq_empty_or_nonempty T with rfl | ht
  · simp
  simpa only [← own_val, WinnerSet.val_union] using congrArg Subtype.val
    (WinnerSet.three_owner_union ⟨S, hs⟩ ⟨T, ht⟩ a b c hab hac hbc)

theorem neutral_intersection (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (S T : Set Role) : dual c (dual a S T) (dual b S T) = S ∩ T := by
  simp only [dual, compl_compl, neutral_union a b c hab hac hbc, Set.compl_union,
    compl_compl]

namespace Expressible

theorem winner (r : Role) : Expressible (fun (_ : Var → Set Role) => {r}) :=
  ⟨.winner r, fun _ => rfl⟩

theorem var (x : Var) : Expressible (fun (values : Var → Set Role) => values x) :=
  ⟨.var x, fun _ => rfl⟩

theorem own {f g : (Var → Set Role) → Set Role} (hf : Expressible f) (hg : Expressible g)
    (r : Role) : Expressible (fun values => ChoiceDuality.own r (f values) (g values)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨.own r s t, fun values => by simp only [Term.eval, hs, ht]⟩

theorem dual {f g : (Var → Set Role) → Set Role} (hf : Expressible f) (hg : Expressible g)
    (r : Role) : Expressible (fun values => ChoiceDuality.dual r (f values) (g values)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨.dual r s t, fun values => by simp only [Term.eval, hs, ht]⟩

variable (three : Fin 3 ↪ Role)
include three

theorem union {f g : (Var → Set Role) → Set Role} (hf : Expressible f) (hg : Expressible g) :
    Expressible (fun values => f values ∪ g values) := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  obtain ⟨t, ht⟩ := (hf.own hg (three 0)).own (hf.own hg (three 1)) (three 2)
  exact ⟨t, fun values => (ht values).trans (neutral_union _ _ _ h01 h02 h12 _ _)⟩

theorem inter {f g : (Var → Set Role) → Set Role} (hf : Expressible f) (hg : Expressible g) :
    Expressible (fun values => f values ∩ g values) := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  obtain ⟨t, ht⟩ := (hf.dual hg (three 0)).dual (hf.dual hg (three 1)) (three 2)
  exact ⟨t, fun values => (ht values).trans (neutral_intersection _ _ _ h01 h02 h12 _ _)⟩

theorem empty : Expressible (fun (_ : Var → Set Role) => ∅) := by
  obtain ⟨t, ht⟩ := inter three (winner (three 0)) (winner (three 1))
  refine ⟨t, fun values => (ht values).trans ?_⟩
  simp

end Expressible

/-- A truth bit carried by the singleton of a specified role. -/
noncomputable def indicator (P : (Var → Set Role) → Prop) (r : Role)
    (values : Var → Set Role) : Set Role := by
  classical
  exact if P values then {r} else ∅

namespace Expressible
variable (three : Fin 3 ↪ Role)
include three

theorem neg_move {P : (Var → Set Role) → Prop} {p q : Role} (hpq : p ≠ q)
    (hP : Expressible (indicator P p)) :
    Expressible (indicator (fun values => ¬ P values) q) := by
  classical
  obtain ⟨t, ht⟩ := inter three (hP.own (winner q) p) (winner q)
  refine ⟨t, fun values => (ht values).trans ?_⟩
  by_cases h : P values
  · simp [indicator, h, ChoiceDuality.own, hpq]
  · simp [indicator, h, ChoiceDuality.own, hpq.symm]

theorem move {P : (Var → Set Role) → Prop} {p q : Role}
    (hP : Expressible (indicator P p)) : Expressible (indicator P q) := by
  by_cases hpq : p = q
  · simpa only [hpq] using hP
  obtain ⟨k, hkp, hkq⟩ := exists_role_outside_pair three p q
  simpa only [not_not] using neg_move three hkq (neg_move three hkp.symm hP)

theorem neg {P : (Var → Set Role) → Prop} {p : Role}
    (hP : Expressible (indicator P p)) :
    Expressible (indicator (fun values => ¬ P values) p) := by
  obtain ⟨q, hqp, _⟩ := exists_role_outside_pair three p p
  exact move three (neg_move three hqp.symm hP)

theorem membership (x : Var) (r a : Role) :
    Expressible (indicator (fun values => r ∈ values x) a) := by
  classical
  have h : Expressible (indicator (fun values => r ∈ values x) r) := by
    obtain ⟨t, ht⟩ := inter three (var x) (winner r)
    refine ⟨t, fun values => (ht values).trans ?_⟩
    by_cases hr : r ∈ values x <;> ext k <;> simp [indicator, hr]
  exact move three h

theorem and_indicator {P Q : (Var → Set Role) → Prop} {a : Role}
    (hP : Expressible (indicator P a)) (hQ : Expressible (indicator Q a)) :
    Expressible (indicator (fun values => P values ∧ Q values) a) := by
  classical
  obtain ⟨t, ht⟩ := inter three hP hQ
  refine ⟨t, fun values => (ht values).trans ?_⟩
  by_cases hp : P values <;> by_cases hq : Q values <;> simp [indicator, hp, hq]

theorem forall_finset {J : Type*} (s : Finset J)
    (P : J → (Var → Set Role) → Prop) (a : Role)
    (hP : ∀ j ∈ s, Expressible (indicator (P j) a)) :
    Expressible (indicator (fun values => ∀ j ∈ s, P j values) a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : indicator (fun values => ∀ j ∈ (∅ : Finset J), P j values) a =
        (fun (_ : Var → Set Role) => {a}) := by
      funext values
      simp [indicator]
    rw [he]
    exact winner a
  | @insert j s hj ih =>
    have hh := and_indicator three (hP j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)))
    simpa only [Finset.forall_mem_insert] using hh

theorem forall_finite {J : Type*} [Fintype J]
    (P : J → (Var → Set Role) → Prop) (a : Role)
    (hP : ∀ j, Expressible (indicator (P j) a)) :
    Expressible (indicator (fun values => ∀ j, P j values) a) := by
  classical
  simpa only [Finset.mem_univ, forall_true_left] using
    forall_finset three Finset.univ P a (fun j _ => hP j)

theorem equality_test [Fintype Role] [Fintype Var] (A : Var → Set Role) (a : Role) :
    Expressible (indicator (fun values => values = A) a) := by
  classical
  have h : Expressible (indicator
      (fun values => ∀ j, ∀ r, r ∈ values j ↔ r ∈ A j) a) := by
    apply forall_finite three _ a
    intro j
    apply forall_finite three _ a
    intro r
    by_cases hr : r ∈ A j
    · simpa only [hr, iff_true] using membership three j r a
    · simpa only [hr, iff_false] using neg three (membership three j r a)
  have he : (fun values : Var → Set Role => ∀ j, ∀ r, r ∈ values j ↔ r ∈ A j) =
      (fun values => values = A) := by
    funext values
    apply propext
    constructor
    · intro hv
      exact funext (fun j => Set.ext (hv j))
    · rintro rfl
      simp
  rwa [he] at h

theorem union_finset {J : Type*} (s : Finset J) (f : J → (Var → Set Role) → Set Role)
    (hf : ∀ j ∈ s, Expressible (f j)) :
    Expressible (fun values => ⋃ j ∈ s, f j values) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty (Var := Var) three)
  | @insert j s hj ih =>
    have hh := union three (hf j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    simpa only [Finset.set_biUnion_insert] using hh

theorem union_finite {J : Type*} [Fintype J] (f : J → (Var → Set Role) → Set Role)
    (hf : ∀ j, Expressible (f j)) :
    Expressible (fun values => ⋃ j, f j values) := by
  classical
  simpa only [Finset.mem_univ, Set.iUnion_true] using
    union_finset three Finset.univ f (fun j _ => hf j)

end Expressible

/-- Every operation of every finite arity is represented in the primitive
signature of the two literal choice families and singleton constants. -/
theorem functional_complete [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → Set Role) → Set Role) : Expressible f := by
  classical
  let a := three 0
  have hcell (A : Var → Set Role) :
      Expressible (fun values => if values = A then f A else ∅) := by
    have h := Expressible.union_finset three (Finset.univ.filter (fun r => r ∈ f A))
      (fun r => indicator (fun values => values = A) r)
      (fun r _ => Expressible.move three (Expressible.equality_test three A a))
    obtain ⟨t, ht⟩ := h
    refine ⟨t, fun values => (ht values).trans ?_⟩
    by_cases hv : values = A <;> ext r <;> simp [indicator, hv]
  obtain ⟨t, ht⟩ := Expressible.union_finite three _ hcell
  refine ⟨t, fun values => (ht values).trans ?_⟩
  ext r
  simp only [Set.mem_iUnion, Set.mem_ite_empty_right]
  constructor
  · rintro ⟨A, hA, hr⟩
    simpa only [hA] using hr
  · intro hr
    exact ⟨values, rfl, hr⟩

end KFOL.ChoiceDuality

#audit_namespace KFOL.ChoiceDuality
