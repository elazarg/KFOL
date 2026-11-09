module

public import KFOL.Algebra.TwoPlayers.Kleene.Model

/-! # Signed disjunctive normal forms for bounded De Morgan terms -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

abbrev Literal (Var : Type v) := Var × Bool
abbrev Monomial (Var : Type v) := Finset (Literal Var)
abbrev NormalForm (Var : Type v) := Finset (Monomial Var)

noncomputable def product {Var : Type v} (F G : NormalForm Var) : NormalForm Var := by
  classical
  exact (F ×ˢ G).image (fun p => p.1 ∪ p.2)

/-- A true sign denotes the complement of the term. Complements are pushed
all the way to literal leaves using De Morgan and involution. -/
noncomputable def normalForm {Var : Type v} [DecidableEq Var] (sign : Bool) : Term Var → NormalForm Var
  | .var x => {{(x,sign)}}
  | .func .bot _ => if sign then {∅} else ∅
  | .func .top _ => if sign then ∅ else {∅}
  | .func .neg args => normalForm (!sign) (args 0)
  | .func .join args => if sign then product (normalForm true (args 0)) (normalForm true (args 1))
      else normalForm false (args 0) ∪ normalForm false (args 1)
  | .func .meet args => if sign then normalForm true (args 0) ∪ normalForm true (args 1)
      else product (normalForm false (args 0)) (normalForm false (args 1))

section Evaluation

variable {M : Type u} [DistribLattice M] [BoundedOrder M]
    {Var : Type v} (neg : M → M) (v : Var → M)

def evalLiteral (l : Literal Var) : M := if l.2 then neg (v l.1) else v l.1

def evalMonomial (A : Monomial Var) : M := A.inf (evalLiteral neg v)

def evalNormalForm (F : NormalForm Var) : M := F.sup (evalMonomial neg v)

@[simp] theorem evalMonomial_union [DecidableEq Var] (A B : Monomial Var) :
    evalMonomial neg v (A ∪ B) = evalMonomial neg v A ⊓ evalMonomial neg v B :=
  Finset.inf_union

@[simp] theorem evalNormalForm_union [DecidableEq Var] (F G : NormalForm Var) :
    evalNormalForm neg v (F ∪ G) = evalNormalForm neg v F ⊔ evalNormalForm neg v G :=
  Finset.sup_union

@[simp] theorem evalNormalForm_product (F G : NormalForm Var) :
    evalNormalForm neg v (product F G) = evalNormalForm neg v F ⊓ evalNormalForm neg v G := by
  classical
  unfold product evalNormalForm
  rw [Finset.sup_image]
  change (F ×ˢ G).sup (fun p => evalMonomial neg v (p.1 ∪ p.2)) = _
  simp_rw [evalMonomial_union]
  exact (Finset.sup_inf_sup F G (evalMonomial neg v) (evalMonomial neg v)).symm

variable (hn : ∀ x, neg (neg x) = x)
    (hd : ∀ x y, neg (x ⊓ y) = neg x ⊔ neg y) (h0 : neg ⊥ = ⊤)

include hn hd h0 in
/-- Every actual term, including zero-ary constants and nested negations,
agrees with both of its signed disjunctive normal forms in every model. -/
theorem normalForm_sound [DecidableEq Var] (t : Term Var) (sign : Bool) :
    let _ := structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) neg
    evalNormalForm neg v (normalForm sign t) = if sign then neg (t.realize v) else t.realize v := by
  let := structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) neg
  induction t generalizing sign with
  | var x => cases sign <;> simp [normalForm,evalNormalForm,evalMonomial,evalLiteral]
  | @func n f args ih =>
    cases f
    · cases sign
      · change evalNormalForm neg v ∅ = ⊥
        simp [evalNormalForm]
      · change evalNormalForm neg v {∅} = neg ⊥
        simp [evalNormalForm,evalMonomial,h0]
    · cases sign
      · change evalNormalForm neg v {∅} = ⊤
        simp [evalNormalForm,evalMonomial]
      · change evalNormalForm neg v ∅ = neg ⊤
        simp [evalNormalForm,neg_top neg hn h0]
    · cases sign
      · change evalNormalForm neg v (normalForm true (args 0)) = neg ((args 0).realize v)
        simpa using ih 0 true
      · change evalNormalForm neg v (normalForm false (args 0)) = neg (neg ((args 0).realize v))
        simpa only [Bool.false_eq_true,ite_false,hn] using ih 0 false
    · cases sign
      · change evalNormalForm neg v (normalForm false (args 0) ∪ normalForm false (args 1)) =
          (args 0).realize v ⊔ (args 1).realize v
        simpa using congrArg₂ (· ⊔ ·) (ih 0 false) (ih 1 false)
      · change evalNormalForm neg v (product (normalForm true (args 0)) (normalForm true (args 1))) =
          neg ((args 0).realize v ⊔ (args 1).realize v)
        simpa [neg_sup neg hn hd] using congrArg₂ (· ⊓ ·) (ih 0 true) (ih 1 true)
    · cases sign
      · change evalNormalForm neg v (product (normalForm false (args 0)) (normalForm false (args 1))) =
          (args 0).realize v ⊓ (args 1).realize v
        simpa using congrArg₂ (· ⊓ ·) (ih 0 false) (ih 1 false)
      · change evalNormalForm neg v (normalForm true (args 0) ∪ normalForm true (args 1)) =
          neg ((args 0).realize v ⊓ (args 1).realize v)
        simpa [hd] using congrArg₂ (· ⊔ ·) (ih 0 true) (ih 1 true)

end Evaluation

end KFOL.TwoPlayers.Kleene
