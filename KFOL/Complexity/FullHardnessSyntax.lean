module
public import KFOL.Algorithms.FullTermCode.View
public import KFOL.Reductions.RawPairs
@[expose] public section
namespace KFOL.Complexity.FullHardness

/-- Each source binary node becomes one original owned-choice node. There are
no winner constants, role switches or copied continuation subtrees. -/
def ofPair {Role : Type} (a b : Role) : RawPair.Term ℕ → Term Role ℕ
  | .var j => .var j
  | .func (.binary sign) args =>
      .choice (if sign then a else b) (ofPair a b (args 0)) (ofPair a b (args 1))

@[simp] theorem ofPair_var {Role : Type} (a b : Role) (j : ℕ) :
    ofPair a b (.var j) = .var j := rfl
@[simp] theorem ofPair_node {Role : Type} (a b : Role) (sign : Bool) (s t : RawPair.Term ℕ) :
    ofPair a b (RawPair.Term.node sign s t) =
      .choice (if sign then a else b) (ofPair a b s) (ofPair a b t) := rfl

theorem ofPair_isCore {Role : Type} (a b : Role) (t : RawPair.Term ℕ) : (ofPair a b t).IsCore := by
  induction t with
  | var j => trivial
  | func symbol args ih =>
    cases symbol
    exact ⟨ih 0,ih 1⟩

@[simp] theorem eval_ofPair {Role : Type} (a b : Role) (t : RawPair.Term ℕ)
    (valuation : ℕ → WinnerSet Role) :
    (ofPair a b t).eval valuation = t.eval (WinnerSet.choice a) (WinnerSet.choice b) valuation := by
  induction t with
  | var j => rfl
  | func symbol args ih =>
    cases symbol with
    | binary sign =>
      simp only [ofPair, Term.eval, RawPair.Term.eval,
        FirstOrder.Language.Term.realize]
      rw [ih 0,ih 1]
      cases sign <;> rfl

/-- Raw implementation of the same original-node translation. -/
def rawPair (a b : ℕ) : RawPair.Term ℕ → FullTermCode.Raw
  | .var j => .var j
  | .func (.binary sign) args =>
      .func (.choice (if sign then a else b)) (fun i => if i = 0 then rawPair a b (args 0) else rawPair a b (args 1))

@[simp] theorem view_ofPair {K : ℕ} (a b : Fin K) (t : RawPair.Term ℕ) :
    FullTermCode.view (ofPair a b t) = rawPair a.val b.val t := by
  induction t with
  | var j => rfl
  | func symbol args ih =>
    cases symbol with
    | binary sign =>
      simp only [ofPair, FullTermCode.view, rawPair]
      congr 1
      · cases sign <;> rfl
      · funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> simp [ih]
end KFOL.Complexity.FullHardness
