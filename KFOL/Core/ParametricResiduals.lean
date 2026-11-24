module

public import Mathlib.Data.Fintype.Card

/-! # Arbitrarily many residuals at the same ordered register

Every rejecting cut for this indexed instance has a distinct terminal
state for each index. The statement is conditional on a cut.
-/

@[expose] public section
namespace KFOL.Core.ParametricResiduals

inductive Input (I : Type) | start | a (i : I) | b (i : I) | c (i : I) | d | h
  deriving DecidableEq
inductive Row (I : Type) | start | a (i : I) | b (i : I) | c (i : I) | d | e (i : I)
  deriving DecidableEq
inductive Offer (I : Type) | js | rs (i : I) | one (i : I) | pair | last | except (i : I)
  deriving DecidableEq

variable {I : Type}

def head : Row I → Input I
  | .start => .start | .a i => .a i | .b i => .b i | .c i => .c i | .d => .d | .e _ => .h

def offer : Row I → Offer I
  | .start => .js | .a i => .rs i | .b i => .one i | .c _ => .pair | .d => .last | .e i => .except i

def leftOwner : Offer I → Bool
  | .one _ | .pair | .except _ => true
  | _ => false

def member : Offer I → Input I → Prop
  | .js, .a _ => True
  | .rs i, .b j | .rs i, .c j => j = i
  | .rs _, .d => True
  | .one i, .c j => j = i
  | .pair, .d | .pair, .h | .last, .h => True
  | .except i, .c j => j ≠ i
  | _, _ => False

def query : Input I → Prop
  | .c _ | .d | .h => True
  | _ => False

def adopt (k : List (Offer I)) (o : Offer I) :=
  o :: k.filter (fun f => leftOwner f != leftOwner o)

def eligible (k : List (Offer I)) (x : Input I) : Prop :=
  match k with
  | [] => x = .start
  | [o] => member o x ∧ ¬ (leftOwner o = true ∧ query x)
  | o :: p :: _ => member o x ∧ member p x

def covered (r : Row I) (o : Offer I) : Prop :=
  leftOwner (offer r) = leftOwner o ∧ ∀ x, member o x → member (offer r) x

/-- Each witness state has a particular residual; different copies can
share the same ordered register. Every retained row admits an adoption.
The successor can be selected arbitrarily among the acceptable children. -/
structure Cut (I S : Type) where
  reg : S → List (Offer I)
  keep : S → Row I → Prop
  start : S
  initial : reg start = []
  cover : ∀ s x, eligible (reg s) x → ∃ r, keep s r ∧ head r = x
  next : S → Row I → S
  step : ∀ {s r}, keep s r → reg (next s r) = adopt (reg s) (offer r)
  sub : ∀ {s r}, keep s r → ∀ {v}, keep (next s r) v → keep s v ∧ ¬ covered v (offer r)

variable {S : Type}

private theorem uniqueRow (r : Row I) (x : Input I) (eq : head r = x) :
    match x with
    | .start => r = .start | .a i => r = .a i | .b i => r = .b i
    | .c i => r = .c i | .d => r = .d | .h => ∃ i, r = .e i := by
  subst x
  cases r <;> simp [head]

private theorem forcing (c : Cut I S) (s : S) (x : Input I) (ok : eligible (c.reg s) x) :
    match x with
    | .start => c.keep s .start | .a i => c.keep s (.a i) | .b i => c.keep s (.b i)
    | .c i => c.keep s (.c i) | .d => c.keep s .d | .h => ∃ i, c.keep s (.e i) := by
  obtain ⟨r,yes,eq⟩ := c.cover s x ok
  have u := uniqueRow r x eq
  cases x <;> simp only at u ⊢
  all_goals first | subst r; exact yes | obtain ⟨i,rfl⟩ := u; exact ⟨i,yes⟩

/-- At the common ordered register, the retained rows with head h are
exactly the singleton indexed by the adoption path. -/
theorem forced_residuals (c : Cut I S) :
    ∃ f : I → S, (∀ i, c.reg (f i) = [.last,.pair]) ∧
      (∀ i j, c.keep (f i) (.e j) ↔ i = j) ∧ Function.Injective f := by
  have a0 := forcing c c.start .start (by rw [c.initial]; rfl)
  let s₁ := c.next c.start .start
  have k₁ : c.reg s₁ = [.js] := by rw [show c.reg s₁ = _ from c.step a0,c.initial]; rfl
  have a₁ (i : I) := forcing c s₁ (.a i) (by rw [k₁]; simp [eligible,member,leftOwner])
  let s₂ (i : I) := c.next s₁ (.a i)
  have k₂ (i : I) : c.reg (s₂ i) = [.rs i] := by rw [show c.reg (s₂ i) = _ from c.step (a₁ i),k₁]; rfl
  have a₂ (i : I) := forcing c (s₂ i) (.b i) (by rw [k₂]; simp [eligible,member,leftOwner])
  let s₃ (i : I) := c.next (s₂ i) (.b i)
  have k₃ (i : I) : c.reg (s₃ i) = [.one i,.rs i] := by rw [show c.reg (s₃ i) = _ from c.step (a₂ i),k₂]; rfl
  have a₃ (i : I) := forcing c (s₃ i) (.c i) (by rw [k₃]; exact ⟨rfl,rfl⟩)
  let s₄ (i : I) := c.next (s₃ i) (.c i)
  have k₄ (i : I) : c.reg (s₄ i) = [.pair,.rs i] := by rw [show c.reg (s₄ i) = _ from c.step (a₃ i),k₃]; rfl
  have a₄ (i : I) := forcing c (s₄ i) .d (by rw [k₄]; exact ⟨True.intro,True.intro⟩)
  let f (i : I) := c.next (s₄ i) .d
  have k₅ (i : I) : c.reg (f i) = [.last,.pair] := by rw [show c.reg (f i) = _ from c.step (a₄ i),k₄]; rfl
  have unique (i j : I) (h : c.keep (f i) (.e j)) : i = j := by
    by_contra ne
    have prev := (c.sub (a₃ i) ((c.sub (a₄ i) h).1)).1
    apply (c.sub (a₂ i) prev).2
    refine ⟨rfl,fun x hit => ?_⟩
    cases x <;> simp_all [member,offer]
  have same (i : I) := forcing c (f i) .h (by rw [k₅]; exact ⟨True.intro,True.intro⟩)
  have yes (i : I) : c.keep (f i) (.e i) := by
    obtain ⟨j,hit⟩ := same i
    exact (unique i j hit).symm ▸ hit
  exact ⟨f,k₅,fun i j => ⟨unique i j,fun h => h ▸ yes i⟩,fun i j h => unique i j (h ▸ yes j)⟩

/-- With t indices, at least t distinct states realize the same register. -/
theorem local_multiplicity {t : ℕ} [Fintype S] (c : Cut (Fin t) S)
    [DecidablePred (fun s => c.reg s = [.last,.pair])] :
    t ≤ Fintype.card {s : S // c.reg s = [.last,.pair]} := by
  obtain ⟨f,atReg,_,inj⟩ := forced_residuals c
  let slots (i : Fin t) : {s : S // c.reg s = [.last,.pair]} := ⟨f i,atReg i⟩
  simpa using Fintype.card_le_of_injective slots (fun _ _ eq => inj (congrArg Subtype.val eq))

end KFOL.Core.ParametricResiduals
