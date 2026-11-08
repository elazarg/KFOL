module

public import KFOL.Algebra
public import Mathlib.ModelTheory.Semantics

/-! A test-only codec for the alternative mathlib term representation. The library
keeps native terms; this module is never imported by `KFOL.Algebra` or `Paper`. -/

@[expose] public section

namespace KFOLTest.SyntaxComparison

open KFOL

universe u v w

inductive Symbol (Role : Type u) : Nat → Type u where
  | winner (r : Role) : Symbol Role 0
  | choice (r : Role) : Symbol Role 2
  | rename (p : Equiv.Perm Role) : Symbol Role 1

def language (Role : Type u) : FirstOrder.Language :=
  ⟨Symbol Role, fun _ => Empty⟩

noncomputable instance {Role : Type u} : (language Role).Structure (WinnerSet Role) where
  funMap := fun {n} symbol args => match symbol with
    | .winner r => WinnerSet.singleton r
    | .choice r => WinnerSet.choice r (args 0) (args 1)
    | .rename p => WinnerSet.rename p (args 0)
  RelMap := fun {_} r => nomatch r

def encode {Role : Type u} {Var : Type v} : Term Role Var → (language Role).Term Var
  | .winner r => .func (.winner r) Fin.elim0
  | .var x => .var x
  | .choice r s t => .func (.choice r) (fun i => if i = 0 then encode s else encode t)
  | .rename p t => .func (.rename p) (fun _ => encode t)

def decode {Role : Type u} {Var : Type v} : (language Role).Term Var → Term Role Var
  | .var x => .var x
  | .func (.winner r) _ => .winner r
  | .func (.choice r) args => .choice r (decode (args 0)) (decode (args 1))
  | .func (.rename p) args => .rename p (decode (args 0))

theorem decode_encode {Role : Type u} {Var : Type v} (t : Term Role Var) :
    decode (encode t) = t := by
  induction t with
  | winner => rfl
  | var => rfl
  | choice r s t hs ht => simp [encode, decode, hs, ht]
  | rename p t ht => simp [encode, decode, ht]

theorem eval_decode {Role : Type u} {Var : Type v} (t : (language Role).Term Var)
    (v : Var → WinnerSet Role) : (decode t).eval v = t.realize v := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f with
    | winner => rfl
    | choice r =>
      change WinnerSet.choice r ((decode (args 0)).eval v) ((decode (args 1)).eval v) =
        WinnerSet.choice r ((args 0).realize v) ((args 1).realize v)
      rw [ih 0, ih 1]
    | rename p =>
      change WinnerSet.rename p ((decode (args 0)).eval v) =
        WinnerSet.rename p ((args 0).realize v)
      rw [ih 0]

-- This is a transport of the entire countervaluation theorem, for arbitrary
-- first-order terms, not just encodings of one chosen example.
theorem mathlib_pair_countervaluations {Role : Type u} {Var : Type v}
    (s t : (language Role).Term Var)
    (failure : ∃ v : Var → WinnerSet Role, s.realize v ≠ t.realize v) :
    ∃ w : Var → WinnerSet Role, (∀ x, ∃ a b, (w x).val = {a, b}) ∧
      s.realize w ≠ t.realize w := by
  obtain ⟨v, hv⟩ := failure
  obtain ⟨w, hw, hne⟩ := (decode s).exists_pair_countervaluation (decode t)
    ⟨v, by simpa only [eval_decode] using hv⟩
  exact ⟨w, hw, by simpa only [eval_decode] using hne⟩

theorem mathlib_eval_subst {Role : Type u} {Var : Type v} {Var' : Type w}
    (t : (language Role).Term Var) (replacement : Var → (language Role).Term Var')
    (v : Var' → WinnerSet Role) :
    (t.subst replacement).realize v = t.realize (fun x => (replacement x).realize v) :=
  FirstOrder.Language.Term.realize_subst

-- The operation-congruence part of equational reasoning on each API.
example {Role : Type u} {Var : Type v} (r : Role) (s s' t t' : Term Role Var)
    (v : Var → WinnerSet Role) (hs : s.eval v = s'.eval v) (ht : t.eval v = t'.eval v) :
    (Term.choice r s t).eval v = (Term.choice r s' t').eval v := by
  exact congrArg₂ (WinnerSet.choice r) hs ht

example {Role : Type u} {Var : Type v} (r : Role)
    (s s' t t' : (language Role).Term Var) (v : Var → WinnerSet Role)
    (hs : s.realize v = s'.realize v) (ht : t.realize v = t'.realize v) :
    (encode (Term.choice r (decode s) (decode t))).realize v =
      (encode (Term.choice r (decode s') (decode t'))).realize v := by
  change WinnerSet.choice r ((encode (decode s)).realize v)
      ((encode (decode t)).realize v) =
    WinnerSet.choice r ((encode (decode s')).realize v)
      ((encode (decode t')).realize v)
  have roundtrip (x : (language Role).Term Var) :
      (encode (decode x)).realize v = x.realize v := by
    rw [← eval_decode, decode_encode, eval_decode]
  rw [roundtrip s, roundtrip s', roundtrip t, roundtrip t', hs, ht]

end KFOLTest.SyntaxComparison
