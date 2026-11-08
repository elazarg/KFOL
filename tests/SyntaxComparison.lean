module

public import KFOL.Algebra
public import Mathlib.ModelTheory.Semantics

/-! Transport the pair-countervaluation theorem through the production codec.
These tests use arbitrary mathlib terms, not just encoded native examples. -/

@[expose] public section

namespace KFOLTest.SyntaxComparison

open KFOL

universe u v w

abbrev language (Role : Type u) := Equational.language (Equational.FullSymbol Role)

noncomputable local instance {Role : Type u} : (language Role).Structure (WinnerSet Role) :=
  Equational.fullStructure Role

open Equational.Full (encode decode decode_encode eval_decode)

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
