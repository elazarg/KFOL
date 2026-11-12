module

public import KFOL.Core.AtomicBasis.Presentation
public import Mathlib.Data.Set.Card

/-! # The displayed presentation has no repeated syntactic equations -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

variable {Role : Type u}

private def nodes {Var : Type v} : Equational.Term (Equational.CoreSymbol Role) Var → ℕ
  | .var _ => 0
  | .func (.choice _) a => 1 + nodes (a 0) + nodes (a 1)

private def head {Var : Type v} : Equational.Term (Equational.CoreSymbol Role) Var → Option Role
  | .var _ => none
  | .func (.choice r) _ => some r

private def left {Var : Type v} : Equational.Term (Equational.CoreSymbol Role) Var →
    Equational.Term (Equational.CoreSymbol Role) Var
  | .var x => .var x
  | .func (.choice _) a => a 0

private def right {Var : Type v} : Equational.Term (Equational.CoreSymbol Role) Var →
    Equational.Term (Equational.CoreSymbol Role) Var
  | .var x => .var x
  | .func (.choice _) a => a 1

private def isVar {Var : Type v} : Equational.Term (Equational.CoreSymbol Role) Var → Bool
  | .var _ => true
  | .func (.choice _) _ => false

private def variableIndex {n : ℕ} : Equational.Term (Equational.CoreSymbol Role) (Fin n) → Option ℕ
  | .var x => some x.val
  | .func (.choice _) _ => none

private theorem pair_ext {p q : OwnerPair Role}
    (ha : pairFirst p = pairFirst q) (hb : pairSecond p = pairSecond q) : p = q := by
  apply Subtype.val_injective
  apply Finset.ext
  intro r
  rw [(pair_spec p).2, (pair_spec q).2, ha, hb]

/-- Distinct displayed indices give distinct actual identities, after every
join and reset abbreviation has been expanded in the core signature. -/
theorem basisAxiom_injective (three : Fin 3 ↪ Role) (rs : List Role) :
    Function.Injective (basisAxiom three rs) := by
  intro a b hab
  have hl := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => nodes e.lhs) hab
  have hr := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => nodes e.rhs) hab
  have hv := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => variableIndex e.rhs) hab
  have ht := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => isVar (left e.lhs)) hab
  rcases a with (a | ⟨i, a⟩) | (⟨p, a⟩ | ⟨⟩) <;>
    rcases b with (b | ⟨j, b⟩) | (⟨q, b⟩ | ⟨⟩) <;>
    (try fin_cases a) <;> (try fin_cases b)
  all_goals simp only [basisAxiom, choiceTerm, unionTerm, nodes, variableIndex, isVar, left,
    Fin.val_zero, Fin.val_one, Fin.isValue, ite_true, ite_false, one_ne_zero] at hl hr hv ht
  all_goals try { contradiction }
  all_goals try { omega }
  all_goals try { rfl }
  all_goals try {
    have h := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => head e.lhs) hab
    simp only [basisAxiom, choiceTerm, head] at h
    have hij : i = j := Option.some.inj h
    subst j
    rfl }
  all_goals {
    apply congrArg (fun r => Sum.inr (Sum.inl (r, _)))
    apply pair_ext
    · first
      | have h := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) =>
          head (left (left e.lhs))) hab
        simpa only [basisAxiom, choiceTerm, unionTerm, head, left, Fin.val_zero, Fin.val_one, ite_true, ite_false,
          one_ne_zero, Option.some.injEq] using h
      | have h := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) => head e.lhs) hab
        simpa only [basisAxiom, choiceTerm, head, Fin.val_zero, Fin.val_one, ite_true, ite_false,
          one_ne_zero, Option.some.injEq] using h
    · first
      | have h := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) =>
          head (right (left e.lhs))) hab
        simpa only [basisAxiom, choiceTerm, unionTerm, head, left, right, Fin.val_zero, Fin.val_one, ite_true, ite_false,
          one_ne_zero, Option.some.injEq] using h
      | have h := congrArg (fun e : Equational.Identity (Equational.CoreSymbol Role) =>
          head (right e.lhs)) hab
        simpa only [basisAxiom, choiceTerm, head, right, Fin.val_zero, Fin.val_one, ite_true, ite_false,
          one_ne_zero, Option.some.injEq] using h }

/-- Exact cardinality of the basis as a set of identities, not just a list. -/
theorem theory_ncard [Fintype Role] (three : Fin 3 ↪ Role) (rs : List Role) :
    (theory three rs).ncard = (Fintype.card Role)^2 + 3 * Fintype.card Role + 4 := by
  classical
  rw [theory, Set.ncard_range_of_injective (basisAxiom_injective three rs), Nat.card_eq_fintype_card,
    basisIndex_card]

end KFOL.Core.AtomicBasis
