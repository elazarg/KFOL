module

public import KFOL.Definitions.Equational

/-! # Exact bridges from the native full and core syntax to equational terms -/

@[expose] public section

namespace KFOL.Equational

universe u v w

variable {Role : Type u} {Var : Type v} {Var' : Type w}

namespace Full

theorem decode_encode (t : KFOL.Term Role Var) : decode (encode t) = t := by
  induction t with
  | winner => rfl
  | var => rfl
  | choice r s t hs ht => simp [encode, decode, hs, ht]
  | rename p t ht => simp [encode, decode, ht]

theorem encode_decode (t : Term (FullSymbol Role) Var) : encode (decode t) = t := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f with
    | winner =>
      simp only [decode, encode]
      congr 1
      funext i
      exact Fin.elim0 i
    | choice r =>
      simp only [decode, encode]
      congr 1
      funext i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> simp [ih]
    | rename p =>
      simp only [decode, encode]
      congr 1
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ih 0

/-- Compatibility holds for all generic terms, not just native encodings. -/
theorem eval_decode (t : Term (FullSymbol Role) Var) (v : Var → WinnerSet Role) :
    let _ := fullStructure Role
    (decode t).eval v = t.realize v := by
  let _ := fullStructure Role
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
      change WinnerSet.rename p ((decode (args 0)).eval v) = WinnerSet.rename p ((args 0).realize v)
      rw [ih 0]

/-- The codec preserves actual variable support, including unused declarations. -/
theorem vars_decode [DecidableEq Var] (t : Term (FullSymbol Role) Var) :
    (decode t).vars = t.varFinset := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f <;> simp [decode, KFOL.Term.vars, FirstOrder.Language.Term.varFinset,
      Finset.univ_fin2, ih]

/-- Structural substitution commutes with the public encoding. -/
theorem encode_subst (t : KFOL.Term Role Var) (replacement : Var → KFOL.Term Role Var') :
    encode (t.subst replacement) = (encode t).subst (fun x => encode (replacement x)) := by
  induction t with
  | winner r =>
    simp only [KFOL.Term.subst, encode, FirstOrder.Language.Term.subst]
    congr 1
    funext i
    exact Fin.elim0 i
  | var => rfl
  | choice r s t hs ht =>
    simp only [KFOL.Term.subst, encode, FirstOrder.Language.Term.subst, hs, ht]
    congr 1
    funext i
    split_ifs <;> rfl
  | rename p t ih => simp only [KFOL.Term.subst, encode, FirstOrder.Language.Term.subst, ih]

end Full

namespace Core

theorem isCore_decode (t : Term (CoreSymbol Role) Var) : (decode t).IsCore := by
  induction t with
  | var => trivial
  | @func n f args ih => cases f; exact ⟨ih 0, ih 1⟩

theorem decode_encode (t : KFOL.Term Role Var) (h : t.IsCore) : decode (encode t h) = t := by
  induction t with
  | winner => exact False.elim h
  | var => rfl
  | choice r s t hs ht => simp [encode, decode, hs h.1, ht h.2]
  | rename => exact False.elim h

theorem encode_decode (t : Term (CoreSymbol Role) Var) :
    encode (decode t) (isCore_decode t) = t := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f
    simp only [decode, encode]
    congr 1
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp [ih]

theorem eval_decode (t : Term (CoreSymbol Role) Var) (v : Var → WinnerSet Role) :
    let _ := coreStructure Role
    (decode t).eval v = t.realize v := by
  let _ := coreStructure Role
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f with
    | choice r =>
      change WinnerSet.choice r ((decode (args 0)).eval v) ((decode (args 1)).eval v) =
        WinnerSet.choice r ((args 0).realize v) ((args 1).realize v)
      rw [ih 0, ih 1]

/-- Core substitution crosses the representation boundary structurally. -/
theorem decode_subst (t : Term (CoreSymbol Role) Var)
    (replacement : Var → Term (CoreSymbol Role) Var') :
    decode (t.subst replacement) = (decode t).subst (fun x => decode (replacement x)) := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f
    simp only [FirstOrder.Language.Term.subst, decode, KFOL.Term.subst, ih]

/-- Core support is the native support, with no constants or hidden variables. -/
theorem vars_decode [DecidableEq Var] (t : Term (CoreSymbol Role) Var) :
    (decode t).vars = t.varFinset := by
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f
    simp [decode, KFOL.Term.vars, FirstOrder.Language.Term.varFinset, Finset.univ_fin2, ih]

end Core
end KFOL.Equational
