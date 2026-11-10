module
public import KFOL.Complexity.OwnerLanguage
public import KFOL.Complexity.GuardedPairHardness
@[expose] public section
namespace KFOL.Complexity.OwnerHardnessTransport
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {Role : Type} [Fintype Role]

def transport (a b : Role) : GuardedPair.Term ℕ → Owner.Term Role ℕ
  | .var j => .var j
  | .func (.guarded sign) children => Owner.Term.guarded (if sign then a else b)
      (transport a b (children 0)) (transport a b (children 1)) (transport a b (children 2))

omit [Fintype Role] in
theorem eval_transport (a b : Role) (term : GuardedPair.Term ℕ) (valuation : ℕ → WinnerSet Role) :
    (transport a b term).eval valuation = term.eval a b valuation := by
  induction term with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol with
    | guarded sign =>
      change WinnerSet.guardedChoice (if sign then a else b)
        ((transport a b (children 0)).eval valuation)
        ((transport a b (children 1)).eval valuation)
        ((transport a b (children 2)).eval valuation) =
        WinnerSet.guardedChoice (if sign then a else b)
        (GuardedPair.Term.eval a b (children 0) valuation) (GuardedPair.Term.eval a b (children 1) valuation)
        (GuardedPair.Term.eval a b (children 2) valuation)
      rw [ih 0,ih 1,ih 2]

omit [Fintype Role] in
theorem owners_transport (a b : Role) (owners : Finset Role) (ha : a ∈ owners) (hb : b ∈ owners)
    (term : GuardedPair.Term ℕ) : (transport a b term).OwnersIn (fun r => r ∈ owners) := by
  induction term with
  | var => trivial
  | @func n symbol children ih =>
    cases symbol with
    | guarded sign =>
      change (if sign then a else b) ∈ owners ∧ _
      exact ⟨by cases sign <;> assumption,ih 0,ih 1,ih 2⟩

noncomputable def transportBound (a b : Role) : ℕ :=
  1 + OwnerTermMachines.guardedHeader a + OwnerTermMachines.guardedHeader b

private theorem code_length (a b : Role) (term : GuardedPair.Term ℕ) :
    (OwnerLanguage.termEncoding (transport a b term)).length ≤
      transportBound a b * (GuardedPairMachines.termEncoding term).length := by
  have hbound : 1 ≤ transportBound a b := by unfold transportBound; omega
  induction term with
  | var =>
    change (GuardedPairMachines.termEncoding (.var _)).length ≤ _
    nlinarith
  | @func n symbol children ih =>
    cases symbol with
    | guarded sign =>
      have h0 := ih 0
      have h1 := ih 1
      have h2 := ih 2
      rw [transport]
      change (OwnerTermMachines.termEncoding _).length ≤ _
      rw [OwnerTermMachines.length_guarded]
      have hheader : OwnerTermMachines.guardedHeader (if sign then a else b) ≤ transportBound a b := by
        unfold transportBound
        cases sign <;> dsimp <;> omega
      have hpos : 1 ≤ GuardedPairMachines.header sign := by
        unfold GuardedPairMachines.header; omega
      have he : (GuardedPairMachines.termEncoding
          (.func (.guarded sign) children)).length =
          (GuardedPairMachines.termEncoding (children 0)).length +
          (GuardedPairMachines.termEncoding (children 1)).length +
          (GuardedPairMachines.termEncoding (children 2)).length + GuardedPairMachines.header sign := by
        simp [GuardedPairMachines.termEncoding,FiniteTermMachines.termEncoding,encode_func,
          List.ofFn_succ,GuardedPairMachines.header,add_assoc]
        omega
      rw [he]
      nlinarith

private def leaf (_ : Unit) (j : ℕ) : Owner.Term Role ℕ := .var j
private def node (a b : Role) (_ : Unit) (operation : Operation GuardedPair.Symbol)
    (children : List (Owner.Term Role ℕ)) : Owner.Term Role ℕ :=
  match operation with
  | ⟨_,.guarded sign⟩ => Owner.Term.guarded (if sign then a else b)
      (children.getD 0 (.var 0)) (children.getD 1 (.var 0)) (children.getD 2 (.var 0))

omit [Fintype Role] in
private theorem fold_transport (a b : Role) (term : GuardedPair.Term ℕ) :
    FiniteFoldMachine.fold leaf (node a b) () term = transport a b term := by
  induction term with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol
    simp [FiniteFoldMachine.fold,node,transport,List.ofFn_succ,ih]

theorem transport_polyTime (a b : Role) : ComputableInPolyTime (transport a b)
    GuardedPairMachines.termEncoding OwnerLanguage.termEncoding := by
  have hl : ComputableInPolyTime (fun p : Unit × ℕ => (leaf p.1 p.2 : Owner.Term Role ℕ))
      (encPair encUnit encNat) OwnerLanguage.termEncoding := OwnerTermMachines.var_polyTime.comp (snd _ _)
  let input := encPair encUnit (encPair
    (FiniteTermMachines.operationEncoding (σ := GuardedPair.Symbol)) (encList (OwnerLanguage.termEncoding (Role := Role))))
  have hop : ComputableInPolyTime
      (fun p : Unit × (Operation GuardedPair.Symbol × List (Owner.Term Role ℕ)) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : Unit × (Operation GuardedPair.Symbol × List (Owner.Term Role ℕ)) => p.2.2)
      input (encList OwnerLanguage.termEncoding) := by fun_prop
  have hx := (listGetD (encA := OwnerLanguage.termEncoding) (.var 0 : Owner.Term Role ℕ)).comp (hc.prod (const 0))
  have hy := (listGetD (encA := OwnerLanguage.termEncoding) (.var 0 : Owner.Term Role ℕ)).comp (hc.prod (const 1))
  have hz := (listGetD (encA := OwnerLanguage.termEncoding) (.var 0 : Owner.Term Role ℕ)).comp (hc.prod (const 2))
  have hn : ComputableInPolyTime
      (fun p : Unit × (Operation GuardedPair.Symbol × List (Owner.Term Role ℕ)) => node a b p.1 p.2.1 p.2.2)
      input OwnerLanguage.termEncoding := by
    apply hop.finite_cases (branch := fun operation p => node a b p.1 operation p.2.2)
    rintro ⟨arity,operation⟩
    cases operation with
    | guarded sign => exact (OwnerTermMachines.guarded_polyTime (if sign then a else b)).comp (hx.prod (hy.prod hz))
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit)
    (valueEncoding := OwnerLanguage.termEncoding) leaf (node a b) hl hn (transportBound a b) 1 (by
      intro context term
      cases context
      rw [fold_transport]
      have h := code_length a b term
      simp only [Nat.pow_one]
      apply h.trans
      apply Nat.mul_le_mul_left
      change (encode GuardedPair.Symbol term).length ≤ _
      omega) (.var 0)
  have hp : ComputableInPolyTime (fun term : GuardedPair.Term ℕ => ((),term))
      GuardedPairMachines.termEncoding (encPair encUnit GuardedPairMachines.termEncoding) :=
    (const ()).prod id'
  convert hf.comp hp using 1
  funext term
  exact (fold_transport a b term).symm
end KFOL.Complexity.OwnerHardnessTransport
