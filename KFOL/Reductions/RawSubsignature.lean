module

public import KFOL.Reductions.RawPairs
public import KFOL.Algebra.Semilattice

/-! Exact raw-subsignature interpretation and semantic dichotomy. -/

@[expose] public section

namespace KFOL.Raw

universe u v

/- The raw operations are independent of any chosen presentation. -/
namespace Operation

end Operation

/- A term can use precisely the selected native binary operations. -/
namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

@[simp] theorem eval_var (j : Var) (valuation : Var → WinnerSet Role) :
    eval (.var j : Term selected Var) valuation = valuation j := rfl

@[simp] theorem eval_node (operation : {operation // operation ∈ selected}) (s t : Term selected Var)
    (valuation : Var → WinnerSet Role) :
    (node operation s t).eval valuation = operation.val.eval (s.eval valuation) (t.eval valuation) := rfl

theorem eval_ofRawPair (operations : Bool → {operation // operation ∈ selected}) (t : RawPair.Term Var)
    (valuation : Var → WinnerSet Role) :
    (ofRawPair operations t).eval valuation =
      t.eval (operations true).val.eval (operations false).val.eval valuation := by
  induction t with
  | var j => rfl
  | @func n symbol args ih =>
    cases symbol with
    | binary sign =>
      change (operations sign).val.eval ((ofRawPair operations (args 0)).eval valuation)
        ((ofRawPair operations (args 1)).eval valuation) = _
      rw [ih 0, ih 1]
      cases sign <;> rfl

@[simp] theorem size_ofRawPair (operations : Bool → {operation // operation ∈ selected}) (t : RawPair.Term Var) :
    size (ofRawPair operations t) = t.size := by
  induction t with
  | var j => rfl
  | @func n symbol args ih => cases symbol; simp only [ofRawPair, size, RawPair.Term.size, ih]

theorem varFinset_ofRawPair [DecidableEq Var] (operations : Bool → {operation // operation ∈ selected})
    (t : RawPair.Term Var) : (ofRawPair operations t).varFinset = t.varFinset := by
  induction t with
  | var j => rfl
  | @func n symbol args ih => cases symbol; simp only [ofRawPair, FirstOrder.Language.Term.varFinset, ih]

end Term
end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

theorem support_nonempty [DecidableEq Var] (t : Term selected Var) : t.support.Nonempty := by
  induction t with
  | var j => exact Finset.singleton_nonempty j
  | @func n symbol args ih => cases symbol; exact (ih 0).mono Finset.subset_union_left

/- Every singleton semilattice presentation has exactly the variable-set
semantics. This lemma accepts the actual operation equality, not validity. -/
theorem eval_eq_sup [DecidableEq Var] [SemilatticeSup (WinnerSet Role)]
    (hoperation : ∀ operation : {operation // operation ∈ selected}, operation.val.eval = (· ⊔ ·))
    (t : Term selected Var) (valuation : Var → WinnerSet Role) :
    t.eval valuation = t.support.sup' t.support_nonempty valuation := by
  induction t with
  | var j => simp [support]
  | @func n symbol args ih =>
    cases symbol with
    | binary operation =>
      change operation.val.eval (eval (args 0) valuation) (eval (args 1) valuation) = _
      rw [hoperation, ih 0, ih 1]
      exact (Finset.sup'_union (support_nonempty (args 0)) (support_nonempty (args 1)) valuation).symm

theorem eval_eq_of_support_eq [DecidableEq Var] [SemilatticeSup (WinnerSet Role)]
    (hoperation : ∀ operation : {operation // operation ∈ selected}, operation.val.eval = (· ⊔ ·))
    (s t : Term selected Var) (hs : s.support = t.support) :
    ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation := by
  intro valuation
  rw [eval_eq_sup hoperation, eval_eq_sup hoperation]
  exact Finset.sup'_congr s.support_nonempty hs (fun _ _ => rfl)

end Term
end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

theorem eval_choice_eq_owner_iff [DecidableEq Var] (owner : Role)
    (hoperation : ∀ operation : {operation // operation ∈ selected}, operation.val = .choice owner)
    (t : Term selected Var) (valuation : Var → WinnerSet Role) :
    t.eval valuation = WinnerSet.singleton owner ↔ ∃ j ∈ t.support, valuation j = WinnerSet.singleton owner := by
  induction t with
  | var j => simp [support]
  | @func n symbol args ih =>
    cases symbol with
    | binary operation =>
      change operation.val.eval (eval (args 0) valuation) (eval (args 1) valuation) = _ ↔ _
      rw [hoperation operation]
      change WinnerSet.choice owner (eval (args 0) valuation) (eval (args 1) valuation) = _ ↔ _
      rw [WinnerSet.choice_eq_owner_iff, ih 0, ih 1]
      simp only [support, Finset.mem_union]
      aesop

theorem eval_union_mem_iff [DecidableEq Var]
    (hoperation : ∀ operation : {operation // operation ∈ selected}, operation.val = .union)
    (t : Term selected Var) (valuation : Var → WinnerSet Role) (r : Role) :
    r ∈ (t.eval valuation).val ↔ ∃ j ∈ t.support, r ∈ (valuation j).val := by
  induction t with
  | var j => simp [support]
  | @func n symbol args ih =>
    cases symbol with
    | binary operation =>
      change r ∈ (operation.val.eval (eval (args 0) valuation) (eval (args 1) valuation)).val ↔ _
      rw [hoperation operation]
      change (r ∈ (eval (args 0) valuation).val ∨ r ∈ (eval (args 1) valuation).val) ↔ _
      rw [ih 0, ih 1]
      simp only [support, Finset.mem_union]
      aesop

theorem support_eq_iff_valid_choice [DecidableEq Var] (a b : Role) (hab : a ≠ b)
    (hselected : selected = {.choice a}) (s t : Term selected Var) :
    s.support = t.support ↔ ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation := by
  classical
  have hop : ∀ operation : {operation // operation ∈ selected}, operation.val = .choice a := by
    intro operation
    exact Finset.mem_singleton.mp (hselected ▸ operation.property)
  constructor
  · intro hs
    let _ := WinnerSet.choiceSemilattice a
    exact eval_eq_of_support_eq (fun operation => congrArg Operation.eval (hop operation)) s t hs
  · intro hv
    apply Finset.ext
    intro j
    let valuation : Var → WinnerSet Role := fun i => if i = j then .singleton a else .singleton b
    have hc (term : Term selected Var) : term.eval valuation = WinnerSet.singleton a ↔ j ∈ term.support := by
      rw [eval_choice_eq_owner_iff a hop]
      simp [valuation, WinnerSet.singleton_inj, hab.symm]
    exact (hc s).symm.trans ((congrArg (fun value => value = WinnerSet.singleton a) (hv valuation)).to_iff.trans (hc t))

@[instance_reducible] noncomputable def unionSemilattice : SemilatticeSup (WinnerSet Role) :=
  letI : Max (WinnerSet Role) := ⟨WinnerSet.union⟩
  SemilatticeSup.mk' WinnerSet.union_comm
    (fun A B C => Subtype.ext (Set.union_assoc A.val B.val C.val)) WinnerSet.union_self

theorem support_eq_iff_valid_union [DecidableEq Var] (a b : Role) (hab : a ≠ b)
    (hselected : selected = {.union}) (s t : Term selected Var) :
    s.support = t.support ↔ ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation := by
  classical
  have hop : ∀ operation : {operation // operation ∈ selected}, operation.val = .union := by
    intro operation
    exact Finset.mem_singleton.mp (hselected ▸ operation.property)
  constructor
  · intro hs
    let _ := unionSemilattice (Role := Role)
    exact eval_eq_of_support_eq (fun operation => congrArg Operation.eval (hop operation)) s t hs
  · intro hv
    apply Finset.ext
    intro j
    let valuation : Var → WinnerSet Role := fun i => if i = j then .singleton a else .singleton b
    have hc (term : Term selected Var) : a ∈ (term.eval valuation).val ↔ j ∈ term.support := by
      rw [eval_union_mem_iff hop]
      have hval (i : Var) : a ∈ (valuation i).val ↔ i = j := by
        dsimp only [valuation]
        split_ifs <;> simp_all [WinnerSet.val_singleton]
      simp only [hval, exists_eq_right]
    exact (hc s).symm.trans ((congrArg (fun value : WinnerSet Role => a ∈ value.val) (hv valuation)).to_iff.trans (hc t))

end Term

/- Every signature with at least two operations contains one of the four
hard pairs, independently of the chosen finite operation numbering. -/
theorem exists_hard_pair {Role : Type u} (selected : Finset (Operation Role)) (h : 1 < selected.card) :
    (.reset ∈ selected ∧ .union ∈ selected) ∨
    (∃ a b : Role, a ≠ b ∧ .choice a ∈ selected ∧ .choice b ∈ selected) ∨
    (∃ a : Role, .choice a ∈ selected ∧ .union ∈ selected) ∨
    (∃ a : Role, .choice a ∈ selected ∧ .reset ∈ selected) := by
  obtain ⟨first, hf, second, hs, hne⟩ := Finset.one_lt_card.mp h
  cases first with
  | choice a =>
    cases second with
    | choice b => exact Or.inr (Or.inl ⟨a, b, fun he => hne (congrArg Operation.choice he), hf, hs⟩)
    | union => exact Or.inr (Or.inr (Or.inl ⟨a, hf, hs⟩))
    | reset => exact Or.inr (Or.inr (Or.inr ⟨a, hf, hs⟩))
  | union =>
    cases second with
    | choice a => exact Or.inr (Or.inr (Or.inl ⟨a, hs, hf⟩))
    | union => exact (hne rfl).elim
    | reset => exact Or.inl ⟨hs, hf⟩
  | reset =>
    cases second with
    | choice a => exact Or.inr (Or.inr (Or.inr ⟨a, hs, hf⟩))
    | union => exact Or.inl ⟨hf, hs⟩
    | reset => exact (hne rfl).elim

end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

theorem exists_var_of_empty (hselected : selected = ∅) (t : Term selected Var) : ∃ j, t = .var j := by
  cases t with
  | var j => exact ⟨j, rfl⟩
  | @func n symbol args =>
    cases symbol with
    | binary operation => exact (Finset.notMem_empty operation.val (hselected ▸ operation.property)).elim

@[simp] theorem eval_ofResetUnion (hreset : Operation.reset ∈ selected) (hunion : Operation.union ∈ selected)
    (t : ResetUnion.Term Var) (valuation : Var → WinnerSet Role) :
    eval (ofResetUnion hreset hunion t) valuation = t.eval valuation := by
  induction t with
  | var j => rfl
  | @func n symbol args ih =>
    cases symbol with
    | reset =>
      change WinnerSet.reset (eval (ofResetUnion hreset hunion (args 0)) valuation)
        (eval (ofResetUnion hreset hunion (args 1)) valuation) =
        WinnerSet.reset (ResetUnion.Term.eval (args 0) valuation) (ResetUnion.Term.eval (args 1) valuation)
      rw [ih 0, ih 1]
    | union =>
      change WinnerSet.union (eval (ofResetUnion hreset hunion (args 0)) valuation)
        (eval (ofResetUnion hreset hunion (args 1)) valuation) =
        WinnerSet.union (ResetUnion.Term.eval (args 0) valuation) (ResetUnion.Term.eval (args 1) valuation)
      rw [ih 0, ih 1]

@[simp] theorem size_ofResetUnion (hreset : Operation.reset ∈ selected) (hunion : Operation.union ∈ selected)
    (t : ResetUnion.Term Var) : size (ofResetUnion hreset hunion t) = t.size := by
  induction t with
  | var j => rfl
  | @func n symbol args ih => cases symbol <;> simp only [ofResetUnion, size, ResetUnion.Term.size, ih]

/- A singleton reset signature is translated node for node to the existing
independently defined reset frontend. -/
@[simp] theorem eval_toReset (hselected : selected = {.reset}) (t : Term selected Var)
    (valuation : Var → WinnerSet Role) : (toReset hselected t).eval valuation = t.eval valuation := by
  induction t with
  | var j => rfl
  | @func n symbol args ih =>
    cases symbol with
    | binary operation =>
      have hop : operation.val = .reset := Finset.mem_singleton.mp (hselected ▸ operation.property)
      change WinnerSet.reset ((toReset hselected (args 0)).eval valuation)
        ((toReset hselected (args 1)).eval valuation) =
        operation.val.eval (eval (args 0) valuation) (eval (args 1) valuation)
      rw [hop, ih 0, ih 1]
      rfl

end Term

/- Validity of native selected terms keeps all valuation quantifiers. -/
namespace Reduction

variable {Role : Type u} (selected : Finset (Operation Role))

theorem valid_resetUnion_iff (three : Fin 3 ↪ Role) (hr : Operation.reset ∈ selected) (hu : Operation.union ∈ selected)
    (formula : Reductions.CNF) : Valid selected (resetUnion selected hr hu formula) ↔ ¬Reductions.Satisfiable formula := by
  simpa only [Valid, resetUnion, Term.eval_ofResetUnion, ResetUnion.Valid] using Reductions.ResetUnion.valid_equation_iff three formula

theorem valid_choiceUnion_iff (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (ha : Operation.choice a ∈ selected) (hu : Operation.union ∈ selected) (formula : Reductions.CNF) :
    Valid selected (choiceUnion selected a ha hu formula) ↔ ¬Reductions.Satisfiable formula := by
  simpa only [Valid, choiceUnion, Term.eval_ofRawPair, Term.pairOperations, Operation.eval] using
    Reductions.RawPair.union_equation_valid_iff_unsatisfiable a b c hab hac hcb formula

theorem valid_twoChoices_iff (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (ha : Operation.choice a ∈ selected) (hb : Operation.choice b ∈ selected) (formula : Reductions.CNF) :
    Valid selected (twoChoices selected a b ha hb formula) ↔ ¬Reductions.Satisfiable formula := by
  simpa only [Valid, twoChoices, Term.eval_ofRawPair, Term.pairOperations, Operation.eval] using
    Reductions.RawPair.twoOwners_equation_valid_iff_unsatisfiable a b c hab hac hcb formula

theorem valid_resetChoice_iff (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Operation.choice a ∈ selected) (hr : Operation.reset ∈ selected) (formula : Reductions.CNF) :
    Valid selected (resetChoice selected a ha hr formula) ↔ ¬Reductions.Satisfiable formula := by
  simpa only [Valid, resetChoice, Term.eval_ofRawPair, Term.pairOperations, Operation.eval] using
    Reductions.ResetChoice.equation_valid_iff_unsatisfiable a b c hab hac hbc formula

end Reduction
end KFOL.Raw

namespace KFOL.Raw

universe u v

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

theorem Term.support_eq_varFinset [DecidableEq Var] (t : Term selected Var) : t.support = t.varFinset := by
  induction t with
  | var j => rfl
  | @func n symbol args ih =>
    cases symbol with
    | binary operation =>
      simp only [Term.support, FirstOrder.Language.Term.varFinset, Finset.univ_fin2,
        Finset.biUnion_insert, Finset.singleton_biUnion, ih]

theorem small_signature_cases (selected : Finset (Operation Role)) :
    selected.card ≤ 1 ↔ selected = ∅ ∨ (∃ a : Role, selected = {.choice a}) ∨
      selected = {.union} ∨ selected = {.reset} := by
  classical
  constructor
  · intro h
    by_cases he : selected = ∅
    · exact Or.inl he
    obtain ⟨operation, hop⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hs : selected = {operation} := Finset.ext (fun x => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hx => (Finset.card_le_one.mp h) x hx operation hop, fun hx => hx ▸ hop⟩)
    cases operation with
    | choice a => exact Or.inr (Or.inl ⟨a, hs⟩)
    | union => exact Or.inr (Or.inr (Or.inl hs))
    | reset => exact Or.inr (Or.inr (Or.inr hs))
  · rintro (he | ⟨a, he⟩ | he | he) <;> simp [he]

theorem valid_vars_iff (a b : Role) (hab : a ≠ b) (i j : ℕ) :
    Valid selected (.var i, .var j) ↔ i = j := by
  classical
  constructor
  · intro h
    by_contra hij
    have hv := h (fun k => if k = i then WinnerSet.singleton a else WinnerSet.singleton b)
    exact hab (WinnerSet.singleton_inj.mp (by simpa [Term.eval_var, Ne.symm hij] using hv))
  · rintro rfl valuation
    rfl

theorem valid_empty_iff (a b : Role) (hab : a ≠ b) (hselected : selected = ∅)
    (s t : Term selected ℕ) : Valid selected (s, t) ↔ s = t := by
  obtain ⟨i, rfl⟩ := Term.exists_var_of_empty hselected s
  obtain ⟨j, rfl⟩ := Term.exists_var_of_empty hselected t
  rw [valid_vars_iff a b hab]
  exact ⟨congrArg _, fun he => FirstOrder.Language.Term.var.inj he⟩

end KFOL.Raw

namespace KFOL.Raw

universe u

/- The reduction selected from an arbitrary nontrivial raw signature uses
only its actual operations and introduces no abstraction hypothesis. -/
theorem exists_cnf_reduction {Role : Type u} (three : Fin 3 ↪ Role)
    (selected : Finset (Operation Role)) (hcard : 1 < selected.card) :
    ∃ reduction : Reductions.CNF → Term selected ℕ × Term selected ℕ,
      ∀ formula, Valid selected (reduction formula) ↔ ¬Reductions.Satisfiable formula := by
  rcases exists_hard_pair selected hcard with ⟨hr, hu⟩ | ⟨a, b, hab, ha, hb⟩ | ⟨a, ha, hu⟩ | ⟨a, ha, hr⟩
  · exact ⟨Reduction.resetUnion selected hr hu, Reduction.valid_resetUnion_iff selected three hr hu⟩
  · obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
    exact ⟨Reduction.twoChoices selected a b ha hb,
      Reduction.valid_twoChoices_iff selected a b c hab hca.symm hcb ha hb⟩
  · obtain ⟨b, hba, _⟩ := exists_role_outside_pair three a a
    obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
    exact ⟨Reduction.choiceUnion selected a ha hu,
      Reduction.valid_choiceUnion_iff selected a b c hba.symm hca.symm hcb ha hu⟩
  · obtain ⟨b, hba, _⟩ := exists_role_outside_pair three a a
    obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
    exact ⟨Reduction.resetChoice selected a ha hr,
      Reduction.valid_resetChoice_iff selected a b c hba.symm hca.symm hcb.symm ha hr⟩

end KFOL.Raw
