module

public import KFOL.Policies.SinglePolicy
public import KFOL.Reset.Selection

/-! The two-owner selective operation is exactly a policy operation, and is
strictly more expressive than reset on every three-distinct-role carrier. -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

/-- The ordered two-choice expression has exactly two blocking atoms. -/
theorem two_choice_selective (a b : Role) (hab : a ≠ b) (Y Z : WinnerSet Role) :
    choice a (choice b Y Z) Y = selective {a, b} Z Y := by
  classical
  by_cases hYa : Y = singleton a
  · have hb : PolicyBlocks {a, b} Y := (policyBlocks_pair a b Y).mpr (Or.inl hYa)
    simp only [selective, hb, ite_true]
    simp [choice, hYa]
  · by_cases hYb : Y = singleton b
    · have hb : PolicyBlocks {a, b} Y := (policyBlocks_pair a b Y).mpr (Or.inr hYb)
      simp only [selective, hb, ite_true]
      have hi : choice b Y Z = Y := by simp [choice, hYb]
      rw [hi, choice_self]
    · have hb : ¬PolicyBlocks {a, b} Y := fun hb => (policyBlocks_pair a b Y).mp hb |>.elim hYa hYb
      simp only [selective, hb, ite_false]
      by_cases hZb : Z = singleton b
      · have hi : choice b Y Z = singleton b := by simp [choice, hZb]
        calc
          _ = (singleton b).union Y := by rw [hi]; simp [choice, singleton_inj, Ne.symm hab, hYa]
          _ = Y.union Z := by rw [hZb]; exact union_comm _ _
      · have hi : choice b Y Z = Y.union Z := by simp [choice, hYb, hZb]
        have hn : Y.union Z ≠ singleton a := fun he => hYa ((union_eq_singleton_iff Y Z a).mp he).1
        rw [hi]
        simp only [choice, hn, hYa, false_or, ite_false]
        apply Subtype.ext
        ext k
        simp only [val_union, Set.mem_union]
        tauto

/-- G and the policy operation agree on every valuation, independently of
any finite table or equation checker. -/
theorem twoOwnerSelective_eq_policyReset (a b : Role) (hab : a ≠ b) (X Y Z : WinnerSet Role) :
    twoOwnerSelective a b X Y Z = policyReset {a, b} X Y Z := by
  rw [twoOwnerSelective, policyReset, two_choice_selective a b hab]

theorem twoOwnerSelective_comm (a b : Role) (hab : a ≠ b) (X Y Z : WinnerSet Role) :
    twoOwnerSelective a b X Y Z = twoOwnerSelective b a X Y Z := by
  rw [twoOwnerSelective_eq_policyReset a b hab, twoOwnerSelective_eq_policyReset b a (Ne.symm hab), Set.pair_comm]

/-- The main paper's exact separating inputs for reset nondefinability. -/
theorem twoOwnerSelective_separates (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a ∉ (twoOwnerSelective a b ((singleton b).union (singleton c)) (singleton b) (singleton a)).val ∧
      a ∈ (twoOwnerSelective a b ((singleton b).union (singleton c)) (singleton c) (singleton a)).val := by
  have hX : ((singleton b).union (singleton c)).Ambiguous :=
    ambiguous_of_two_mem _ b c hbc (Or.inl rfl) (Or.inr rfl)
  have haX : a ∉ ((singleton b).union (singleton c)).val := by
    rintro (he | he)
    · exact hab he
    · exact hac he
  have hb : ¬PolicyPasses {a, b} a (singleton b) := fun hp => hp b (Or.inr rfl) (Ne.symm hab) rfl
  have hc : PolicyPasses {a, b} a (singleton c) := by
    apply (policyPasses_singleton _ _ _).mpr
    left
    intro h
    rcases h with he | he
    · exact hac he.symm
    · exact hbc (Set.mem_singleton_iff.mp he).symm
  rw [twoOwnerSelective_eq_policyReset a b hab, twoOwnerSelective_eq_policyReset a b hab,
    mem_policyReset, mem_policyReset]
  constructor
  · rintro (h | ⟨_, h | ⟨hp, _⟩⟩)
    · exact haX h
    · exact hab h
    · exact hb hp
  · exact Or.inr ⟨hX, Or.inr ⟨hc, rfl⟩⟩

end KFOL.WinnerSet

namespace KFOL.Policies

universe u

/-- No reset-only native term, of any depth, defines the two-owner operation.
The two evaluations preserve all input ambiguity and possible-a statuses. -/
theorem twoOwnerSelective_not_reset_definable {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∃ t : Reset.Term (Fin 3), ∀ v : Fin 3 → WinnerSet Role,
      t.eval v = WinnerSet.twoOwnerSelective a b (v 0) (v 1) (v 2) := by
  rintro ⟨t, ht⟩
  let X := (WinnerSet.singleton b).union (WinnerSet.singleton c)
  let v : Fin 3 → WinnerSet Role := ![X, WinnerSet.singleton b, WinnerSet.singleton a]
  let w : Fin 3 → WinnerSet Role := ![X, WinnerSet.singleton c, WinnerSet.singleton a]
  have hM : {i | (v i).Ambiguous} = {i | (w i).Ambiguous} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · rfl
    · constructor
      · intro h; exact False.elim (h b rfl)
      · intro h; exact False.elim (h c rfl)
    · rfl
  have hV (i : Fin 3) : a ∈ (v i).val ↔ a ∈ (w i).val := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · rfl
    · constructor
      · intro h; exact False.elim (hab h)
      · intro h; exact False.elim (hac h)
    · rfl
  have hobs : a ∈ (t.eval v).val ↔ a ∈ (t.eval w).val := by
    rw [t.mem_eval, t.mem_eval, hM]
    constructor
    · rintro ⟨i, hi, ha⟩
      exact ⟨i, hi, (hV i).mp ha⟩
    · rintro ⟨i, hi, ha⟩
      exact ⟨i, hi, (hV i).mpr ha⟩
  have hsep := WinnerSet.twoOwnerSelective_separates a b c hab hac hbc
  have hw : a ∈ (t.eval w).val := by
    rw [ht w]
    exact hsep.2
  have hv := hobs.mpr hw
  rw [ht v] at hv
  exact hsep.1 hv

namespace Term

/-- Either named owner's observation is complete for the two-owner extension.
The conclusion quantifies over all valuations, not a finite sample. -/
theorem twoOwner_observation_equation_iff {Role : Type u} {Label : Type*} {Var : Type*}
    (three : Fin 3 ↪ Role) (a b observer : Role) (hab : a ≠ b)
    (hobs : observer = a ∨ observer = b) (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role,
      left.eval (fun _ => ({a, b} : Set Role)) v = right.eval (fun _ => ({a, b} : Set Role)) v) ↔
      ∀ v : Var → WinnerSet Role,
        observer ∈ (left.eval (fun _ => ({a, b} : Set Role)) v).val ↔
          observer ∈ (right.eval (fun _ => ({a, b} : Set Role)) v).val := by
  classical
  obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
  have hc : c ∉ ({a, b} : Set Role) := by
    rintro (he | he)
    · exact hca he
    · exact hcb (Set.mem_singleton_iff.mp he)
  rcases hobs with hobs | hobs
  · subst observer
    exact single_observation_equation_iff {a, b} a b c (Or.inr rfl) hc hab (Ne.symm hca) left right
  · subst observer
    exact single_observation_equation_iff {a, b} b a c (Or.inl rfl) hc (Ne.symm hab) (Ne.symm hcb) left right

/-- The concrete syntax-only checker decides equality in the G signature. -/
theorem twoOwner_equationB_correct {Role : Type u} {Label : Type*} {Var : Type*} [DecidableEq Var]
    (three : Fin 3 ↪ Role) (a b : Role) (left right : Term Label Var) :
    singleEquationB left right = true ↔ ∀ v : Var → WinnerSet Role,
      left.eval (fun _ => ({a, b} : Set Role)) v = right.eval (fun _ => ({a, b} : Set Role)) v := by
  obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
  have hc : c ∉ ({a, b} : Set Role) := by
    rintro (he | he)
    · exact hca he
    · exact hcb (Set.mem_singleton_iff.mp he)
  exact singleEquationB_correct three {a, b} ⟨a, Or.inl rfl⟩ ⟨c, hc⟩ left right

end Term

end KFOL.Policies
