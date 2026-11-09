module

public import KFOL.Algebra.TwoPlayers.Kleene.Winner

/-! # Every original public term has a canonical bounded Kleene term -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

open Classical

variable {Role : Type u}

/-- On two roles, every internal permutation is identity or the one swap. -/
theorem permutation_cases (e : Fin 2 ≃ Role) (p : Equiv.Perm Role) :
    p = 1 ∨ p = Equiv.swap (e 0) (e 1) := by
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  rcases role_cases e (p (e 0)) with h0 | h0
  · have h1 : p (e 1) = e 1 := by
      rcases role_cases e (p (e 1)) with h1 | h1
      · exact False.elim (hne (p.injective (h0.trans h1.symm)))
      · exact h1
    apply Or.inl
    ext r
    rcases role_cases e r with rfl | rfl <;> assumption
  · have h1 : p (e 1) = e 0 := by
      rcases role_cases e (p (e 1)) with h1 | h1
      · exact h1
      · exact False.elim (hne (p.injective (h0.trans h1.symm)))
    apply Or.inr
    ext r
    rcases role_cases e r with rfl | rfl <;> simp_all

/-- Translate the original syntax, with arbitrary role constants and arbitrary
internal permutations, into the five-operation canonical Kleene signature. -/
noncomputable def ofPublic {Var : Type v} (e : Fin 2 ≃ Role) : KFOL.Term Role Var → Term Var
  | .winner r => if r = e 1 then botTerm else topTerm
  | .var x => .var x
  | .choice r s t => if r = e 0 then joinTerm (ofPublic e s) (ofPublic e t)
      else meetTerm (ofPublic e s) (ofPublic e t)
  | .rename p t => if p (e 0) = e 0 then ofPublic e t else negTerm (ofPublic e t)

/-- The canonical finite signature loses none of the original public term
functions, including terms with internal switches at arbitrary depth. -/
theorem realize_ofPublic {Var : Type v} (e : Fin 2 ≃ Role) (t : KFOL.Term Role Var)
    (v : Var → WinnerSet Role) :
    let _ := winnerStructure e
    (ofPublic e t).realize v = t.eval v := by
  let := winnerStructure e
  dsimp only
  induction t with
  | winner r =>
    rcases role_cases e r with rfl | rfl
    · simp only [ofPublic,show e 0 ≠ e 1 from e.injective.ne (by decide),ite_false]
      rfl
    · simp only [ofPublic,ite_true]
      rfl
  | var x => rfl
  | choice r s t hs ht =>
    rcases role_cases e r with rfl | rfl
    · simp only [ofPublic,ite_true]
      change WinnerSet.choice (e 0) ((ofPublic e s).realize v) ((ofPublic e t).realize v) =
        WinnerSet.choice (e 0) (s.eval v) (t.eval v)
      rw [hs,ht]
    · simp only [ofPublic,show e 1 ≠ e 0 from e.injective.ne (by decide),ite_false]
      change WinnerSet.choice (e 1) ((ofPublic e s).realize v) ((ofPublic e t).realize v) =
        WinnerSet.choice (e 1) (s.eval v) (t.eval v)
      rw [hs,ht]
  | rename p t ht =>
    rcases permutation_cases e p with rfl | rfl
    · simpa only [ofPublic,Equiv.Perm.one_apply,ite_true,KFOL.Term.eval,WinnerSet.rename_one] using ht
    · simp only [ofPublic,Equiv.swap_apply_left,show e 1 ≠ e 0 from e.injective.ne (by decide),ite_false]
      change WinnerSet.rename (Equiv.swap (e 0) (e 1)) ((ofPublic e t).realize v) =
        WinnerSet.rename (Equiv.swap (e 0) (e 1)) (t.eval v)
      exact congrArg (WinnerSet.rename (Equiv.swap (e 0) (e 1))) ht

/-- The finite presentation decides exactly the identities of the original
full syntax after the semantics-preserving canonical translation. -/
theorem public_equational_completeness (e : Fin 2 ≃ Role) (n : Nat)
    (s t : KFOL.Term Role (Fin n)) :
    (∀ v : Fin n → WinnerSet Role, s.eval v = t.eval v) ↔
      Equational.Derives basis (ofPublic e s) (ofPublic e t) := by
  let := winnerStructure e
  have h := basis_winner e ⟨n,ofPublic e s,ofPublic e t⟩
  exact (show (∀ v : Fin n → WinnerSet Role, s.eval v = t.eval v) ↔
      (⟨n,ofPublic e s,ofPublic e t⟩ : Equational.Identity Symbol).Holds (WinnerSet Role) from
    ⟨fun h v => (realize_ofPublic e s v).trans ((h v).trans (realize_ofPublic e t v).symm),
      fun h v => (realize_ofPublic e s v).symm.trans ((h v).trans (realize_ofPublic e t v))⟩).trans h

end KFOL.TwoPlayers.Kleene
