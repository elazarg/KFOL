module

public import KFOL.Algebra.TwoPlayers.Degeneracies

/-! # The three-role idempotent characterization fails with two players -/

@[expose] public section

namespace KFOL.TwoPlayers

universe u v

open Classical

variable {Role : Type u}

@[simp] theorem rank_choice_top (e : Fin 2 ≃ Role) (A B : WinnerSet Role) :
    rank e (WinnerSet.choice (e 0) A B) = max (rank e A) (rank e B) := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  obtain ⟨j,rfl⟩ := value_surjective e B
  simp only [choice_top,rank_value]

@[simp] theorem rank_choice_bottom (e : Fin 2 ≃ Role) (A B : WinnerSet Role) :
    rank e (WinnerSet.choice (e 1) A B) = min (rank e A) (rank e B) := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  obtain ⟨j,rfl⟩ := value_surjective e B
  simp only [choice_bottom,rank_value]

@[simp] theorem rank_rename_swap (e : Fin 2 ≃ Role) (A : WinnerSet Role) :
    rank e (WinnerSet.rename (Equiv.swap (e 0) (e 1)) A) = (rank e A).rev := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  simp only [rename_swap,rank_value]

/-- Every core operation is increasing in the two-player truth chain. -/
theorem core_monotone (e : Fin 2 ≃ Role) {Var : Type v} {t : Term Role Var}
    (ht : t.IsCore) (v w : Var → WinnerSet Role) (hvw : ∀ x, rank e (v x) ≤ rank e (w x)) :
    rank e (t.eval v) ≤ rank e (t.eval w) := by
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x => exact hvw x
  | choice r s t hs ht' =>
    rcases role_cases e r with rfl | rfl
    · simpa only [Term.eval,rank_choice_top] using max_le_max (hs ht.1) (ht' ht.2)
    · simpa only [Term.eval,rank_choice_bottom] using min_le_min (hs ht.1) (ht' ht.2)

/-- A genuine two-player idempotent operation requiring an internal switch:
`x ∨ (y ∧ ¬y)` decreases as `y` rises from ambiguity to top, whereas every
core operation is increasing. This proves failure of the semantic core
characterization, rather than only the presence of a redundant winner leaf. -/
theorem idempotent_not_core (e : Fin 2 ≃ Role) :
    ∃ t : Term Role (Fin 2),
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
      ¬∃ s : Term Role (Fin 2), s.IsCore ∧ (∀ v : Fin 2 → WinnerSet Role, s.eval v = t.eval v) := by
  let t : Term Role (Fin 2) := .choice (e 0) (.var 0)
    (.choice (e 1) (.var 1) (.rename (Equiv.swap (e 0) (e 1)) (.var 1)))
  refine ⟨t,?_,?_⟩
  · intro A
    apply (equiv e).injective
    change rank e (t.eval (fun _ => A)) = rank e A
    simp [t,Term.eval]
  · rintro ⟨s,hs,he⟩
    let v : Fin 2 → WinnerSet Role := fun i => value e (if i = 0 then 0 else 1)
    let w : Fin 2 → WinnerSet Role := fun i => value e (if i = 0 then 0 else 2)
    have hvw : ∀ i, rank e (v i) ≤ rank e (w i) := by
      intro i
      simp only [v,w,rank_value]
      by_cases hi : i = 0 <;> simp [hi]
    have hmono := core_monotone e hs v w hvw
    rw [he v,he w] at hmono
    have hbad : ¬rank e (t.eval v) ≤ rank e (t.eval w) := by
      simp [t,Term.eval,v,w,rank_value]
    exact hbad hmono

end KFOL.TwoPlayers
