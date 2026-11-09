module

public import KFOL.Algebra.Atomic.BinaryCore
public import KFOL.Reset.Public

/-! # Exact classification of idempotent atom-preserving binary operations -/

@[expose] public section

namespace KFOL.Term

universe u

variable {Role : Type u}

/-- Every idempotent atom-preserving full-language binary term is one of
exactly four winner-set operations: two projections and two oriented resets. -/
theorem binary_atom_preserving (three : Fin 3 ↪ Role) (t : Term Role (Fin 2))
    (ha : t.AtomPreserving) (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 1).reset (v 0)) := by
  obtain ⟨hc,he,_⟩ := t.idempotent_extraction three hd
  obtain ⟨i,hp⟩ := t.atomic_determinacy three ha (fun r => hd (WinnerSet.singleton r))
  have hpc : (t.pushRenames 1).AtomicRealizes (fun v => v i) :=
    fun v => (he _).trans (hp v)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rcases hc.binary_of_atomic_projection three 0 1 (by decide) hpc with h | h
    · exact Or.inl (fun v => (he v).symm.trans (h v))
    · exact Or.inr (Or.inr (Or.inr (fun v => (he v).symm.trans (h v))))
  · rcases hc.binary_of_atomic_projection three 1 0 (by decide) hpc with h | h
    · exact Or.inr (Or.inl (fun v => (he v).symm.trans (h v)))
    · exact Or.inr (Or.inr (Or.inl (fun v => (he v).symm.trans (h v))))

/-- Each of the four classified operations is represented by a reset term. -/
theorem binary_reset_representation (three : Fin 3 ↪ Role) (t : Term Role (Fin 2))
    (ha : t.AtomPreserving) (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    ∃ s : Reset.Term (Fin 2), ∀ v : Fin 2 → WinnerSet Role, t.eval v = s.eval v := by
  rcases t.binary_atom_preserving three ha hd with h | h | h | h
  · exact ⟨.var 0,h⟩
  · exact ⟨.var 1,h⟩
  · exact ⟨Reset.Term.step (.var 0) (.var 1),h⟩
  · exact ⟨Reset.Term.step (.var 1) (.var 0),h⟩

/-- The four-way semantic description is also sufficient. Every operation
in it has an actual core term, with idempotence and atom preservation proved
for that term. This closes both directions of the binary classification. -/
theorem binary_operation_classification [Finite Role] (three : Fin 3 ↪ Role)
    (f : (Fin 2 → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role (Fin 2), t.IsCore ∧ t.AtomPreserving ∧
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧ (∀ v, t.eval v = f v)) ↔
    (∀ v : Fin 2 → WinnerSet Role, f v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 1).reset (v 0)) := by
  classical
  constructor
  · rintro ⟨t,_,ha,hd,he⟩
    rcases t.binary_atom_preserving three ha hd with h | h | h | h
    · exact Or.inl (fun v => (he v).symm.trans (h v))
    · exact Or.inr (Or.inl (fun v => (he v).symm.trans (h v)))
    · exact Or.inr (Or.inr (Or.inl (fun v => (he v).symm.trans (h v))))
    · exact Or.inr (Or.inr (Or.inr (fun v => (he v).symm.trans (h v))))
  · intro h
    let := Fintype.ofFinite Role
    have reset (i j : Fin 2) : ∃ t : Term Role (Fin 2), t.IsCore ∧ t.AtomPreserving ∧
        (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
        (∀ v, t.eval v = (v i).reset (v j)) := by
      let t := Reset.Term.resetTerm three Finset.univ.toList (.var i) (.var j)
      have hc : t.IsCore := Reset.Term.isCore_resetTerm three _ _ _ trivial trivial
      have he (v : Fin 2 → WinnerSet Role) : t.eval v = (v i).reset (v j) :=
        Reset.Term.eval_resetTerm three Finset.univ.toList (by simp) _ _ v
      refine ⟨t,hc,?_,hc.eval_diagonal,he⟩
      intro v
      exact ⟨v j,(he _).trans (WinnerSet.reset_singleton _ _)⟩
    rcases h with h | h | h | h
    · exact ⟨.var 0,trivial,fun v => ⟨v 0,rfl⟩,fun _ => rfl,fun v => (h v).symm⟩
    · exact ⟨.var 1,trivial,fun v => ⟨v 1,rfl⟩,fun _ => rfl,fun v => (h v).symm⟩
    · obtain ⟨t,hc,ha,hd,he⟩ := reset 0 1
      exact ⟨t,hc,ha,hd,fun v => (he v).trans (h v).symm⟩
    · obtain ⟨t,hc,ha,hd,he⟩ := reset 1 0
      exact ⟨t,hc,ha,hd,fun v => (he v).trans (h v).symm⟩

end KFOL.Term
