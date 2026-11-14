module

public import KFOL.AtomicLogic.Substitution
public import KFOL.Reset.Public
public import KFOL.Equational.Native

/-! # Atomic validity is not an ordinary one-sorted equational theory -/

@[expose] public section

namespace KFOL.AtomicLogic

universe u

noncomputable def roles {Role : Type u} [Fintype Role] : List Role := by
  classical
  exact Finset.univ.toList

theorem roles_cover {Role : Type u} [Fintype Role] (r : Role) : r ∈ roles := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ r)

/-- A native reset term, whose right projection law is valid on atomic inputs. -/
noncomputable def resetLeft {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    KFOL.Term Role (Fin 2) :=
  Reset.Term.resetTerm three roles (.var 0) (.var 1)

theorem resetLeft_valid {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    Valid (resetLeft three) (.var 1) := by
  intro valuation
  rw [resetLeft, Reset.Term.eval_resetTerm three roles roles_cover]
  simp only [KFOL.Term.eval, WinnerSet.reset_singleton]

/-- This substitution is deliberately winner-valued: its second image is a union. -/
def ambiguousSubstitution {Role : Type u} (three : Fin 3 ↪ Role)
    (i : Fin 2) : KFOL.Term Role (Fin 3) :=
  if i = 0 then .var 0 else KFOL.Term.unionTerm three (.var 1) (.var 2)

theorem resetLeft_substitution_invalid {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    ¬ Valid ((resetLeft three).subst (ambiguousSubstitution three))
      ((.var 1 : KFOL.Term Role (Fin 2)).subst (ambiguousSubstitution three)) := by
  classical
  intro h
  have e := h three
  rw [KFOL.Term.eval_subst, KFOL.Term.eval_subst, resetLeft,
    Reset.Term.eval_resetTerm three roles roles_cover] at e
  simp [ambiguousSubstitution, KFOL.Term.eval, KFOL.Term.eval_unionTerm] at e
  let pair : WinnerSet Role :=
    (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2))
  have hamb : pair.Ambiguous := by
    apply WinnerSet.ambiguous_of_two_mem pair (three 1) (three 2)
      (three.injective.ne (by decide))
    · exact Or.inl rfl
    · exact Or.inr rfl
  change (WinnerSet.singleton (three 0)).reset pair = pair at e
  rw [WinnerSet.reset_of_ambiguous _ _ hamb] at e
  have hm : three 0 ∈ ((WinnerSet.singleton (three 0)).union pair).val := Or.inl rfl
  rw [e] at hm
  change three 0 = three 1 ∨ three 0 = three 2 at hm
  rcases hm with hm | hm
  · exact (show (0 : Fin 3) ≠ 1 by decide) (three.injective hm)
  · exact (show (0 : Fin 3) ≠ 2 by decide) (three.injective hm)

/-- Arbitrary native substitution is not an admissible rule on atomic equations. -/
theorem not_substitution_closed {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    ∃ s t : KFOL.Term Role (Fin 2), Valid s t ∧
      ∃ replacement : Fin 2 → KFOL.Term Role (Fin 3),
        ¬ Valid (s.subst replacement) (t.subst replacement) :=
  ⟨resetLeft three, .var 1, resetLeft_valid three,
    ambiguousSubstitution three, resetLeft_substitution_invalid three⟩

/-- No ordinary equational theory, even infinite, has exactly the native
atom-valid equations as its consequences. The obstruction is sorting,
rather than the finite-basis obstruction for unrestricted winner inputs. -/
theorem no_unsorted_equational_presentation {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    ¬ ∃ theory : Equational.Theory (Equational.FullSymbol Role),
      ∀ (n : ℕ) (s t : KFOL.Term Role (Fin n)),
        Valid s t ↔ Equational.Derives theory (Equational.Full.encode s)
          (Equational.Full.encode t) := by
  rintro ⟨theory, exactness⟩
  obtain ⟨s, t, hvalid, replacement, hbad⟩ := not_substitution_closed three
  have proof := (exactness 2 s t).mp hvalid
  have substituted := proof.subst (fun x => Equational.Full.encode (replacement x))
  rw [← Equational.Full.encode_subst, ← Equational.Full.encode_subst] at substituted
  exact hbad ((exactness 3 _ _).mpr substituted)

end KFOL.AtomicLogic
