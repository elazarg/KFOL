module

public import KFOL.Algebra.TwoPlayers.Algebra
public import KFOL.Definitions.Atomic
public import KFOL.Algebra.Basic
public import KFOL.Definitions.Policies
public import KFOL.Reset.Basic

/-! # Atomic public values and projection degeneracies with two players -/

@[expose] public section

namespace KFOL.TwoPlayers

universe u v

open Classical

variable {Role : Type u}

theorem middle_mem (e : Fin 2 ≃ Role) (r : Role) : r ∈ (value e 1).val := by
  rcases role_cases e r with rfl | rfl <;> simp [value]

theorem union_middle (e : Fin 2 ≃ Role) (A : WinnerSet Role) : A.union (value e 1) = value e 1 := by
  apply Subtype.ext
  ext r
  exact ⟨fun _ => middle_mem e r,fun h => Or.inr h⟩

theorem ambiguous_iff_middle (e : Fin 2 ≃ Role) (A : WinnerSet Role) :
    A.Ambiguous ↔ A = value e 1 := by
  constructor
  · intro h
    obtain ⟨i,rfl⟩ := value_surjective e A
    fin_cases i
    · exact False.elim (h (e 1) rfl)
    · rfl
    · exact False.elim (h (e 0) rfl)
  · rintro rfl
    exact ambiguous_middle e

/-- With two roles reset is exactly its right projection. -/
theorem reset_projection (e : Fin 2 ≃ Role) (A B : WinnerSet Role) : A.reset B = B := by
  by_cases hb : B.Ambiguous
  · rw [WinnerSet.reset_of_ambiguous _ _ hb,(ambiguous_iff_middle e B).mp hb,union_middle]
  · simp [WinnerSet.reset,hb]

/-- Every owner guard degenerates to its root projection. -/
theorem guardedChoice_projection (e : Fin 2 ≃ Role) (r : Role) (X Y Z : WinnerSet Role) :
    WinnerSet.guardedChoice r X Y Z = X :=
  reset_projection e _ _

/-- Every policy-family operation also degenerates to its root projection. -/
theorem policyReset_projection (e : Fin 2 ≃ Role) (D : Set Role) (X Y Z : WinnerSet Role) :
    WinnerSet.policyReset D X Y Z = X :=
  reset_projection e _ _

/-- The two atoms are closed under every owned choice. -/
theorem choice_atoms (e : Fin 2 ≃ Role) (r a b : Role) :
    ∃ q, WinnerSet.choice r (WinnerSet.singleton a) (WinnerSet.singleton b) = WinnerSet.singleton q := by
  by_cases ha : a = r
  · exact ⟨r,by simp [ha,WinnerSet.choice]⟩
  by_cases hb : b = r
  · exact ⟨r,by simp [hb,WinnerSet.choice]⟩
  have hab : a = b := by
    rcases role_cases e r with rfl | rfl <;>
      rcases role_cases e a with rfl | rfl <;>
      rcases role_cases e b with rfl | rfl <;> simp_all
  subst b
  exact ⟨a,WinnerSet.choice_idempotent _ _⟩

/-- Every full-language two-player term preserves atoms, including constants
and internal switches. -/
theorem atom_preserving (e : Fin 2 ≃ Role) {Var : Type v} (t : Term Role Var) :
    t.AtomPreserving := by
  intro v
  induction t with
  | winner r => exact ⟨r,rfl⟩
  | var x => exact ⟨v x,rfl⟩
  | choice r s t hs ht =>
    obtain ⟨a,ha⟩ := hs
    obtain ⟨b,hb⟩ := ht
    simpa only [Term.eval,ha,hb] using choice_atoms e r a b
  | rename p t ht =>
    obtain ⟨r,hr⟩ := ht
    exact ⟨p r,by simp [Term.eval,hr]⟩

/-- In particular a public closed game reaches an atom; ambiguity is not a
closed public value. -/
theorem closed_atomic (e : Fin 2 ≃ Role) (t : Term Role Empty)
    (v : Empty → WinnerSet Role) : ∃ r, t.eval v = WinnerSet.singleton r := by
  let atomic : Empty → Role := Empty.elim
  have hv : (fun x => WinnerSet.singleton (atomic x)) = v := funext (fun x => x.elim)
  simpa only [hv] using atom_preserving e t atomic

/-- Neutral union cannot be represented in the two-player public syntax. -/
theorem union_not_definable (e : Fin 2 ≃ Role) :
    ¬∃ t : Term Role (Fin 2), ∀ v : Fin 2 → WinnerSet Role,
      t.eval v = (v 0).union (v 1) := by
  rintro ⟨t,ht⟩
  obtain ⟨r,hr⟩ := atom_preserving e t e
  have he : t.eval (fun x => WinnerSet.singleton (e x)) = value e 1 := by
    simpa only [value,show ¬((1 : Fin 3) = 0) from by decide,ite_false,ite_true] using
      ht (fun x => WinnerSet.singleton (e x))
  exact ambiguous_middle e r (he.symm.trans hr)

end KFOL.TwoPlayers
