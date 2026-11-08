module

public import KFOL.Reset.Basis.Coverage
public import KFOL.Reset.Chain
public import KFOL.Equational.Completeness
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Finite.Range

/-! # The explicit six equations and their arbitrary-model interpretation -/

@[expose] public section

namespace KFOL.Reset

universe u v

variable {Var : Type v} {M : Type u} [(Equational.language Symbol).Structure M]

@[simp] theorem realize_step (s t : Term Var) (v : Var → M) :
    (Term.step s t).realize v = operation M (s.realize v) (t.realize v) := by
  unfold Term.step operation
  simp only [FirstOrder.Language.Term.realize]
  congr 1
  funext i
  split_ifs <;> rfl

/-- Interpretation using the extracted operation is the original realization. -/
theorem interpret_operation {Var : Type v} (t : Term Var) (v : Var → M) :
    interpret (operation M) v t = t.realize v := by
  induction t using Term.induction_reset with
  | var => rfl
  | step s t hs ht =>
    change operation M (interpret (operation M) v s) (interpret (operation M) v t) = _
    rw [hs, ht, realize_step]

private def valuation3 (x y z : M) (i : Fin 3) : M :=
  if i = 0 then x else if i = 1 then y else z

/-- The data family is equivalent to the independently stated six algebra laws. -/
theorem models_basis_iff : Equational.Models basis M ↔ Laws (operation M) := by
  constructor
  · intro hm
    have ax (i : Fin 6) := hm (basisAxiom i) ⟨i, rfl⟩
    constructor
    · intro x
      simpa [basisAxiom, valuation3] using ax 0 (fun _ => x)
    · intro x y
      simpa [basisAxiom, valuation3] using ax 1 (valuation3 x y x)
    · intro x y
      simpa [basisAxiom, valuation3] using ax 2 (valuation3 x y x)
    · intro x y z
      simpa [basisAxiom, valuation3] using ax 3 (valuation3 x y z)
    · intro x y z
      simpa [basisAxiom, valuation3] using ax 4 (valuation3 x y z)
    · intro x y z
      simpa [basisAxiom, valuation3] using ax 5 (valuation3 x y z)
  · intro h e he v
    obtain ⟨i, rfl⟩ := he
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change Fin 3 → M at v
    all_goals simp [basisAxiom]
    · exact h.idem _
    · exact h.absorb _ _
    · exact h.repeat_right _ _
    · exact h.nested _ _ _
    · exact h.exchange _ _ _
    · exact h.left_comm _ _ _

/-- Soundness holds for arbitrary role sets, without assuming three roles. -/
theorem winnerSet_laws (Role : Type u) : Laws (WinnerSet.reset (Role := Role)) := by
  constructor
  · exact WinnerSet.reset_self
  all_goals
    intros
    apply Subtype.ext
    ext r
    simp only [WinnerSet.mem_reset, WinnerSet.ambiguous_reset]
    tauto

/-- A syntactic node count used solely to distinguish the six explicit axioms. -/
private def nodes {Var : Type v} : Term Var → ℕ
  | .var _ => 1
  | .func .reset args => 1 + nodes (args 0) + nodes (args 1)

private def fingerprint (i : Fin 6) : ℕ × ℕ :=
  (nodes (basisAxiom i).lhs, (Term.root (basisAxiom i).lhs).val)

private theorem fingerprint_injective : Function.Injective fingerprint := by decide

theorem basisAxiom_injective : Function.Injective basisAxiom := by
  intro i j he
  apply fingerprint_injective
  exact congrArg (fun e : Equational.Identity Symbol => (nodes e.lhs, (Term.root e.lhs).val)) he

theorem basis_finite : basis.Finite := Set.finite_range basisAxiom

/-- All six equations are present and distinct; no finite search is trusted. -/
theorem card_basis : Nat.card basis = 6 := by
  have he := Nat.card_congr (Equiv.ofInjective basisAxiom basisAxiom_injective)
  simpa only [basis, Nat.card_fin] using he.symm

end KFOL.Reset
