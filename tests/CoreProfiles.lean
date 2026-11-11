import KFOL.Core.ProfileSynthesis

open KFOL

private def family (r : Fin 3) (v : Fin 3 → Bool) : Bool :=
  if r = 0 then (v 0 || v 1) && v 2
  else if r = 1 then v 0 && v 1
  else v 0 && v 1 && v 2

set_option maxRecDepth 4096 in
private theorem compatible : Core.AdmissibleProfiles family := by
  constructor <;> decide

-- The predicates are synthesized together, rather than independently.
example : ∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 3),
    ∀ i v, Core.profile i v t = family i v :=
  (Core.exists_term_iff_admissibleProfiles (Function.Embedding.refl _) family).mpr compatible

private def majority (_ : Fin 3) (v : Fin 3 → Bool) : Bool :=
  (v 0 && v 1) || (v 0 && v 2) || (v 1 && v 2)

-- Pairwise intersection is insufficient: these three winning pairs have
-- empty total intersection. This rejects a weaker compatibility condition.
example : ¬Core.AdmissibleProfiles majority := by
  intro h
  obtain ⟨x, hx⟩ := h.common_source (fun r j => decide (r ≠ j)) (by decide)
  simpa using hx x

-- Arity zero is covered without inventing a constant-free leaf.
example : ¬Core.AdmissibleProfiles (fun (_ : Fin 3) (_ : Fin 0 → Bool) => true) := by
  intro h
  obtain ⟨x, _⟩ := h.common_source (fun _ _ => true) (by simp)
  exact Fin.elim0 x
