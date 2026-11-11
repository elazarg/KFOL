import KFOL.Core.SourceCompatibility

open KFOL Core.Sources

-- Positivity is essential: the zero array satisfies the fixed-point test.
example : interior (Function.Embedding.refl (Fin 3))
    (fun (_ : Fin 3) (_ : Fin 2) (_ : Pattern _ _) => False) =
      (fun _ _ _ => False) := by
  funext k j p
  exact propext ⟨interior_le _ _ k j p, False.elim⟩

example : ¬ Compatible (Function.Embedding.refl (Fin 3))
    (fun (_ : Fin 3) (_ : Fin 2) (_ : Pattern _ _) => False) := by
  rintro ⟨⟨_, _, _, h⟩, _⟩
  exact h

-- The nullary boundary is rejected without an assumed nonempty variable type.
example (G : ∀ (k : Fin 3) (j : Fin 0), Finset (Guard k j)) :
    ¬ Admissible (Function.Embedding.refl _) G := by
  rintro ⟨_, ⟨⟨_, j, _, _⟩, _⟩⟩
  exact Fin.elim0 j

private def bad (k : Fin 3) (_ : Unit) (_ : Pattern k ()) : Prop := k = 0

-- Even a positive monotone coefficient array can be jointly impossible.
-- In arity one idempotence forces every observer's coefficient to be true.
example : ¬ Compatible (Function.Embedding.refl (Fin 3)) bad := by
  intro h
  obtain ⟨t, ht, he⟩ := (compatible_iff _ bad).mp h
  let p : Pattern (1 : Fin 3) () := fun i => False.elim (i.property (Subsingleton.elim _ _))
  have hv : probe (Function.Embedding.refl _) 1 () p =
      (fun _ => WinnerSet.singleton 1) := by
    funext i
    cases i
    exact probe_source _ _ _ _
  have hm : 1 ∈ (t.eval (probe (Function.Embedding.refl _) 1 () p)).val := by
    rw [hv, ht.eval_diagonal]
    exact Set.mem_singleton _
  exact (show (1 : Fin 3) ≠ 0 by decide) ((he 1 () p).mp hm)
