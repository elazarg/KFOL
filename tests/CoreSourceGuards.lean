import KFOL.Core.SourceNormalForm

open KFOL Core.Sources

-- A ternary operation needs 81 indexed Boolean observations for three owners.
example : Fintype.card (ProbeIndex (Fin 3) (Fin 3)) = 81 := by
  rw [card_probeIndex]
  decide

-- Arity zero adds no fictitious source.
example : Fintype.card (ProbeIndex (Fin 3) (Fin 0)) = 0 := by
  rw [card_probeIndex]
  decide

-- Canonicalization contracts a projection to one empty source guard.
example (j : Fin 4) (k : Fin 3) :
    normalForm (Function.Embedding.refl _) (fun v => (Term.var j).eval v) k j = {∅} := by
  simp [normalForm_var]

