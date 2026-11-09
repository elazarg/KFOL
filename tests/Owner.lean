module

public import KFOL.Owner

/-! Original occurrence guards and one-outsider executable comparisons. -/

@[expose] public section

namespace KFOLTest.Owner

open KFOL

private def x : Owner.Term (Fin 3) (Fin 3) := .var 0
private def y : Owner.Term (Fin 3) (Fin 3) := .var 1
private def z : Owner.Term (Fin 3) (Fin 3) := .var 2
private def h : Owner.Term (Fin 3) (Fin 3) := Owner.Term.guarded 0 x y z

example : h.root = 0 := by decide
example : h.guards 1 = [⟨0, [], []⟩, ⟨1, [0], [2, 1]⟩, ⟨2, [0], [2, 1]⟩] := by decide
example : h.guards 0 = [⟨0, [], []⟩, ⟨1, [0], []⟩, ⟨2, [0], []⟩] := by decide
example : h.leafCount = 3 := by decide
example : h.OwnersIn (fun r => r = 0) := ⟨rfl, trivial, trivial, trivial⟩

example : Owner.Term.equationB 1 h x = false := by decide
example : Owner.Term.equationB 2 h x = false := by decide
example : Owner.Term.equationB 1 (Owner.Term.guarded 0 x x x) x = true := by decide
example : Owner.Term.equationB 1 (Owner.Term.step x y) (Owner.Term.guarded 0 y x x) = true := by decide
example : Owner.Term.equationB 1 (Owner.Term.guarded 0 x y z)
    (Owner.Term.guarded 0 x z y) = true := by decide

private def weak : Owner.Guard (Fin 3) := ⟨1, [], [1]⟩
private def strong : Owner.Guard (Fin 3) := ⟨1, [0], [2]⟩

-- The source itself discharges the non-owner-atom test.
example : Owner.dominatesB weak strong = true := by decide
example : Owner.dominatesB strong weak = false := by decide
example : Owner.coversB [strong] [weak] = true := by decide
example : Owner.coversB [] [weak] = true := by decide
example : Owner.coversB [weak] [] = false := by decide

example (v : Fin 3 → WinnerSet (Fin 3)) : h.eval v = WinnerSet.singleton 2 ↔ v 0 = WinnerSet.singleton 2 :=
  h.eq_singleton_iff v 2
example (v : Fin 3 → WinnerSet (Fin 3)) : (h.eval v).Ambiguous ↔ (v 0).Ambiguous :=
  h.ambiguous_iff v

end KFOLTest.Owner
