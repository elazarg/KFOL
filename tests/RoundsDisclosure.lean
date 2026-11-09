module

import KFOL.Rounds.Disclosure

/- Two-bit commitments in a two-round game, including the second-round
public histories that a strategy may assign zero probability. -/

namespace KFOL.Rounds.DisclosureTest

open GameTheory.Languages GameTheory.Protocol
open Bridges.FOSGToEFG

noncomputable section

abbrev source := observed (Fin 2) 2
abbrev order : ExplicitOrder (Fin 2) := ⟨2, Equiv.refl _⟩

def committedPrefix (h : source.execution.History) (before : h.state.length < 2) (bit : Bool) :
    Prefix source order h 1 :=
  (Prefix.initial h).advance (by decide)
    ⟨some bit, by exact ⟨before, Set.mem_univ _⟩⟩

example (h : source.execution.History) (before : h.state.length < 2) :
    viewOfState source order 1 (.stage h 1 (committedPrefix h before false)) =
      viewOfState source order 1 (.stage h 1 (committedPrefix h before true)) :=
  hidden_prefix 2 order h 1 _ _ 1

example (bit : Bool) :
    let h := appendPublicHistory (Role := Fin 2) 2 source.execution.initHistory (fun _ => bit) (by change (0 : ℕ) < 2; decide)
    h.state.length = 1 ∧
      viewOfState source order 1 (.stage h 1 (committedPrefix h (by change (1 : ℕ) < 2; decide) false)) =
      viewOfState source order 1 (.stage h 1 (committedPrefix h (by change (1 : ℕ) < 2; decide) true)) := by
  dsimp only
  exact ⟨by simp, hidden_prefix 2 order _ 1 _ _ 1⟩

#print axioms KFOL.Rounds.hidden_prefix
#print axioms KFOL.Rounds.serial_information
#print axioms KFOL.Rounds.public_step

end
end KFOL.Rounds.DisclosureTest
