module

public import KFOL.Core

/-! The uniform algebra specializes beyond the legacy three-owner model. -/

@[expose] public section

namespace KFOLTest.CoreBasis

open KFOL KFOL.Core

attribute [local instance] Native.structureOf Equational.coreStructure

example : Fintype.card (Native (Fin 3)) = 5 := by decide
example : Fintype.card (Native (Fin 4)) = 6 := by decide
example : Fintype.card (Native (Fin 5)) = 7 := by decide

example : Native.choice (0 : Fin 4) .upper (.atom 0) = .atom 0 := by decide
example : Native.choice (3 : Fin 4) .upper (.atom 0) = .upper := by decide
example : Native.join (Native.atom (0 : Fin 4)) (.atom 3) = .lower := by decide

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
private def valuation : Option (Fin 3) → Native (Fin 3)
  | none => .upper
  | some r => .atom r

example : (exhaustionRight three [0, 1, 2]).realize valuation = Native.lower := by decide
example : (unionTerm three (.var none) (exhaustionRight three [0, 1, 2])).realize valuation =
    Native.upper := by decide

-- The role-count obstruction quantifies over all identities, without a
-- syntactic search or a cutoff on their depth or declared arity.
example (e : Equational.Identity (Equational.CoreSymbol (Fin 4)))
    (he : e.variableCount ≤ 4) (hv : e.Holds (WinnerSet (Fin 4))) :
    e.Holds (Native (Fin 4)) := by
  let emb : Fin 3 ↪ Fin 4 := ⟨Fin.castLE (by decide), Fin.castLE_injective (by decide)⟩
  exact Native.holds_of_variableCount_le emb e (by simpa using he) hv

example : (exhaustionIdentity three).variableCount = 4 := by
  simpa using exhaustion_variableCount three

end KFOLTest.CoreBasis

#print axioms KFOL.Core.Native.generated_inVariety
#print axioms KFOL.Core.no_basis_with_role_bound
#print axioms KFOL.Core.profile_common_source
