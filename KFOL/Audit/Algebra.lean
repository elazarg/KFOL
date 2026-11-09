module

import all KFOL.Algebra
import all KFOL.Algorithms.GuardWords
meta import Lean.Elab.Command

/-! # Independent algebra and representation import boundary

Build this module separately from Paper and the machine proofs. Inspect the
compiled transitive module list, so an indirect library dependency cannot
silently couple pure semantics to game or machine definitions.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let forbidden := #[`GameTheory, `GameTheoryComplexity, `FixedPointTheorems,
    `Complexitylib, `Complexity, `Cslib, `KFOL.Strategic, `KFOL.Rounds,
    `KFOL.Definitions.Strategic, `KFOL.Definitions.Rounds, `KFOL.Complexity]
  for moduleName in env.header.moduleNames do
    for forbiddenRoot in forbidden do
      if forbiddenRoot.isPrefixOf moduleName then
        throwError "Algebra audit: forbidden transitive import {moduleName}"
