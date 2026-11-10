module

import all KFOL.Algebra
import all KFOL.Definitions.Reductions
import all KFOL.Reductions.RawPairs
import all KFOL.Reductions.Colouring
import all KFOL.Algorithms.GuardWords
import all KFOL.Algorithms.SupportIndex
import all KFOL.Algorithms.ResetEquation
import all KFOL.Algorithms.FullTermCode
import all KFOL.Reductions.RawSubsignature
import all KFOL.Reductions.Circuits
import all KFOL.Owner.ObservationCompilation
import all KFOL.Reset.Realizability.Records
import all KFOL.Reductions.Circuits.LargeTables.Succinctness
import all KFOL.Algebra.ChoiceSupport
import all KFOL.Definitions.PaperAlgebra
import all KFOL.Query.Compilation
import all KFOL.Query.Relations
import all KFOL.Query.ZeroExtension
import all KFOL.Algebra.FullBasis.NonfiniteBasis
import all KFOL.Owner.FourVariableObstruction
import all KFOL.Owner.Basis.Exchange
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
