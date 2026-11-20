module

import all KFOL.Algebra
import all KFOL.Core.AtomicBasis.Basis
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
import all KFOL.Algebra.AtomicDecision
import all KFOL.Algebra.CoalitionMapsImages
import all KFOL.AtomicLogic.Unsorted
import all KFOL.Representation.WinnerEquivalences
import all KFOL.Representation.OperatorMorphisms
import all KFOL.Representation.Recovery
import all KFOL.Core.ProfileBudgets.Profiles
import all KFOL.Core.BichainSwitch
import all KFOL.Core.BichainCubeCuts
import all KFOL.Core.CompletionDepthChain
import all KFOL.Core.CompletionSuspension
import all KFOL.Core.AddressedGuards
import all KFOL.Core.AlternatingReachability
import all KFOL.Core.ProfileSourceFiber
import all KFOL.Core.SingleSourceCompletion
import all KFOL.Core.PassiveProfileBounds
import all KFOL.Core.AcyclicSourceQueries
import all KFOL.Core.MonochromaticLosses
import all KFOL.Core.MonochromeLossLift
import all KFOL.Core.BlockerCovers
import all KFOL.Core.CompulsoryPruning
import all KFOL.Core.PruningContextRows
import all KFOL.Core.PruningContextProduct
import all KFOL.Core.PruningModules
import all KFOL.Core.PruningExclusion
import all KFOL.Core.SupportModules
import all KFOL.Core.GraphPruning
import all KFOL.Core.BipartitePruning
import all KFOL.Core.IncidencePruning
import all KFOL.Core.EdgeSupportPruning
import all KFOL.Core.NonrectangularPruning
import all KFOL.Core.RainbowWinnerLift
import all KFOL.Core.MonochromaticHeadCuts
import all KFOL.Core.MonochromaticCutObstruction
import all KFOL.Core.SinglePostingObstruction
import all KFOL.Core.PurePostingPaths
import all KFOL.Core.ProfileCutObstruction
import all KFOL.Core.AnchoredPostingObstruction
import all KFOL.Core.SourceReciprocity
import all KFOL.Core.FacetPosting
import all KFOL.Core.ProfilePruning
import all KFOL.Core.SquareSourceObstruction
import all KFOL.Core.OfferLattice
import all KFOL.Core.DecreasingPaths
import all KFOL.Core.TransversalContexts
import all KFOL.Core.LayerInterpolation
import all KFOL.Core.GuardConsensus
import all KFOL.Core.OwnerFoldClosure
import all KFOL.Core.SpineThinning
import all KFOL.Core.IntervalMinorant
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
