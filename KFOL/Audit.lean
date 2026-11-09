module

import all KFOL
import all KFOL.Algebra
import all KFOL.Algebra.Atomic.Binary
import all KFOL.Algebra.Atomic.BinaryCore
import all KFOL.Algebra.Atomic.Boolean
import all KFOL.Algebra.Atomic.Classification
import all KFOL.Algebra.Atomic.CoreSupport
import all KFOL.Algebra.Atomic.FiniteProduct
import all KFOL.Algebra.Atomic.Matrix
import all KFOL.Algebra.Atomic.Necessity
import all KFOL.Algebra.Atomic.OneConstant
import all KFOL.Algebra.Atomic.Unary
import all KFOL.Algebra.Basic
import all KFOL.Algebra.CommonSource
import all KFOL.Algebra.IdempotencyTestCard
import all KFOL.Algebra.IdempotencyTests
import all KFOL.Algebra.Idempotent
import all KFOL.Algebra.PairTests
import all KFOL.Algebra.Provenance
import all KFOL.Algebra.ReductTestCard
import all KFOL.Algebra.ReductTests
import all KFOL.Algebra.SemilatticeTrace
import all KFOL.Algebra.SmallCarriers
import all KFOL.Algebra.Switching
import all KFOL.Algebra.TestDomainCard
import all KFOL.Algebra.TestDomains
import all KFOL.Algebra.TwoPlayers.Algebra
import all KFOL.Algebra.TwoPlayers.Coordinates
import all KFOL.Algebra.TwoPlayers.CoreFailure
import all KFOL.Algebra.TwoPlayers.Degeneracies
import all KFOL.Algebra.Views
import all KFOL.Algorithms.FiniteTermCode
import all KFOL.Algorithms.Framing
import all KFOL.Algorithms.GuardDescriptor
import all KFOL.Algorithms.GuardRecord
import all KFOL.Algorithms.GuardWords
import all KFOL.Algorithms.Normalization
import all KFOL.Algorithms.ResetEquation
import all KFOL.Algorithms.ResetUnionCode
import all KFOL.Algorithms.SupportIndex
import all KFOL.Algorithms.TermCode
import all KFOL.Algorithms.Words
import all KFOL.Audit.Algebra
import all KFOL.Audit.Dependencies
import all KFOL.Complexity.BlockScan
import all KFOL.Complexity.DescriptorValidation
import all KFOL.Complexity.Dictionary
import all KFOL.Complexity.FiniteAlgebraVerifier
import all KFOL.Complexity.FiniteTermMachines
import all KFOL.Complexity.Framing
import all KFOL.Complexity.GuardCompression
import all KFOL.Complexity.GuardExtraction
import all KFOL.Complexity.GuardSubset
import all KFOL.Complexity.Language
import all KFOL.Complexity.NormalizeMachine
import all KFOL.Complexity.OptionTraversal
import all KFOL.Complexity.OwnerCheckMachine
import all KFOL.Complexity.OwnerPathMachines
import all KFOL.Complexity.OwnerRunMachine
import all KFOL.Complexity.OwnerRuntime
import all KFOL.Complexity.OwnerSynthesisBridge
import all KFOL.Complexity.OwnerSynthesisMachine
import all KFOL.Complexity.OwnerTermMachines
import all KFOL.Complexity.RawRecords
import all KFOL.Complexity.ReachMachine
import all KFOL.Complexity.RecognitionMachine
import all KFOL.Complexity.ResetEquality
import all KFOL.Complexity.ResetUnionCompleteness
import all KFOL.Complexity.ResetUnionDecoding
import all KFOL.Complexity.ResetUnionEvaluation
import all KFOL.Complexity.ResetUnionHardness
import all KFOL.Complexity.ResetUnionMachines
import all KFOL.Complexity.ResetUnionReduction
import all KFOL.Complexity.ResetUnionSource
import all KFOL.Complexity.ResetUnionVariables
import all KFOL.Complexity.ResetUnionWordCompleteness
import all KFOL.Complexity.SuffixFold
import all KFOL.Complexity.TermMachine
import all KFOL.Complexity.TermSupport
import all KFOL.Congruences
import all KFOL.Congruences.Basic
import all KFOL.Congruences.Classification
import all KFOL.Congruences.Closure
import all KFOL.Congruences.Families
import all KFOL.Congruences.Quotients
import all KFOL.Congruences.SymmetricClassification
import all KFOL.Congruences.Symmetry
import all KFOL.Congruences.Thresholds
import all KFOL.Congruences.UniformMatroid
import all KFOL.Core
import all KFOL.Core.AtomicNative
import all KFOL.Core.ChoiceUnion
import all KFOL.Core.ChoiceUnion.Basis
import all KFOL.Core.ChoiceUnion.Cover
import all KFOL.Core.ChoiceUnion.Embedding
import all KFOL.Core.ChoiceUnion.Laws
import all KFOL.Core.ChoiceUnion.NormalForm
import all KFOL.Core.ChoiceUnion.Probe
import all KFOL.Core.ChoiceUnion.ThreeCompleteness
import all KFOL.Core.Exhaustion
import all KFOL.Core.Folds
import all KFOL.Core.GridAlgebra
import all KFOL.Core.GridBounded
import all KFOL.Core.GridClone
import all KFOL.Core.GridCountermodel
import all KFOL.Core.GridCrossing
import all KFOL.Core.GridData
import all KFOL.Core.GridFoldValues
import all KFOL.Core.GridGuards
import all KFOL.Core.GridIdeal
import all KFOL.Core.GridIdealLabel
import all KFOL.Core.GridLocalCover
import all KFOL.Core.GridOrder
import all KFOL.Core.GridPatterns
import all KFOL.Core.GridPigeonhole
import all KFOL.Core.GridPrivate
import all KFOL.Core.GridProfiles
import all KFOL.Core.GridRows
import all KFOL.Core.GridSeparation
import all KFOL.Core.GridTerms
import all KFOL.Core.HomRange
import all KFOL.Core.Locality
import all KFOL.Core.MarkerGap
import all KFOL.Core.ModelLaws
import all KFOL.Core.Native
import all KFOL.Core.NativeTheory
import all KFOL.Core.NonfiniteBasis
import all KFOL.Core.PairLabel
import all KFOL.Core.PairModel
import all KFOL.Core.Profiles
import all KFOL.Core.Protected
import all KFOL.Core.Quotients
import all KFOL.Core.TypedCover
import all KFOL.Core.UpperClone
import all KFOL.Core.UpperMap
import all KFOL.Definitions.Algorithms
import all KFOL.Definitions.Atomic
import all KFOL.Definitions.Congruences
import all KFOL.Definitions.Core
import all KFOL.Definitions.CoreBasis
import all KFOL.Definitions.Dissemilattice
import all KFOL.Definitions.Encoding
import all KFOL.Definitions.Equational
import all KFOL.Definitions.Owner
import all KFOL.Definitions.Policies
import all KFOL.Definitions.Public
import all KFOL.Definitions.Reductions
import all KFOL.Definitions.Reset
import all KFOL.Definitions.Rounds
import all KFOL.Definitions.Strategic
import all KFOL.Definitions.TestDomains
import all KFOL.Definitions.TwoPlayers
import all KFOL.Definitions.Views
import all KFOL.Equational
import all KFOL.Equational.Completeness
import all KFOL.Equational.Locality
import all KFOL.Equational.Logic
import all KFOL.Equational.Native
import all KFOL.Equational.Preservation
import all KFOL.Owner
import all KFOL.Owner.Basic
import all KFOL.Owner.Basis
import all KFOL.Owner.Basis.CommonRoot
import all KFOL.Owner.Basis.Completeness
import all KFOL.Owner.Basis.Presentation
import all KFOL.Owner.Basis.WinnerSet
import all KFOL.Owner.Basis.WordAbsorption
import all KFOL.Owner.Basis.WordNormalForm
import all KFOL.Owner.BasisObstruction
import all KFOL.Owner.Completeness
import all KFOL.Owner.Four
import all KFOL.Owner.Guards
import all KFOL.Owner.Minimum
import all KFOL.Owner.Public
import all KFOL.Owner.Saturation
import all KFOL.Owner.Separation
import all KFOL.Owner.SmallCarriers
import all KFOL.Owner.SmallModels
import all KFOL.Owner.Synthesis
import all KFOL.Owner.SynthesisNecessity
import all KFOL.Owner.SynthesisSoundness
import all KFOL.Policies.Basic
import all KFOL.Policies.Coverage
import all KFOL.Policies.Guards
import all KFOL.Policies.Lattice
import all KFOL.Policies.Normalized
import all KFOL.Policies.Patterns
import all KFOL.Policies.Public
import all KFOL.Policies.Recognition
import all KFOL.Policies.SinglePolicy
import all KFOL.Policies.Strict
import all KFOL.Reductions.ResetUnionCorrectness
import all KFOL.Reductions.ResetUnionMarkers
import all KFOL.Reductions.ResetUnionSemantics
import all KFOL.Reductions.ResetUnionSize
import all KFOL.Reductions.ValueFolds
import all KFOL.Reset
import all KFOL.Reset.Antimatroid
import all KFOL.Reset.Antimatroid.Basic
import all KFOL.Reset.Antimatroid.Equivalence
import all KFOL.Reset.Antimatroid.Orders
import all KFOL.Reset.Antimatroid.Paths
import all KFOL.Reset.Antimatroid.Product
import all KFOL.Reset.Antimatroid.Synthesis
import all KFOL.Reset.Antimatroid.Term
import all KFOL.Reset.Basic
import all KFOL.Reset.Basis
import all KFOL.Reset.Basis.Coverage
import all KFOL.Reset.Basis.Laws
import all KFOL.Reset.Basis.NormalForm
import all KFOL.Reset.Basis.Presentation
import all KFOL.Reset.Basis.Words
import all KFOL.Reset.Chain
import all KFOL.Reset.Extraction
import all KFOL.Reset.Generator
import all KFOL.Reset.Public
import all KFOL.Reset.Realizability
import all KFOL.Reset.Realizability.Constructible
import all KFOL.Reset.Realizability.GreedyOrder
import all KFOL.Reset.Realizability.Model
import all KFOL.Reset.Realizability.Necessity
import all KFOL.Reset.Realizability.Recognition
import all KFOL.Reset.Realizability.Size
import all KFOL.Reset.Realizability.Synthesis
import all KFOL.Reset.Selection
import all KFOL.Reset.Substitution
import all KFOL.Reset.Tables
import all KFOL.Rounds.Disclosure
import all KFOL.Rounds.InformationFibers
import all KFOL.Rounds.PrefixLaw
import all KFOL.Rounds.Reachability
import all KFOL.Rounds.SequentialExistence
import all KFOL.Rounds.SerializationFinite
import all KFOL.Rounds.SerializationRecall
import all KFOL.Rounds.SerializationTrace
import all KFOL.Rounds.Tree
import all KFOL.Strategic
import all KFOL.Strategic.Adequacy
import all KFOL.Strategic.Basic
import all KFOL.Strategic.Compilation
import all KFOL.Strategic.Examples
import all KFOL.Strategic.Forcing
import all Paper
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-!
# Whole-project axiom audit

Inspect every authored declaration, including private helpers and all
transitive axiom dependencies. The separate KFOL.Audit.Algebra target checks
the pure module closure before Paper and the machine proofs are loaded.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.moduleNames[idx.toNat]!
        (`KFOL).isPrefixOf owner || owner == `Paper
      | none => false
    if owned then
      checked := checked + 1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit: {name} depends on forbidden axiom {axiomName}"
  if checked == 0 then
    throwError "Axiom audit: no authored declarations were checked"
