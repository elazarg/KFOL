module

public import KFOL.Core.NonfiniteBasis
public import KFOL.Core.ProfileSynthesis
public import KFOL.Core.ProfileRelations
public import KFOL.Core.ProfileBounds
public import KFOL.Core.WholeInputs
public import KFOL.Core.ProfileQueries
public import KFOL.Core.ProfileCompletion
public import KFOL.Core.ProfilePointObstruction
public import KFOL.Core.Staircase
public import KFOL.Core.RainbowPersistence
public import KFOL.Core.ProfilePersistence
public import KFOL.Core.ProfileEnvelope
public import KFOL.Core.Interpolation
public import KFOL.Core.PairwiseInterpolation
public import KFOL.Core.TernaryInterpolation
public import KFOL.Core.MinorantPatches
public import KFOL.Core.MinorantFivePatches
public import KFOL.Core.FivePointInterpolation
public import KFOL.Core.FiniteRelationObstruction
public import KFOL.Core.CrownFullSyntax
public import KFOL.Core.SourceCertificates
public import KFOL.Core.SourcePeeling
public import KFOL.Core.Cuts
public import KFOL.Core.SourceNormalForm
public import KFOL.Core.LocalNormalForm
public import KFOL.Core.SourceCompatibility
public import KFOL.Core.ColoredGraphGuards
public import KFOL.Core.AtomicObserver
public import KFOL.Core.AtomicAmalgamation
public import KFOL.Core.BichainFiber
public import KFOL.Core.Hypergraphs
public import KFOL.Core.ExponentialCrown

/-! # Core operations, representations and basis obstructions

The explicit native quotients prove the K-variable obstruction. Actual
padded-grid algebras and graph-generated typed covers yield finite
countermodels for every variable bound, and hence the full no-finite-basis
results for both the winner core and the ambient native variety. Source guards
have canonical prime forms and finite colored-graph realizations at every arity.
Cyclic deletion patches disprove finite relatedness at every fixed finite role
set of size at least three, also for the full syntax with constants and switches.
-/
