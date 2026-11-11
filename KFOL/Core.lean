module

public import KFOL.Core.NonfiniteBasis
public import KFOL.Core.ProfileSynthesis
public import KFOL.Core.ProfileEnvelope
public import KFOL.Core.Interpolation
public import KFOL.Core.PairwiseInterpolation
public import KFOL.Core.TernaryInterpolation
public import KFOL.Core.MinorantPatches
public import KFOL.Core.Cuts
public import KFOL.Core.SourceNormalForm
public import KFOL.Core.LocalNormalForm
public import KFOL.Core.SourceCompatibility
public import KFOL.Core.ColoredGraphGuards

/-! # Core operations, representations and basis obstructions

The explicit native quotients prove the K-variable obstruction. Actual
padded-grid algebras and graph-generated typed covers yield finite
countermodels for every variable bound, and hence the full no-finite-basis
results for both the winner core and the ambient native variety. Source guards
have canonical prime forms and finite colored-graph realizations at every arity.
-/
