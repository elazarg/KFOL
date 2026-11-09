# Reproduced historical mixed open-game obstruction

The immutable GameTheory artifact at
`02898a 2d 8b 918f 9b 106a 683420ca 78c 99867560e` was rebuilt in an isolated archive
under `/tmp`, with its original Lean 4.32.2 and pinned mathlib
`905b 95818eb 32af 7874a 58b 427f 50c 1711a 5e 96c`. The sibling `../GameTheory` was
only read to export the pinned source; no worktree or source modification was
used. This historical build is independent of KFOL's Lean 4.35.0 imports.

`lake build GameTheory.Languages.OpenGame.Examples` passed 3333 jobs. The five
relevant theorem closures were checked to use only `propext`, `Classical.choice`
and `Quot.sound`: left identity failure, canonical associativity failure,
incomparable bracketings, convex-equivalence failure as a composition
congruence, and failure of post-composition convex closing to restore
associativity. Their complete declarations are listed in `open-game-v 1.json`.

The source hash manifest covers all 64 local Lean sources in the target's
import closure plus its toolchain, Lake configuration and dependency manifest.
`python 3 scripts/check_external_open_game.py /path/to/isolated/checkout`
verifies those hashes and every Git dependency revision, rebuilds the target,
and audits the five theorem closures. A clean checkout needs the pinned
submodule and Lake dependencies available first; mathlib cache retrieval can
be limited to the 32 direct mathlib roots of the local import closure.

These proofs concern the specified raw lifting/composition from Definitions
11–12 of the cited version, and its specified convex repairs. They establish
no general impossibility for probabilistic open games. KFOL's round recursion
uses its independently proved canonical SE/SPE bridge and none of the refuted
category laws. Porting the external development remains unnecessary.
