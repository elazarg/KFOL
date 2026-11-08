module

import all KFOL.Definitions.Public
import all KFOL.Definitions.Core
import all KFOL.Definitions.Views
import all KFOL.Definitions.TestDomains
import all KFOL.Algebra.Basic
import all KFOL.Algebra.PairTests
import all KFOL.Algebra.Idempotent
import all KFOL.Algebra.Views
import all KFOL.Algebra.SemilatticeTrace
import all KFOL.Algebra.CommonSource
import all KFOL.Algebra.TestDomains
import all KFOL.Algebra.TestDomainCard
import all KFOL.Algebra
import all KFOL
import all Paper
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-!
# The algebra slice's import and axiom boundaries

Inspect the loaded environment, including private authored declarations and
every transitively loaded module. A source-only import check would miss an
unwanted dependency hidden behind another import.
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
          throwError "Algebra audit: {name} depends on forbidden axiom {axiomName}"
  if checked == 0 then
    throwError "Algebra audit: no authored declarations were checked"
