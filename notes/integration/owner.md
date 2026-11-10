# Owner branch integration

The initial slice is ready at Lean/mathlib 4.35.0. No shared configuration,
`Paper.lean`, audit, inventory or manuscript files were edited by this agent.

## Completed slice

- `Definitions/Owner.lean`: `WinnerSet.guardedChoice r x y z = (choice r y z).reset x`;
  a relation-free mathlib signature with reset and owner-labelled ternary H;
  terms, independent root/evaluation/owner restrictions, one guard per occurrence,
  guard conditions/coverage, executable coverage/equation checks and explicit minimal valuations.
- `Owner/Basic.lean`: generic structural induction, root ambiguity/atomic laws.
- `Owner/Guards.lean`: exact membership semantics and one guard per original leaf.
- `Owner/Separation.lean`: coverage iff universal implication, explicit failed-guard
  countervaluations, all inputs unions of at most two atoms from three named roles.
- `Owner/Completeness.lean`: observer implication/equivalence, one outsider table
  characterizes full equality; executable checker correctness.
- `Owner/Public.lean`: idempotence and atom preservation of H, explicit compilation
  into existing public owned-choice syntax, preserving evaluation and the core fragment.
- `Owner.lean`: imports the slice.
- `tests/Owner.lean`: kernel-decided concrete guards, owner/outsider differences,
  leaf occurrence counting, idempotence, symmetry, reset presentation,
  source-discharge in dominance and empty-list coverage.

All definitions are in one additional small module; no GameTheory dependency is
introduced. Guard prerequisites are finite lists denoting conjunctions; repeated
conditions do not alter meaning. Terms reuse the existing mathlib term datatype.

## Full root propositions to integrate

`owner:lem:root` can be completed by the following complete statement:

```lean
theorem owner_root_status {Role : Type u} {Var : Type v}
    (t : Owner.Term Role Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    (∀ r, t.eval valuation = WinnerSet.singleton r ↔
      valuation t.root = WinnerSet.singleton r) :=
  ⟨t.ambiguous_iff valuation, t.eq_singleton_iff valuation⟩
```

`owner:thm:guards` can be completed by conjoining `Term.guard_semantics`,
`Term.observation_implication_iff`, and `Term.observation_countervaluation`.
All take arbitrary variable and role types, equality decisions where guard
computation needs them, and three explicitly distinct roles `observer other background`.
Terms must satisfy `OwnersIn (fun r => r = observer ∨ r = other)`.
The complete mathematical statement is:

```lean
theorem owner_guard_completeness {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var]
    (s t : Owner.Term Role Var) (k a b : Role)
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hs : s.OwnersIn (fun r => r = k ∨ r = a))
    (ht : t.OwnersIn (fun r => r = k ∨ r = a)) :
    (Owner.Covers (s.guards k) (t.guards k) ↔
      ∀ v : Var → WinnerSet Role, k ∈ (s.eval v).val → k ∈ (t.eval v).val) ∧
    (¬Owner.Covers (s.guards k) (t.guards k) →
      ∃ g ∈ s.guards k,
        k ∈ (s.eval (Owner.minimalVal k a b g)).val ∧
        k ∉ (t.eval (Owner.minimalVal k a b g)).val ∧
        ∀ j, ∃ r ∈ ({k, a, b} : Set Role), ∃ q ∈ ({k, a, b} : Set Role),
          Owner.minimalVal k a b g j =
            (WinnerSet.singleton r).union (WinnerSet.singleton q)) :=
  ⟨s.observation_implication_iff t k a b hka hkb hab hs ht,
    s.observation_countervaluation t k a b hka hkb hab hs ht⟩
```

The algebraic/checker clauses of `owner:thm:one-table` are proved by:

```lean
theorem owner_one_table {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k : Role) (hka : k ≠ a) (s t : Owner.Term Role Var)
    (hs : s.OwnersIn (fun r => r = a)) (ht : t.OwnersIn (fun r => r = a)) :
    ((∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔
      Owner.Covers (s.guards k) (t.guards k) ∧ Owner.Covers (t.guards k) (s.guards k)) ∧
    (Owner.Term.equationB k s t = true ↔
      ∀ v : Var → WinnerSet Role, s.eval v = t.eval v) :=
  ⟨s.single_table_equation_iff three t a k hka hs ht,
    Owner.Term.equationB_correct three a k hka s t hs ht⟩
```

The initial slice left polynomial time separate. It is now certified by
`OwnerWordFrontend` and the complete owner-count frontend.

## Integration chores for root

Import `KFOL.Owner` where desired; extend exact audit coverage with the definition
and proof modules; include all pure modules in the pure build closure;
copy full propositions to root `Paper.lean` with axiom guards; update inventory
and definition index. The complete one-table and owner-count runtime clauses
are now checked. Root and guard semantics have no global K≥3 hypothesis.
The three-role requirements occur only at separation/completeness.

## Subsequent completed integrations

Four-element generator equivalence, realizability/synthesis, minimum-generator
exclusion and the full thirty-six-law completeness theorem are all implemented
and checked by the production targets.

## Four-element semantic equivalence now checked

`Owner/Four.lean` is ready (it is intentionally not added to the umbrella yet,
so root can integrate it explicitly). Definitions remain in `Definitions/Owner`:
`Four` with four constructors, explicit finite enumeration, `Four.reset`,
`Four.guarded`, the direct `Four.project` from winner sets, `Four.embed` of the
four displayed concrete values, `fourStructure`, and `Term.evalFour`.

`Four.project_reset` and `Four.project_guarded` prove the direct projection
preserves both operations; its `winning` fiber is exactly observer membership.
`Four.project_embed` is a section on three distinct roles. `Four.embed_reset`
and `Four.embed_guarded` prove closure of the concrete four displayed values and
identify the multiplication tables. `Term.four_element_complete` proves:

```lean
(∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔
  ∀ w : Var → Owner.Four, s.evalFour w = t.evalFour w
```

under a three-role embedding, `observer ≠ owner` and both syntax trees restricted
to the fixed owner. `Four.card` proves cardinality 4. No finite-state testing is
used in place of the arbitrary-role projection/equivalence proofs; the finite
multiplication tables themselves are kernel-checked by cases.

The minimum-generator exclusion is still missing, so this completes the first
clause of `owner:thm:four`, not the entire main-paper theorem.

`WinnerSet.guardedChoice_separates` in `Owner/Public.lean` now proves the exact
main-text H example at pairwise distinct a,b,c: with root `{a,b}` and z=`{c}`,
c is absent for y=`{a}` and present for y=`{b}`. Combined with
`guardedChoice_self`, `guardedChoice_singleton` and `eval_compile`, this finishes
the H-specific algebraic clauses of main-prose:derived-reset.

## Minimum four-element generator is now fully proved

Ready staged sources (warnings-as-errors builds passed):

- `Owner/SmallModels.lean` is already in production and compiles. Its
  `reset_three_classification` universally quantifies over all binary operations
  on `Fin 3` satisfying the six reset laws. Idempotence fixes the diagonal;
  all remaining six table cells range independently over `Fin 3`. Kernel
  `decide` checks that finite family. A separate function-extensionality proof
  reconstructs every possible idempotent operation from those cells, proving
  exhaustiveness. The Python development counts are not formal evidence and
  are not asserted by the Lean theorem.
- `staging/OwnerSmallCarriers.lean.pending` is ready to promote to
  `KFOL/Owner/SmallCarriers.lean`. It transports the classification to arbitrary
  finite carriers and combines it with the ternary minor/absorption obstruction.
  `idempotent_assoc_of_card_le_two` is public for reuse in the reset minimum
  generator proof; it includes empty, singleton and two-element carriers.
- `staging/OwnerMinimum.lean.pending` is ready to promote to
  `KFOL/Owner/Minimum.lean`. It proves `four_minimum_generator` using the
  independent generic `Equational.Identity.Holds` semantics:

```lean
theorem four_minimum_generator {M : Type u} [Fintype M]
    [(Equational.language (Symbol Unit)).Structure M]
    (hTheory : ∀ e : Equational.Identity (Symbol Unit),
      (letI := fourStructure (Role := Unit); e.Holds Four) ↔ e.Holds M) :
    4 ≤ Fintype.card M
```

The fixed one-owner signature is `Symbol Unit`: its binary symbol is reset,
its one ternary symbol is H. The all-identities hypothesis is exactly the
mathematical meaning of generating Four's theory; it is not a temporary
external theorem assumption. The proof transfers eleven identities that Four
satisfies to M, invokes the complete small-carrier obstruction, and transfers
one of three explicit nonidentities back to Four for a contradiction.
No Freese theorem is assumed or added as an axiom.

Together with `Four.card`, `Four.embed_reset`, `Four.embed_guarded`, and
`Term.four_element_complete`, this closes the entire `owner:thm:four` main claim.
The thirty-six-law basis and four-variable lower bound remain separate work.
Promote the staged files, add their audit imports, and retire the pending
copies after integration; no duplicate lasting semantics are intended.

The minimum-generator staging files were promoted in checkpoint `e97189b`;
the pending duplicates have been retired. Root is factoring the generic size≤2
associativity lemma into the pure algebra infrastructure for reset reuse.

## Complete semantic one-owner synthesis (new, ready for integration)

Production definitions `Definitions/Owner.lean` and modules `Owner/Saturation.lean`,
`Owner/SynthesisSoundness.lean`, `Owner/Synthesis.lean` and
`Owner/SynthesisNecessity.lean` now compile. `Owner.lean` exports the result.
The corresponding pending duplicates have been retired.

This covers the mathematical realization equivalence, an actual synthesizer,
the complete expanded-tree size bound, and update-order independence in
`owner:thm:synthesis` (`sections/appendix-owner-synthesis.tex`). The polynomial
machine-runtime clause remains required and is handed to `/root/complexity`;
do not mark the entire result complete until that clause is connected. No
substitution theorem is claimed yet.

Independent definitions are concentrated in `Definitions/Owner.lean`:
`GuardPair` contains finite ambiguity/nonowner sets, `GuardTable` contains an
independent root and an explicit list of source/pair records, `Canonical`
spells out exactly the paper's canonical conditions, and `Realizes` means
fixed root, the fixed-owner signature, and exact outsider winner semantics
for arbitrary WinnerSet valuations. `Realizes` does not refer to the checker,
the saturation, or a synthesized term. The dictionary `positions : List Var`
need only cover the root and all source/test positions (`Listed`); unused
positions are permitted and label values do not determine iteration counts.
No global finite variable type is assumed. Canonical input includes `Nodup`
on the record list so M is the actual canonical guard count.

Suggested complete paper-facing semantic statement (expand `Realizes` if
required by the public theorem convention, preserving its complete
root/owner/observer clauses):

```lean
theorem owner_table_synthesis {Role : Type u} [DecidableEq Role]
    {Var : Type v} [DecidableEq Var]
    (T : KFOL.Owner.GuardTable Var)
    (owner observer background : Role)
    (hko : observer ≠ owner) (hkb : observer ≠ background)
    (hob : owner ≠ background) (positions : List Var)
    (hcan : T.Canonical) (hlisted : T.Listed positions) :
    (T.check positions = true ↔
      ∃ t : KFOL.Owner.Term Role Var,
        t.root = T.root ∧ t.OwnersIn (fun a => a = owner) ∧
        ∀ k, k ≠ owner → ∀ v : Var → KFOL.WinnerSet Role,
          k ∈ (t.eval v).val ↔
            T.Enabled {i | (v i).Ambiguous}
              {i | v i ≠ KFOL.WinnerSet.singleton owner}
              {i | k ∈ (v i).val}) ∧
    (∀ t : KFOL.Owner.Term Role Var,
      T.synthesize owner positions = some t →
        t.root = T.root ∧ t.OwnersIn (fun a => a = owner) ∧
        (∀ k, k ≠ owner → ∀ v : Var → KFOL.WinnerSet Role,
          k ∈ (t.eval v).val ↔
            T.Enabled {i | (v i).Ambiguous}
              {i | v i ≠ KFOL.WinnerSet.singleton owner}
              {i | k ∈ (v i).val}) ∧
        t.size ≤ 1 + T.entries.length * (10 * positions.length + 7))
```

The first conjunct is `GuardTable.check_iff_realizable`; the second is
`GuardTable.synthesize_spec` with its first conjunct expanded. To expose
actual construction from realizability, use `GuardTable.synthesis_iff`:

```lean
(∃ t : Term Role Var, T.Realizes owner t) ↔
  ∃ t : Term Role Var, T.synthesize owner positions = some t ∧
    T.Realizes owner t ∧
    t.size ≤ 1 + T.entries.length * (10 * positions.length + 7)
```

Actual option-success is `GuardTable.synthesize_isSome`:
`(T.synthesize owner positions).isSome = true ↔ T.check positions = true`.
It needs no realizability hypothesis. Every accepted guard has a path
constructed by the explicit program `guardPath`, whose per-path bound is
`10 * positions.length + 6`. Joining M paths adds M binary nodes and one
root-variable node, giving the stated full bound including all copied
variable occurrences.

The update-order statement is `GuardTable.run_order_independent`:

```lean
(T.run left j g (2 * left.length)).1 =
  (T.run right j g (2 * right.length)).1
```

under exactly `T.root ∈ g.many`, `target j g ⊆ left.toFinset` and
`target j g ⊆ right.toFinset`. This proves order independence even for
lists with different unused positions and repeated dictionary entries.
The underlying generic statement `run_le_closed` proves every execution
below every closed extension of the initial tests. `run_fixed` proves the
2n clock always suffices. `SaturationState.rank_eq` identifies the rank
with the report's `2*|C|+|D|` on the proved disjoint states.

Necessity is a direct induction through the actual term occurrence guards.
`Term.root_guard_mem` supplies each subterm's root contribution, and
`Term.root_mem_guard_many` forces the ambiguity test when a contribution
leaves that root. Independent minimal three-role valuations turn semantic
containment into permission of each raw guard, and choose a raw occurrence
covering each candidate guard. `admissible_finish` then descends the term:
right reset and first H child preserve the state; left reset and the
other H children force the necessary roots/tests into the closed state.
The last frame gives exactly one of the two finish alternatives. This
proves the paper's pruning argument without assuming a pruning theorem.

Validation completed:

- `lake build KFOL.Owner.SynthesisNecessity`: passed 1112 jobs.
- `lake env lean -DwarningAsError=true tests/OwnerSynthesis.lean`: passed.
- Regression examples kernel-check the projection and ternary H tables,
  two dictionary orders, missing-position rejection, and a canonical
  unrealizable table needing a nonexistent intermediate contribution.
- `synthesis_iff` and `run_order_independent` axiom guards pass with only
  `propext`, `Classical.choice`, and `Quot.sound`.

No proof gaps, outside theorem assumptions, native_decide, or added axioms
occur in this semantic synthesis slice. Thirty-six-law completeness and the
no-three-variable basis theorem remain separate active work.

## No-three-variable basis (new, ready)

`Owner/BasisObstruction.lean` now migrates and completes the entire
`owner:prop:four-variables` statement from `sections/appendix-basis.tex`.
The witness definitions (W's four constructors, operations, embeddings and
four-variable root-expansion identity) are in the existing
`Definitions/Owner.lean`, keeping the independent surface concentrated.

Unlike an arity-three-only certificate, the exported theorem bounds the
actual number of distinct variables and permits arbitrary padded arities:

```lean
theorem BasisObstruction.holds_of_variableCount_le
    (e : Equational.Identity (Symbol Unit))
    (hn : e.variableCount ≤ 3)
    (hvalid : letI := fourStructure (Role := Unit); e.Holds Four) :
    e.Holds BasisObstruction.Carrier
```

For a valuation, its support image has cardinality at most three, so one
of W's four elements is missing. Off-support variables are replaced by a
fixed remaining element; `Equational.realize_eq_of_eqOn` proves this
preserves both sides. The explicit embedding of the proper subalgebra
into Four squared then transfers the arbitrary-depth identity. This
uses the shared actual-support locality API, without imposing an arity
bound or assuming generation/embedding claims as hypotheses.

`rootExpansion_holds` proves the displayed four-variable identity in
Four; `rootExpansion_fails` refutes it in W at the paper's valuation.
Its actual support is independently checked to be four. On that valuation
the left side is `.middle` and the right side is `.high`.

Suggested complete paper statement:

```lean
theorem owner_basis_variable_bound
    (T : KFOL.Equational.Theory (KFOL.Owner.Symbol Unit))
    (n : ℕ)
    (hbasis : letI := KFOL.Owner.fourStructure (Role := Unit);
      KFOL.Equational.IsBasis KFOL.Owner.Four T)
    (hbound : ∀ e ∈ T, e.variableCount ≤ n) : 4 ≤ n
```

Proof: `BasisObstruction.variableBound_ge_four T n hbasis hbound`.
There is no finiteness hypothesis on T; even an infinite three-variable
basis is excluded. `not_hasVariableBound_three` exports this stronger
negative form directly. The thirty-four additional equations' soundness
and thirty-six-law generic completeness remain separate work.

Validation: production `lake build KFOL.Owner.BasisObstruction` passed
1119 jobs; `tests/OwnerBasisObstruction.lean` checks W's cardinality,
root-expansion's exact support and the two distinct values, plus standard
axiom guards for the full actual-support transfer and lower-bound theorems.

## Thirty-six-law basis completeness (new, ready)

The entire `owner:thm:finite-basis` claim is now proved, including
arbitrary finite or infinite algebras. `Owner/Basis.lean` exports the exact
native thirty-six-equation family, soundness, completeness, direct intended
winner-set interpretation, and the four-to-six variable bounds. No
external generation theorem, conditional completeness premise, or finite
closure certificate is substituted for the generic conclusion.

Independent data are concentrated in existing `Definitions/Owner.lean`:

- `FiniteBasis.basisAxiom : Fin 36 → Identity (Symbol Unit)` contains the
  thirty-six fully expanded native reset/H equations, with comments matching
  the paper's labels. `theory = Set.range basisAxiom` is defined from this
  explicit data family, independently of semantic validity. The kernel-checked `basisAxiom_injective` and `theory_ncard` prove
  that the actual data family has exactly 36 distinct identities. The
  four repeated equations have been removed; no irredundance claim is made.
- `FiniteBasis.Laws` is the semantic thirty-six-law view. The proved
  `models_theory_iff` connects it to the independent exact data family.
  `RootFiber`, primitive operation extraction, and `Term.actionWords`
  provide the generic model interface and actual native normalization.
- `oneOwnerStructure owner` interprets the single ternary symbol of
  `Symbol Unit` as the chosen owner's guarded operation on WinnerSet.
  `Term.withOwner` explicitly maps that signature into the existing
  owner-labelled native signature, without changing variable occurrences.

Suggested complete paper-facing statement for the basis itself:

```lean
theorem owner_thirty_six_equation_basis {Role : Type u}
    (three : Fin 3 ↪ Role) (owner observer : Role)
    (ho : observer ≠ owner) :
    (Set.range KFOL.Owner.FiniteBasis.basisAxiom).ncard = 36 ∧
    (Set.range KFOL.Owner.FiniteBasis.basisAxiom).Finite ∧
    (∀ i : Fin 36,
      (KFOL.Owner.FiniteBasis.basisAxiom i).variableCount ≤ 6) ∧
    (letI := KFOL.Owner.oneOwnerStructure owner
     ∀ e : KFOL.Equational.Identity (KFOL.Owner.Symbol Unit),
       e.Holds (KFOL.WinnerSet Role) ↔
         KFOL.Equational.Derives
           (Set.range KFOL.Owner.FiniteBasis.basisAxiom) e.lhs e.rhs)
```

Use `theory_ncard`, `theory_finite`, `variable_bound`, and `isBasis_winnerSet`.
`FiniteBasis.isBasis` proves the same complete proposition for Four
itself. `hasFiniteBasis` is the corresponding existential theorem.
The additional main-paper lower-bound statement can be given directly
for the intended winner algebra:

```lean
∀ (T : Equational.Theory (Symbol Unit)) (n : ℕ),
  (letI := oneOwnerStructure owner
   ∀ e : Equational.Identity (Symbol Unit),
     e.Holds (WinnerSet Role) ↔ Equational.Derives T e.lhs e.rhs) →
  (∀ e ∈ T, e.variableCount ≤ n) → 4 ≤ n
```

This is `FiniteBasis.variableBound_ge_four_winnerSet`; no finiteness
hypothesis on T is needed. Thus the exhibited basis proves the upper
bound6 and the independent four-state obstruction proves the lower
bound4.

The proof follows the report's mathematical argument, with explicit
mathlib abstraction at its common-root semilattice boundary:

- `Basis/Presentation.lean` proves every native equation in Four,
  finite enumeration, actual support≤6, and Models↔Laws.
- `Basis/CommonRoot.lean` constructs local mathlib `SemilatticeSup` and
  `OrderBot` on `RootFiber f r`. Primitive actions are `SupHom`; G/K and
  constants remain derived native operations. Generic words satisfy
  `P Q P = P Q`, preservation of joins, contractivity by P(bottom), and
  all test/capture/weak/constant/terminal equations.
- `Basis/WordNormalForm.lean` proves independent root preservation,
  the two projected normalization equations, and full arbitrary-depth
  term normalization to the explicit finite word language. Repeated
  variable occurrences contribute independently.
- `Basis/WordAbsorption.lean` proves the uniform covering-word reduction,
  exceptional terminal case, and the full generic algebraic two-source
  absorption lemma.
- `Basis/Completeness.lean` constructs explicit minimal four-state
  marker valuations. Induction extracts a first source occurrence whose
  prefix has exactly the guard coverage requirements. Omitting its suffix
  gives a word witness below the complete upper word value. The two-source
  lemma then proves containment in every basis model, by induction on
  prefixes. Two containments yield equality. Independent root separation
  in Four removes the projection, and shared equational completeness
  supplies the independently defined Derives conclusion.
- `Basis/WinnerSet.lean` proves the exact intended-algebra/Four identity
  theory equivalence using explicit native owner transport and the
  previously completed Four projection/embedding theorem. It transfers
  the complete basis and lower variable bound to arbitrary role sets with
  a three-role embedding.

Validation: `lake build KFOL.Owner` passed1133 jobs after the intended
winner-set bridge. `tests/OwnerBasis.lean`, `OwnerSynthesis.lean`, and
`OwnerBasisObstruction.lean` all passed with warnings as errors. The
complete `isBasis` and `isBasis_winnerSet` axiom guards allow exactly
`propext`, `Classical.choice`, `Quot.sound`. The finite soundness,
Models↔Laws and generic term-normalization foundations need only
`propext` and `Quot.sound`; generic two-source absorption needs only
`propext`. All promoted staging duplicates have been retired.

The earlier synthesis polynomial machine-runtime clause remains with
`/root/complexity`. Owner:thm:finite-basis has no analogous runtime clause
or remaining proof gap. Parent assigned finite policy-family dichotomy
and strict selective extension as the next pure algebra/reduction task.

## Literal two-source report wrapper complete

`Owner/Basis/TwoSource.lean` now exports
`FiniteBasis.two_source_guard_absorption`, with exact full statement:

```lean
{Var : Type v} (r a b : Var) (P : List (Var × Var)) (W : Owner.Term Unit Var)
(hzero : Equational.Derives FiniteBasis.theory
  (Owner.Term.step (Owner.Term.pathBody () r P (.var r)) W) W)
(hcover : Owner.Covers (Owner.Term.twoSourceGuards r a b P)
  ((W.withOwner false).guards true)) :
Equational.Derives FiniteBasis.theory
  (Owner.Term.step
    (Owner.Term.pathBody () r P (Owner.Term.guarded () (.var r) (.var a) (.var b))) W) W
```

This is the literal `owner:lem:two-source` statement, strengthened by allowing
any native upper term W; the report's word-value join is a special case. The
premise and conclusion use the independent Derives relation and exact thirty-six
identities, and coverage uses independent Guard.Dominates/Covers. There are
no root inequalities or selected-role semantic hypotheses replacing either
required premise. Equal indices and indices already in P are allowed.

Two audit-surface definitions were added to Definitions/Owner:
`Guard.pathLift` is precisely the native path's guard transformer, and
`Term.twoSourceGuards` consists of exactly the two new source occurrences
from C_ab, transformed by P. Native self tests, repeated root tests and
repeated indices are retained. In particular the initial source-a/source-b
guards are (source=a,many=[r],outside=[b,a]) and
(source=b,many=[r],outside=[b,a]); source membership makes the self test
harmless, just as Guard.Dominates allows a passing test at the source.

`Term.eval_guards_two_sources` independently proves the full Boolean guard
decomposition of P(C_ab) into P(0) and those two new guards, for arbitrary
M,N,V predicates. Sound coverage and the derivation premise then give
observational absorption. The already-proved one-observer completeness,
Four bridge and generic equational completeness yield the actual Derives
conclusion. This corollary depends on the complete basis; the basis core
continues to use WordAbsorption.two_source_absorption, private
Completeness.covering_witness and witness_le_wordsValue in its arbitrary-model
word induction, so the formal dependency graph is acyclic.

Validation: production build `KFOL.Owner.Basis.TwoSource` passed1211 jobs.
`tests/OwnerTwoSource.lean` checks no-prefix guards and actual repeated indices
and self tests. Both public theorems have standard-three axiom guards.
This closes the standalone report dependency row; it is no longer justified
merely by pointing to the complete IsBasis theorem.

## Native original-tree guard annotation gate

`KFOL.Owner.GuardEncoding` is a pure module importing the generic finite
signature codec, with arbitrary `[Fintype (FiniteTermCode.Operation
(Owner.Symbol Unit))]`. It uses no concrete complexity-package instance.
`Term.guards_withOwner_outsider t owner observer (hne : observer ≠ owner)`
proves exact raw-list equality with `(t.withOwner false).guards true`,
including list order and all repeated tests, uniformly in role count.

Two generic audit-surface measures were added to Definitions/Owner:
`Guard.payloadWeight weight g = weight source + 1 + 2*sum(many weights)
+ sum(outside weights)` and `Term.guardAnnotationWeight weight observer t
= weight(root) + sum(2*guard payload+1)`. With
`weight j = 2*j.bits.length+1`, these are exactly the native pair/list framed
annotation payload and full annotation lengths used by the machine worker.

`Term.guard_payloadWeight_le_encode` proves each actual raw guard payload
is ≤2*N², where N is the original Unit term's generic encoded length.
`Term.guardAnnotationWeight_le_encode` proves the complete annotation weight
is ≤6*(N+1)^3. Root-name and leaf-count bounds are proved separately; the
argument does not bound names by their numeric value, nor bound iterations
by the maximum variable label. Every repeated long root test is counted.
`Term.guardAnnotationWeight_withOwner_le_encode` exports the same bound for
any actual owner/outsider roles. This supplies the pure output-bound and
semantic bridge requested for native uniform-K original-tree extraction.

Validation: `lake build KFOL.Owner.GuardEncoding` passed1188 jobs;
`tests/OwnerEncoding.lean` passed with warnings as errors. Regressions keep
two repeated outside tests at name1000000000 and verify exact outsider
transport. Full polynomial bound has only standard-three axioms; the exact
outsider guard-list transport uses only propext and Quot.sound.

Final combined validation after all promotions: `lake build KFOL.Owner
KFOL.Policies.Public` passed1236 jobs. The six warning-as-error regressions
OwnerEncoding, OwnerTwoSource, OwnerBasis, OwnerSynthesis, Policies and
PoliciesHardness all passed. Owner/Policies sources are stable and ready for
parent Paper/audit/inventory integration; no commits were made by this worker.


## Basis audit correction: 36 distinct identities

The literal basis and semantic Laws structure have been reduced from 40 to 36
assumptions. Original S12 was R3 with variables renamed, A18 was R2, and A19
was the reverse of S8. The full deterministic alpha/orientation audit then
found a fourth repeat: original S11 was R5 with variables renamed and sides
reversed. The exact derivation is `(laws.R5 u r a).symm`. All four are now
proved consequences, with no retained basis rows or Laws fields:

- `Laws.project_idem r u := laws.R3 u r`;
- `Laws.G_zero r a := laws.R2 r a`;
- `Laws.F_zero r a b := (laws.h_insert r a b).symm`;
- `Laws.reset_back r a u := (laws.R5 u r a).symm`.

The entire arbitrary-model normalization/completeness proof therefore works
from precisely the 36 retained hypotheses. These four derived lemmas require
no axioms at all.

The actual list is `basisAxiom : Fin 36 → Identity (Symbol Unit)`, with
retained order unchanged. After the six reset equations there are eleven
structural equations S1–S11 and nineteen action equations A1–A19. Old S13 is
now S11, old A20/A21 are A18/A19, and the normalization projection step cites
R5 directly. The expanded six-variable action-band equation is source index 21.

`basisAxiom_injective` compares the fully expanded native left/right term
pairs by kernel `decide`. `theory_ncard` proves
`(Set.range basisAxiom).ncard = 36`; the public theorem asserts this actual
set cardinality, replacing the former count of index slots. The independent
Python check additionally canonicalizes variables by first occurrence across
BOTH sides and compares both orientations, over the ENTIRE retained list.
It confirms 36 equivalence classes, ruling out another missed alpha/orientation
repeat. No minimum-cardinality or irredundant-basis claim is made.

The public declaration is now `KFOL.Paper.owner_thirty_six_equation_basis`;
only its count/name/doc/guard block changed in Paper. The main owner theorem
and report list/proof references were updated in place. checks/owner_basis.py
removes exactly these four rows, and checks/check_owner_finite_basis.py checks
both literal and alpha/orientation distinctness before soundness enumeration.
Root should refresh inventory/definition-surface/public axiom references and
the verification appendix, and run make paper for updated label snapshots.

## Four-variable basis obstruction

A six-element model now rules out every four-variable basis, including infinite
ones. Its five subalgebras obtained by omitting one of the first five values
cover every four inputs and satisfy the entire thirty-six-law basis. The full
carrier satisfies the other thirty-five laws; the action-band law has exactly
two failing assignments, both using all five indispensable values. A native
five-variable consequence separates it. The resulting lower bound of five is
proved for Four and every intended winner-set algebra with at least three
roles in `KFOL/Owner/FourVariableObstruction.lean`. The displayed basis still
gives upper bound six. Earlier four-variable lower bounds in this note record
historical milestones; the conservative relative bound is still optimal.

## Optimal five-variable presentation

Five variables suffice. `FiniteBasis.fiveVariableAxiom` retains the thirty-five
non-band axioms and replaces the six-variable action-band law by the native
five-variable exchange law. `Owner/Basis/Exchange` gives an ordinary Lean
congruence/transitivity derivation of the action-band law, followed by the
arbitrary-model bridge and completeness. The new family has exactly thirty-six
equations. The original word/action presentation stays available with its
original theorem contracts. Together with the six-element local obstruction,
this proves that five is the least possible variable bound, even when infinite
bases are allowed. Earlier upper bounds of six in this chronological note are
superseded by this presentation.
