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

The final polynomial-time clause remains separate, so do not mark the whole
one-table main theorem complete yet.

## Integration chores for root

Import `KFOL.Owner` where desired; extend exact audit coverage with the definition
and proof modules; include all pure modules in the pure build closure;
copy full propositions to root `Paper.lean` with axiom guards; update inventory
and definition index, marking root/guard main results complete and one-table
partial for machine time. Root and guard semantics have no global K≥3 hypothesis.
The three-role requirements occur only at separation/completeness.

## Current continuation

Four-element generator semantic equivalence and one-owner realizability/synthesis
are next in this branch. Minimum-generator exclusion and forty-law completeness
are explicitly separate and not yet provided.

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
The forty-law basis and four-variable lower bound remain separate work.
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
occur in this semantic synthesis slice. Forty-law completeness and the
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
and forty-law generic completeness remain separate work.

Validation: production `lake build KFOL.Owner.BasisObstruction` passed
1119 jobs; `tests/OwnerBasisObstruction.lean` checks W's cardinality,
root-expansion's exact support and the two distinct values, plus standard
axiom guards for the full actual-support transfer and lower-bound theorems.
