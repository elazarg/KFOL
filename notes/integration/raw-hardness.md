# Native hard-pair reductions integration

## Pure two-guarded-owner reduction: complete mathematics

Production `KFOL.Reductions.GuardedPair` proves the report's
`thm:H-hardness` native reduction mathematics, including the third-role
observational clause. Definitions are consolidated in existing
`KFOL/Definitions/Reductions.lean`; the new signature is
`GuardedPair.Symbol.guarded : Bool → Symbol 3`. There is no primitive reset,
union, role constant, winner constant, or switch. `true` interprets H_a,
`false` H_b. Every reset is the original expanded native tree
`Term.reset s t = Term.guarded true t s s`.

`Reductions.GuardedPair.equation formula` is exactly the report construction:
W is the right reset comb of source Boolean inputs over root z;
clause branches nest the literal's H owner over z, y_i and the remaining
branch; R is the right reset comb of those branches over W;
the equation is c reset R = R. Inputs are z=0,c=1,y_i=i+2.
The shared sparse support includes dummy0 and every listed source variable;
no numerical maximum controls output construction.

The complete public statement is:

```lean
{Role : Type u} (a b d : Role)
(hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    (Reductions.GuardedPair.equation formula).1.eval a b v =
      (Reductions.GuardedPair.equation formula).2.eval a b v) ↔
    ¬Reductions.Satisfiable formula
```

Proof: `Reductions.GuardedPair.equation_valid_iff_unsatisfiable`.
`third_role_observation_valid_iff_unsatisfiable` proves the same equivalence
with the full equality replaced by d-membership equivalence on every
valuation. `satisfying_assignment_separates` exhibits the actual d marker:
true inputs are {a}, false inputs {b}, z={a,b}, c={d}; d belongs to the left
and is absent on the right. `guarded_marker` handles every marker, including
a marker equal to a guarded owner, so the UNSAT argument quantifies over
all winner-set valuations.

The exact combined original expanded tree size is:

```
left.size + right.size =
  5 + 6*support.length + 6*formula.length + 12*sum(clause.length).
```

Proof: `Reductions.GuardedPair.equation_size`. It holds for every CNF,
including empty clauses and empty conjunctions, without a width-three
hypothesis. The right comb duplicates each small literal or clause branch;
it never duplicates an accumulated left-comb continuation. The clause gates
retain one continuation occurrence. Generic fixed finite signature
codecs/native constructors are assigned to the complexity worker; fixed
alphabet runtime is not presented as a uniform-K theorem.

Validation: `lake build KFOL.Reductions.GuardedPair` passed1190 jobs;
`tests/ReductionsGuardedPair.lean` checks empty formula/empty clause,
actual native expanded sizes, sparse variable1000000000, universally valid
empty-clause equation, and the exact third-role SAT witness. Standard axiom
guards cover equality, third-role observation, and exact size.

Remaining: native word generation/validity frontend/class transport belongs
to the complexity worker. Required raw binary pairs are the next pure
mathematical slice; they are not counted as completed by this H result.
