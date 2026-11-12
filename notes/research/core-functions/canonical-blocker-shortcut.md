# Column-sound blockers do not close a target query

This is a finite research counterexample, not a new manuscript or Lean claim.
It rules out checking only the target's owner cuts while accepting auxiliary
blockers merely because they hold on the input columns. It does not refute
the complete boundary/no-trap theorem, which checks the auxiliary clauses too.

## The precise proposed shortcut

For supplied input columns, let `Sound(p,S)` mean that every column satisfies
`p => OR S`; a missing premise means a pure disjunction. Put

    B_r(S,i) = S union {(i,s): s != r}.

For a target clause with premise `p=(q,k)` and head H, impose:

1. `Sound(p,H)`;
2. for every owner r and every proper cut S of H containing all r-colored
   vertices of H, some `(i,a)` in `H\S` has the following column-sound blockers:
   - if r=k: `Sound(none,B_r(S,i))`;
   - otherwise: `Sound((q,s),B_r(S,i))` for every s different from r.

This is the literal target-edge cut test from `Diagram.NoTrap`, with supports
replaced by the canonical, directly computed predicate `Sound`. `Sound`
automatically has row nonemptiness, pure weakening and membership tautologies.
The shortcut would conclude that the target holds for every core term.
That conclusion is false.

## Five genuine canonical probes

Take roles 0,1,2 and variables X,Y,Z,W. A string such as `02` denotes the
ambiguous set `{0,2}`. The observer and isolated source are shown at right.

| Row | X | Y | Z | W | Observer | Source |
| --- | --- | --- | --- | --- | --- | --- |
| q | 1 | 02 | 0 | 02 | 1 | X |
| A | 0 | 2 | 01 | 0 | 2 | Y |
| B | 0 | 01 | 2 | 0 | 2 | Z |
| C | 0 | 2 | 2 | 2 | 0 | X |
| D | 1 | 1 | 0 | 2 | 2 | W |

Every source value is its observer's singleton. Every other entry is either
another owner's singleton or the complement of the observer, the exact
neutral representative in `Sources.probe` for three roles. Thus this is a
subtable of the actual canonical source-probe table, not an unrestricted
winner-valued surrogate.

Write `a=2A`, `b=2B`, `c=0C`, `d=2D`. The target is

    1q => a or b or c or d.                              (Q)

Only column X satisfies the premise, and it meets c. Hence (Q) is column-sound.

## Every target cut passes

Let H={a,b,c,d}. The following cases exhibit a blocker for every permitted cut.

- **Owner 0.** Every cut contains c. If d is absent, expose d: the off-owner
  block `1D or 2D` meets every column having 1 or 2 at q. If d is present,
  expose any missing a or b. Column X meets c; column W meets d; column Y
  meets either `1A or 2A` or `1B or 2B`. These are all columns having 1 or 2
  at q, so both required conditional blockers hold.
- **Owner 1.** Pure blockers are required. If one of a,b,c is missing, expose
  it. Each of the row blocks `0A or 2A`, `0B or 2B`, and `0C or 2C` meets
  all four columns. Otherwise the proper cut is {a,b,c}; expose d. The
  blocker `{a,b,c,0D,2D}` is met respectively by c,a,b,d in columns X,Y,Z,W.
- **Owner 2.** The only proper cut contains a,b,d and omits c. Expose c. The
  blocker head is `{a,b,d,0C,1C}`. Columns X,Y,Z,W meet c,a,b,d respectively,
  so the required premises 0q and 1q are both covered.

There are respectively 7,15,1 cuts for owners 0,1,2. The accompanying checker
verifies every one directly, including all required conditional stems.

## A two-choice counterterm

Let

    u = Z star_0 W,
    t = X star_2 u.

Their row values are

| Term | q | A | B | C | D |
| --- | --- | --- | --- | --- | --- |
| u | 0 | 0 | 0 | 2 | 0 |
| t | 01 | 0 | 0 | 2 | 01 |

Thus t has winner 1 at q and misses every atom in H, violating (Q).
The failure already appears in a blocker that the one-pass test accepts:

    0q => a or b or d or 0C or 1C.                     (B)

This blocker is column-sound: columns X,Y,Z,W meet c,a,b,d respectively.
But u has 0 at q and meets none of its head, so (B) is not a valid all-term
clause. For owner 2 it is one of the mandatory blockers of (Q). The outer
owner-2 choice turns that invalid auxiliary blocker into the failed target.

## Consequence

Quantifying over every cut of the target does not make input-column soundness
an adequate replacement for auxiliary invariant support. This also explains
why simply taking all column-sound heads is too permissive. Checking the
auxiliary blockers again would be a repeated closure procedure; the example
does not supply the desired short direct global guard criterion.

Run the independent standard-library checker with:

    python3 notes/research/core-functions/check-canonical-blocker-shortcut.py
