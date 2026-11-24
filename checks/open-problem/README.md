# Explicit-table recognition and the offer history

For a fixed number of owners at least three, full-table and source-table
recognition are PSPACE-complete. The proof is in
[the report](../../overleaf/sections/appendix-core-table-recognition.tex)
in the separate paper checkout. The [Lean theorem](../../KFOL/Core/ExplicitTableReduction.lean)
applies to arbitrary encoded quantified CNF, proves equivalence for both tables,
and bounds their lengths. Both [machine-level classifications](../../KFOL/Complexity/TablePeelingSpace.lean)
include the upper bound and a polynomial-time many-one reduction from
quantified truth. The [uniform theorems](../../KFOL/Complexity/ExplicitTableUniform.lean)
cover the same two tables with the owner count supplied in binary.

## Reproduce the finite checks

From the repository root run the following with Python 3.

```sh
python3 checks/open-problem/explicit_table.py --qbf-suite
python3 checks/open-problem/addressed_rectangles.py --random 200
python3 checks/open-problem/test_qbf_tables.py
python3 checks/open-problem/history_pairs_selector.py
```

The first command checks source reconstruction on every menu tuple of 23
three-owner targets, tests realization with exact row deletion, and compares
260 two-variable formulas with a logically independent rectangle solver.
The second follows transported cuts and tests competing offers, including
the auxiliary owner. The third checks the fixed-assignment clause reduction
and native quantified rectangle construction. The fourth exhausts one
selector on small pairs of envelopes from the full two-input clone.

[qbf_tables.py](qbf_tables.py) computes the target from a closed QBF. Input
JSON, for example `{"quantifiers":"AE","clauses":[[1,-2],[2]]}`, uses signed
one-based variables. Supply a path as the first argument. The default output
gives the arity and table sizes. `--entry` evaluates one tuple of nonzero
player masks, and `--full-table` or `--source-table` streams one row per line.
The code numbers addresses within each track and omits unused rails. Lean
reserves a uniform set of rails and uses global label numbers. These choices
change literal table indices and preserve the reduction argument.

## Earlier invariant tests

- [Single-owner phases](phase-notes.md) admit a greatest surviving support.
  [OfferPhase.lean](../../KFOL/Core/OfferPhase.lean) proves the general
  one-owner batch criterion. [phase.py](phase.py) compares two independent
  recursions with an adoption-switch budget.
- [Distinguishable histories](history_pairs_results.md) can reach the same
  register while encoding independent answers to the next adoption.
  [history_pairs_index.py](history_pairs_index.py) and
  [history_pairs_padding.py](history_pairs_padding.py) reproduce the finite tests.
  This memory bound concerns queries at an arbitrary inherited history.
- [A family forcing nested swaps](swap-depth.tex) gives the written
  address-path construction. [OfferPath.lean](../../KFOL/Core/OfferPath.lean)
  proves its abstract rank bound. [saturated_swap_path.py](saturated_swap_path.py)
  checks the small path games after allowing safe parent preparations.
- [residual_certificate.py](residual_certificate.py) checks a rejecting
  four-input game on five rows. A SAT encoding using one residual for each
  register and order of last adoptions is unsatisfiable. Two residuals suffice
  on this instance. The [Lean proof](../../KFOL/Core/OrderedResidualObstruction.lean)
  follows the forced paths below and checks a two-residual witness directly.
  The Python version also checks the outcome with CaDiCaL.
  [residual_search.py](residual_search.py) uses two overlapping copies of the
  earlier five-row example, removing rows from each before combining them.
  With its default seed, 964 of 2,000 labelled four- to six-input games
  were feasible. Among the 1,036 rejections, 1,011 admitted a one-slot cut
  and the other 25 required exactly two. The sample contains no obstruction
  to two slots.

For fixed $K$, the table lower bound also constrains certificates at the
blank root. With $m$ negative rows there are at most $(m+1)^K$ coalition
registers and $K!$ orders per register. A cut lists residual row sets at
these registers; its heads and successor conditions are checkable by
scanning the rows. If a polynomial number of residuals per ordered
register sufficed to certify every rejected table, guessing a failed
positive and its cut would put the complement in NP and imply NP = PSPACE.
There is also an unconditional family. For every $t\ge2$, one specified
positive query with $3t+3$ inputs and $4t+2$ negative rows needs exactly
$t$ residuals at one ordered register. Five adoptions reach that register
in the same order on every path, with a different necessary row at its
only eligible head. [ParametricResiduals.lean](../../KFOL/Core/ParametricResiduals.lean)
checks the forced paths. The matching cut is proved in the report under
“Distinct row sets at one coalition assignment”.
[residual_family.py](residual_family.py) checks the construction for
$t=2$ through $32$, with a separate exact game and SAT check at $t=2,3$.
The lower bound is linear in the number of listed negative rows. A
superpolynomial unconditional lower bound remains open.

### Why the five rows require two residuals

The query has head 0 and no postings. Only owners $p$ and $q$ occur
in the negative rows. A string of digits denotes a coalition.

| Row | Head | $p$ | $q$ |
| --- | ---: | --- | --- |
| A | 0 | 2 | 1 |
| B | 1 | — | 23 |
| C | 2 | 13 | — |
| D | 3 | — | 0 |
| E | 3 | 0 | — |

A cut must retain a row at every eligible head. Each coalition occurring
in a retained row must lead to a child whose residual contains only
rows the offer leaves uncovered.

The blank root retains A. Adopting its $q:1$ forces B at head 1.
B's $q:23$ then forces a row at head 3. If E was omitted from the
root, only D can supply head 3. D's $q:0$ now demands head 0 after
the first offer discharged A. Thus E was required. Exchanging $p$
with $q$ and input 1 with input 2 shows that D was required too.

- After D's $q:0$, head 0 forces A; its $q:1$ would leave head 1
  uncovered unless B is retained. Adopt B's $q:23$, then C's $p:13$,
  which head 2 forces. Only A and E could remain; head 3 requires E.
- After E's $p:0$, head 0 forces A. Adopt A's $p:2$. Head 2 now
  forces C; its $p:13$ would leave head 1 uncovered unless B is retained.
  Adopt B's $q:23$, then C's $p:13$, again forced by head 2. Only D
  could remain; head 3 requires D.

Both paths finish with $q:23$ followed by $p:13$ as their last
adoptions. No single residual at that ordered register satisfies both
requirements. A cut on 11 eligible registers suffices: only the
register holding $p:13$ and $q:23$ needs both D and E as alternatives.
