# Explicit-table recognition and the offer history

For a fixed number of owners at least three, full-table and source-table
recognition are PSPACE-complete. The proof is in
[the report](../../overleaf/sections/appendix-core-table-recognition.tex)
in the separate paper checkout. The [Lean theorem](../../KFOL/Core/ExplicitTableReduction.lean)
applies to arbitrary encoded quantified CNF, proves equivalence for both tables,
and bounds their lengths. The report's verification appendix distinguishes
semantic proofs, machine certificates, and independent finite checks.

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
  on this instance. This check uses CaDiCaL.
