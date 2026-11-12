# Canonical essential-source extensions

The [research package](essential-extensions/README.md) contains complete
written proofs and a self-contained standard-library checker. These are
intermediate characterization results, pending Lean formalization and report
integration. They do not settle the characterization of arbitrary canonical
source guards.

- [Quadratic graph family](essential-extensions/cograph-theorem.md): the
  canonical extension is realizable exactly for cographs.
- [Weighted majority](essential-extensions/weighted-majority-counterexample.md):
  weights (3,2,2,1,1), threshold 5 give a nonterm extension.
- [Six-variable obstruction](essential-extensions/six-variable-counterexample.md):
  every proper Boolean cofactor is realizable, and both root SCC tests pass,
  but eight forbidden marked cubes exclude a global term.
- [Relative safety](essential-extensions/relative-safety-game.md): inherited
  negative budgets explain why independently normalizing the children can
  lose realizations and why hereditary root tests are insufficient.

Run `python3 notes/research/core-functions/essential-extensions/check.py --exhaustive-cographs` to
check the finite certificates, all twelve five-variable cofactor witnesses,
and all cographs through five vertices. These checks corroborate the written
proofs; their results are not counted as kernel-checked claims.
