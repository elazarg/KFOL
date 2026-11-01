"""Actual native reductions, all winner-set valuations, independently of Lean."""
from check_fragments import Valuations, cnfs, satisfiable
from fragments import owned, raw_reduction, union_reduction, var


def check():
    for k, n in ((3, 1), (3, 2), (4, 1)):
        raw, guarded = Valuations(k, 2*n+1), Valuations(k, 2*n+3)
        formulas = cnfs(n)
        for formula in formulas:
            valid = not satisfiable(formula, n)
            raw.check(raw_reduction(formula, n), valid)
            raw.check(raw_reduction(formula, n, None), valid)
            pair = ((var(0), var(0)) if any(not c for c in formula) else
                    (var(0), var(1)) if not formula else
                    union_reduction(formula, n, lambda x, y: owned(0, x, y)))
            guarded.check(pair, valid)
        print(f"Raw pairs: K={k}, {len(formulas)} CNFs on {n} variables; "
              f"both raw reductions on all {raw.count} valuations, "
              f"reset/owned choice on all {guarded.count} valuations.", flush=True)


if __name__ == '__main__':
    check()
