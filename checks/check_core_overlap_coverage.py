#!/usr/bin/env python3
"""Finite verification of native overlap coverage and its peak consequence.

Standard library only; no data files, repository imports, or solver.
The uniform all-K validity argument is mathematical, not extrapolated from
this check. The five-variable boundary is an intentional false peak.
"""
from itertools import permutations, product
import json


def native_tables(owners):
    """Atoms 0..owners-1, neutral owners, greatest marker owners+1."""
    n = owners + 2
    join = [[x if x == y else max(owners, x, y)
             for y in range(n)] for x in range(n)]
    choices = [
        [[i if i in (x, y) else join[x][y] for y in range(n)]
         for x in range(n)]
        for i in range(owners)
    ]
    return choices + [join]


def verify_overlap_and_peak():
    valuations = 0
    support_equalities = 0
    by_owner_count = {}
    for owners in range(2, 6):
        ops = native_tables(owners)
        join = ops[-1]
        carrier = range(owners + 2)
        count = 0
        for i, j in permutations(range(len(ops)), 2):
            f, g = ops[i], ops[j]
            for x, y, z, w in product(carrier, repeat=4):
                e = f[x][y]
                d = f[x][z]
                c = f[y][w]
                a = f[x][g[y][z]]
                b = f[y][g[x][w]]
                s = g[a][c]
                t = g[b][d]
                q = g[g[e][d]][c]
                middle = g[a][b]

                # OC: f(x,y) <= the join of the two overlap arms.
                cover = join[a][b]
                assert join[e][cover] == cover

                # The support insertions used in the symbolic proof.
                ed = g[e][d]
                ec = g[e][c]
                assert g[a][ed] == ed
                assert g[b][ec] == ec
                assert g[q][middle] == q
                assert join[s][q] == q == join[t][q]
                support_equalities += 5
                for h in ops:
                    assert h[s][q] == q == h[t][q]
                    assert h[s][t] == q
                    support_equalities += 2

                # Peak consequence and its native residual-fiber equality.
                assert g[s][t] == q
                assert g[s][t] == join[s][t]
                assert q == join[s][t]
                count += 1
        by_owner_count[str(owners)] = count
        valuations += count
    assert valuations == 106986
    return valuations, support_equalities, by_owner_count


def verify_false_five_variable_peak():
    f, g, join = native_tables(2)
    alpha, beta, neutral, greatest = range(4)
    x, y, z, u, v = neutral, neutral, greatest, beta, beta
    q = g[g[f[f[x][y]][z]][f[x][u]]][f[y][v]]
    s = g[f[x][g[f[y][z]][u]]][f[y][v]]
    t = g[f[y][g[f[x][z]][v]]][f[x][u]]
    assert (q, s, t, join[s][t]) == (greatest, neutral, neutral, neutral)
    assert q != join[s][t]
    # Residual common-fiber coherence still holds at this countervaluation.
    assert all(h[s][t] == join[s][t] for h in (f, g, join))
    return {
        "native_generator": "D_2",
        "valuation": {"x": "n", "y": "n", "z": "p",
                      "u": "beta", "v": "beta"},
        "Q": "p", "S": "n", "T": "n", "S_plus_T": "n",
        "residual_R_S_T": True,
    }


def main():
    valuations, supports, by_k = verify_overlap_and_peak()
    boundary = verify_false_five_variable_peak()
    print(json.dumps({
        "status": "PASS",
        "owner_counts": [2, 3, 4, 5],
        "ordered_distinct_operations_include_join": True,
        "overlap_and_peak_valuations": valuations,
        "valuations_by_owner_count": by_k,
        "peak_support_equalities": supports,
        "false_five_variable_peak": boundary,
    }, indent=2))


if __name__ == "__main__":
    main()
