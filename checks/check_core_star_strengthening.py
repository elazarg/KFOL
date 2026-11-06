#!/usr/bin/env python3
"""Actual-row star identities and a core refutation of abstract guarded Merge.

Standard library only, with explicit tables and an eleven-point proper
native cover. The native case proof is separate; finite checks do not
assert preservation of these quasiidentities under homomorphic images.
"""
from itertools import permutations, product
import json


def native(k):
    n = k + 2
    join = [[x if x == y else max(k, x, y) for y in range(n)] for x in range(n)]
    return [[[i if i in (x, y) else join[x][y] for y in range(n)]
             for x in range(n)] for i in range(k)] + [join]


def counterexample():
    join = [[0,1,2,3,4,5], [1,1,5,5,5,5], [2,5,2,5,5,5],
            [3,5,5,3,4,5], [4,5,5,4,4,5], [5,5,5,5,5,5]]
    g = [[0,0,0,0,0,0], [0,1,0,1,1,1], [0,0,2,2,2,2],
         [0,1,2,3,3,5], [0,1,2,3,4,5], [0,1,2,5,5,5]]
    return [join, g, join, join]


def laws(tables):
    choices, join = tables[:3], tables[-1]
    r = range(len(join))
    count = 0
    for h in tables:
        for x in r:
            assert h[x][x] == x
            count += 1
        for x, y in product(r, repeat=2):
            assert h[x][y] == h[y][x]
            count += 1
        for x, y, z in product(r, repeat=3):
            assert h[x][h[y][z]] == h[h[x][y]][z]
            count += 1
    for h in choices:
        for x, y, z in product(r, repeat=3):
            assert h[x][join[y][z]] == join[h[x][y]][h[x][z]]
            count += 1
    for h, k in permutations(choices, 2):
        for x, y in product(r, repeat=2):
            assert join[h[x][y]][k[x][y]] == join[x][y]
            assert h[x][k[x][y]] == k[x][h[x][y]]
            count += 2
        for x, y, z in product(r, repeat=3):
            assert h[x][k[y][h[y][z]]] == h[x][k[y][h[x][h[y][z]]]]
            count += 1
    for h, k, ell in permutations(choices):
        for x, y in product(r, repeat=2):
            assert ell[h[x][y]][k[x][y]] == join[x][y]
            count += 1
    for c, x, y, z in product(r, repeat=4):
        out = join[join[choices[0][c][x]][choices[1][c][y]]][choices[2][c][z]]
        assert join[c][out] == out
        count += 1
    return count



def star_row_closure(tables):
    """Check all nonempty row folds, by exact closure of (A_i,U_i) pairs.

    This closes ACTUAL term rows, not the larger abstract guarded relation.
    Every added pair has a stored finite row-fold construction. Final closure
    and support checks cover every arity in this particular finite algebra.
    """
    n = len(tables[-1])
    join = tables[-1]
    support = [[join[a][b] == b and all(h[a][b] == b for h in tables)
                for b in range(n)] for a in range(n)]
    total_seeds = total_states = constructions = contexts = 0
    maximum_rows = 0
    for fi, gi in permutations(range(len(tables)), 2):
        f, g = tables[fi], tables[gi]
        for y in range(n):
            states = []
            index = {}
            reasons = []
            widths = []
            for x, z, r in product(range(n), repeat=3):
                row = (f[x][g[f[y][z]][r]], f[x][z])
                if row not in index:
                    index[row] = len(states)
                    states.append(row)
                    reasons.append(("row", x, z, r))
                    widths.append(1)
            seed_count = len(states)
            position = 0
            while position < len(states):
                a, u = states[position]
                for other in range(position + 1):
                    b, v = states[other]
                    value = (g[a][b], g[u][v])
                    if value not in index:
                        index[value] = len(states)
                        states.append(value)
                        reasons.append(("fold", position, other))
                        widths.append(widths[position] + widths[other])
                position += 1
            # Independently replay generatedness and verify full closure.
            for i, reason in enumerate(reasons):
                if reason[0] == "row":
                    _, x, z, r = reason
                    assert states[i] == (f[x][g[f[y][z]][r]], f[x][z])
                else:
                    _, left, right = reason
                    assert left < i and right < i
                    a, u = states[left]
                    b, v = states[right]
                    assert states[i] == (g[a][b], g[u][v])
            for (a, u), (b, v) in product(states, repeat=2):
                assert (g[a][b], g[u][v]) in index
            for a, u in states:
                d = g[a][f[y][u]]
                assert support[a][d]
            total_seeds += seed_count
            total_states += len(states)
            constructions += len(states) - seed_count
            maximum_rows = max(maximum_rows, max(widths))
            contexts += 1
    return {"fixed_y_operation_contexts": contexts,
            "actual_seed_pairs": total_seeds,
            "closed_row_pairs": total_states,
            "nontrivial_fold_constructions": constructions,
            "largest_replayed_row_fold": maximum_rows,
            "scope": "Every positive arity in this finite algebra, via exact actual-row closure."}


def residual_path(tables):
    """Exhaust the three-edge private-residual path (the R5 instance)."""
    n = len(tables[-1])
    join = tables[-1]
    count = 0
    for fi, gi in permutations(range(len(tables)), 2):
        f, g = tables[fi], tables[gi]
        for x, y, z, u, v in product(range(n), repeat=5):
            s = g[f[x][g[f[y][z]][u]]][f[y][v]]
            t = g[f[y][g[f[x][z]][v]]][f[x][u]]
            w = g[s][t]
            assert join[s][w] == w == join[t][w]
            assert all(h[s][w] == w == h[t][w] for h in tables)
            assert w == join[s][t]
            assert all(h[s][t] == w for h in tables)
            count += 1
    return count


def n4_common_lower(tables):
    """Check the proved two-active-choice N4 chain, including all h owners."""
    n = len(tables[-1])
    join = tables[-1]
    support = [[join[a][b] == b and all(h[a][b] == b for h in tables)
                for b in range(n)] for a in range(n)]
    count = 0
    for fi, gi in permutations(range(len(tables)), 2):
        f, g = tables[fi], tables[gi]
        for a, b, c, d in product(range(n), repeat=4):
            ab = g[a][b]
            s = f[ab][g[g[a][c]][d]]
            t = g[g[a][f[b][c]]][f[ab][d]]
            lower = g[a][f[b][g[c][d]]]
            middle = g[g[a][f[b][c]]][f[b][d]]
            assert support[lower][s]
            assert support[lower][middle]
            assert support[middle][t]
            assert all(h[s][t] == join[s][t] for h in tables)
            count += 1
    return count


def main():
    tables = counterexample()
    law_count = laws(tables)
    f, g, _, join = tables
    a = b = 4
    y, u, v = 3, 1, 2
    guard_a, guard_b = g[a][f[y][u]], g[b][f[y][v]]
    for low, up in ((a, guard_a), (b, guard_b)):
        assert all(h[low][up] == up for h in tables)
    c = g[a][b]
    d = g[c][f[y][g[u][v]]]
    assert (guard_a, guard_b, c, d, join[c][d]) == (5, 5, 4, 3, 4)
    assert join[c][d] != d
    assert all(g[4][x] == x for x in range(6))

    # Native D3 values: beta=owner1 atom1, neutral3, greatest marker4.
    cover = {(1,1,1):0, (1,4,1):1, (3,3,1):3, (3,3,3):4,
             (3,4,1):5, (3,4,3):5, (4,1,1):2, (4,3,1):5,
             (4,3,3):5, (4,4,1):5, (4,4,3):5}
    scalar = native(3)
    assert set(cover.values()) == set(range(6))
    cover_entries = 0
    for source_op, target_op in zip(scalar, tables):
        for x, z in product(cover, repeat=2):
            value = tuple(source_op[xx][zz] for xx, zz in zip(x, z))
            assert value in cover
            assert cover[value] == target_op[cover[x]][cover[z]]
            cover_entries += 1
    assert cover_entries == 484
    models = {f"D{k}": native(k) for k in range(2, 6)}
    models["six_state_core"] = tables
    row_checks = {name: star_row_closure(ops) for name, ops in models.items()}
    path_checks = {name: residual_path(models[name])
                   for name in ("D2", "D3", "six_state_core")}
    n4_checks = {name: n4_common_lower(models[name])
                 for name in ("D2", "D3", "six_state_core")}
    print(json.dumps({"status": "PASS", "counterexample_states": 6,
                      "candidate_law_instances": law_count,
                      "native_cover_states": len(cover),
                      "native_cover_entries": cover_entries,
                      "guard_valuation_a_b_y_u_v": [a,b,y,u,v],
                      "guard_values": [guard_a,guard_b],
                      "guard_conclusion_left_right_join": [c,d,join[c][d]],
                      "actual_row_star_checks": row_checks,
                      "private_residual_path_valuations": path_checks,
                      "N4_common_lower_valuations": n4_checks,
                      "scope": "The abstract guarded quasiidentities fail in the core. Actual-row Star identities and their bounded-degree graph consequences are distinct."}, indent=2))


if __name__ == '__main__':
    main()
