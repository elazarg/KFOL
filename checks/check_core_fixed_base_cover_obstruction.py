#!/usr/bin/env python3
"""A genuine-core obstruction to supported covers over a prescribed base.

Construct the algebra as a subalgebra of an atomic square times D2 with
a common absorbing point. Independently verify a twenty-point native cover.
Standard library only; no solver, repository imports, or external data.
"""
from itertools import permutations, product
import json


def native(k):
    size = k + 2
    join = [[x if x == y else max(k, x, y) for y in range(size)]
            for x in range(size)]
    choices = [[[i if i in (x, y) else join[x][y] for y in range(size)]
                for x in range(size)] for i in range(k)]
    return choices + [join]


def construct():
    f, g, join = native(2)
    basic = [f, g, join, join]  # Three choices, then designated join.
    base = [(0, 1), (0, 2), (2, 1), (2, 2)]  # d, a, b, n
    base_index = {x: i for i, x in enumerate(base)}
    c_ops = [[[base_index[tuple(h[u][v] for u, v in zip(x, y))]
               for y in base] for x in base] for h in basic]
    infinity = 4
    b_ops = [[[infinity if infinity in (x, y) else h[x][y]
               for y in range(5)] for x in range(5)] for h in basic]
    points = [(0, 4), (1, 0), (1, 4), (2, 1), (2, 4), (3, 2), (3, 3), (3, 4)]
    index = {x: i for i, x in enumerate(points)}
    tables = [[[index[(hc[x[0]][y[0]], hb[x[1]][y[1]])]
                for y in points] for x in points]
              for hc, hb in zip(c_ops, b_ops)]
    return basic, base, c_ops, points, tables


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


def main():
    basic, base, c_ops, points, tables = construct()
    join = tables[-1]
    rho = [c for c, _ in points]
    law_count = laws(tables)
    for h, ch in zip(tables, c_ops):
        for x, y in product(range(8), repeat=2):
            assert rho[h[x][y]] == ch[rho[x]][rho[y]]
            if rho[x] == rho[y]:
                assert h[x][y] == join[x][y]

    # The inverse image of A inside C x (D2 x {n,p}) is a native subpower.
    mapping = {}
    for c, (a, b) in enumerate(base):
        for x, flag in product(range(4), (2, 3)):
            value = (c, x if flag == 2 else 4)
            if value in points:
                mapping[(a, b, x, flag)] = points.index(value)
    assert len(mapping) == 20 and set(mapping.values()) == set(range(8))
    cover_entries = 0
    for h, target in zip(basic, tables):
        for x, y in product(mapping, repeat=2):
            z = tuple(h[a][b] for a, b in zip(x, y))
            assert z in mapping
            assert mapping[z] == target[mapping[x]][mapping[y]]
            cover_entries += 1

    zero = {1, 3, 5}
    psi = [int(x not in zero) for x in range(8)]
    p = 6
    assert {x for x in range(8) if join[x][5] == 5} == zero
    for x in range(8):
        if psi[x]:
            assert join[p][join[5][x]] == join[5][x]
    types = {a: next((i for i, h in enumerate(tables[:3])
                      if not psi[h[a][p]]), 3) for a in zero}
    assert types == {1: 0, 3: 1, 5: 3}
    rhs = join[tables[0][p][1]][tables[1][p][3]]
    assert rhs == 5 and join[p][rhs] == p != rhs

    observer_counts = []
    upper_cases = 0
    for k in range(2, 6):
        target = native(k)
        atom_ops = [h[:k + 1] for h in target]  # Inputs below use only atomic values.
        source_ops = c_ops[:2] + [c_ops[-1]] * (k - 2) + [c_ops[-1]]
        observers = []
        for phi in product(range(k + 1), repeat=4):
            if phi[3] != k:
                continue
            if all(phi[h[x][y]] == nh[phi[x]][phi[y]]
                   for h, nh in zip(source_ops, atom_ops)
                   for x, y in product(range(4), repeat=2)):
                observers.append(phi)
        assert len(observers) == 3
        assert not any(phi[1] == 0 and phi[2] == 1 for phi in observers)
        for phi in observers:
            assert phi[1] == k or phi[2] == k
            supported = lambda c: [phi[c]] if phi[c] < k else [k, k + 1]
            for a, b, value in product(supported(1), supported(2), supported(3)):
                bound = target[-1][target[0][value][a]][target[1][value][b]]
                assert target[-1][value][bound] == bound
                upper_cases += 1
        observer_counts.append({"owners": k, "top_neutral_observers": len(observers)})
    print(json.dumps({"status": "PASS", "states": 8,
                      "candidate_law_instances": law_count,
                      "native_cover_states": len(mapping),
                      "native_cover_entries": cover_entries,
                      "atomic_base_size": 4, "minimal_cut_zero_set": sorted(zero),
                      "witness": {"left": p, "right": rhs},
                      "observers": observer_counts,
                      "supported_upper_valuations": upper_cases,
                      "scope": "Genuine core; prescribed-base supported cover and partial-observer extension fail."}, indent=2))


if __name__ == "__main__":
    main()
