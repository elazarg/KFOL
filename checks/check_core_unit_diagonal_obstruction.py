#!/usr/bin/env python3
"""Check the unit-diagonal obstruction and its ten-state core reconstruction.

Standard library only; no external data, solver, or free-algebra cache.
The nine-state base is a literal subalgebra of the proper native D2 cubed.
Its ten-state bit reconstruction embeds subdirectly into D2 times B9.
B9 is checked as a legal bit doubling of an eight-state atomic lattice;
the atomic-region-doubling theorem therefore supplies its core membership.
All finite law counts below concern three choices, the third equal to join.
"""

from collections import Counter
from itertools import permutations, product
import json


ALPHA, BETA, NEUTRAL, UPPER = range(4)


def native_tables():
    """Operation order is designated join, f, g throughout this checker."""
    join = [[x if x == y else max(NEUTRAL, x, y)
             for y in range(4)] for x in range(4)]
    return [join] + [
        [[owner if owner in (x, y) else join[x][y]
          for y in range(4)] for x in range(4)]
        for owner in (ALPHA, BETA)
    ]


def subpower_tables(points, scalar):
    index = {point: i for i, point in enumerate(points)}
    assert len(index) == len(points)
    tables = []
    count = 0
    for operation in scalar:
        table = []
        for x in points:
            row = []
            for y in points:
                value = tuple(operation[a][b] for a, b in zip(x, y))
                assert value in index, (x, y, value)
                row.append(index[value])
                count += 1
            table.append(row)
        tables.append(table)
    return tables, count


def reset(tables, coefficient, value):
    join, f, g = tables
    result = join[coefficient][value]
    for operation in (f, g, join):
        result = operation[value][result]
    return result


def bit_doubling(base, points, owned):
    index = {point: i for i, point in enumerate(points)}
    tables = []
    for operation in base:
        table = []
        for x, bit_x in points:
            row = []
            for y, bit_y in points:
                value = operation[x][y]
                bit = 0 if value in owned else bit_x | bit_y
                assert (value, bit) in index
                row.append(index[value, bit])
            table.append(row)
        tables.append(table)
    return tables


def laws(tables):
    """Exhaustive Gamma_3, all ordered M, and E_3 table verification."""
    join, f, g = tables
    choices = (f, g, join)
    carrier = range(len(join))
    counts = Counter()
    for operation in (*choices, join):
        for x in carrier:
            assert operation[x][x] == x
            counts["ACI"] += 1
        for x, y in product(carrier, repeat=2):
            assert operation[x][y] == operation[y][x]
            counts["ACI"] += 1
        for x, y, z in product(carrier, repeat=3):
            assert operation[x][operation[y][z]] == operation[operation[x][y]][z]
            counts["ACI"] += 1
    for operation in choices:
        for x, y, z in product(carrier, repeat=3):
            assert operation[x][join[y][z]] == join[operation[x][y]][operation[x][z]]
            counts["distribution"] += 1
    for h, k in permutations(choices, 2):
        for x, y in product(carrier, repeat=2):
            assert join[h[x][y]][k[x][y]] == join[x][y]
            assert h[x][k[x][y]] == k[x][h[x][y]]
            counts["pair_coverage_and_Birkhoff"] += 2
        for x, y, z in product(carrier, repeat=3):
            assert h[x][k[y][h[y][z]]] == h[x][k[y][h[x][h[y][z]]]]
            counts["ordered_M"] += 1
    for h, k, ell in permutations(choices):
        for x, y in product(carrier, repeat=2):
            assert ell[h[x][y]][k[x][y]] == join[x][y]
            counts["third_choice_coverage"] += 1
    for c, x, y, z in product(carrier, repeat=4):
        bound = join[join[f[c][x]][g[c][y]]][join[c][z]]
        assert join[c][bound] == bound
        counts["E3"] += 1
    return dict(counts)


def homomorphism(source, target, mapping):
    assert set(mapping) == set(range(len(target[0])))
    count = 0
    for h, k in zip(source, target):
        for x, y in product(range(len(mapping)), repeat=2):
            assert mapping[h[x][y]] == k[mapping[x]][mapping[y]]
            count += 1
    return count


def atomic_section(tables, scalar, lower, neutral, upper):
    labels = {lower: ALPHA, neutral: NEUTRAL, upper: BETA}
    count = 0
    for operation, target in zip(tables, scalar):
        for x, y in product(labels, repeat=2):
            assert operation[x][y] in labels
            assert labels[operation[x][y]] == target[labels[x]][labels[y]]
            count += 1
    return count


def main():
    scalar = native_tables()
    a, b, n, p = ALPHA, BETA, NEUTRAL, UPPER
    q_points = [
        (a, a, a), (n, a, a), (n, n, n), (b, n, b), (b, b, b),
        (a, b, p), (a, n, p), (n, b, p), (n, n, p),
    ]
    q, q_entries = subpower_tables(q_points, scalar)
    join, f, g = q
    e, lower, upper = 2, 0, 4
    ideal = {x for x in range(9) if join[e][x] == e}
    units = {c for c in range(9)
             if all(reset(q, c, x) == x for x in range(9))}
    assert ideal == units == set(range(5))
    reflection_entries = 0
    for operation in q:
        for x in range(9):
            assert join[e][operation[e][x]] != e or x in ideal
            reflection_entries += 1
    for x, y in product(range(5), repeat=2):
        assert f[x][y] == min(x, y)
        assert g[x][y] == max(x, y)

    # Any compatible relation diagonal on I would have to label point 5
    # by a point i satisfying BOTH equations; no such unit point exists.
    assert f[1][5] == lower and g[3][5] == upper
    f_labels = [i for i in ideal if f[1][i] == lower]
    g_labels = [i for i in ideal if g[3][i] == upper]
    assert f_labels == [lower] and g_labels == [upper]
    assert not set(f_labels) & set(g_labels)

    section = {lower, e, upper}
    section_entries = atomic_section(q, scalar, lower, e, upper)
    a_points = [(x, 0 if x in section else 1) for x in range(9)] + [(e, 1)]
    a10 = bit_doubling(q, a_points, {lower, upper})
    a_laws = laws(a10)

    # The second factor remembers the first two native coordinates and bit.
    # Its base is exactly B2^2 minus the reversed corner (beta, alpha).
    j_points = sorted({point[:2] for point in q_points})
    assert set(j_points) == set(product(range(3), repeat=2)) - {(b, a)}
    j, j_entries = subpower_tables(j_points, scalar)
    j_index = {point: i for i, point in enumerate(j_points)}
    j_lower, j_e, j_upper = (j_index[value] for value in ((a, a), (n, n), (b, b)))
    assert all(reset(j, x, y) == y for x, y in product(range(8), repeat=2))
    section_entries += atomic_section(j, scalar, j_lower, j_e, j_upper)
    b_points = []
    b_map = []
    for old, bit in a_points:
        point = (j_index[q_points[old][:2]], bit)
        if point not in b_points:
            b_points.append(point)
        b_map.append(b_points.index(point))
    assert len(b_points) == 9
    assert set(b_points) == {
        (x, 0 if x in (j_lower, j_e, j_upper) else 1) for x in range(8)
    } | {(j_e, 1)}
    b9 = bit_doubling(j, b_points, {j_lower, j_upper})
    b_laws = laws(b9)

    # The displayed finite atomic-region theorem applies directly to J.
    jj, jf, jg = j
    regional_entries = 0
    for x in range(8):
        assert (jf[x][j_e] == j_lower) == (x == j_lower)
        assert (jg[x][j_e] == j_upper) == (x == j_upper)
        regional_entries += 2
    for x, y in product(range(8), repeat=2):
        if jf[x][y] == j_lower and jg[x][y] == j_upper:
            assert x in (j_lower, j_upper) and y in (j_lower, j_upper)
        regional_entries += 1

    # First factor: the OLD third native coordinate, even at upper e.
    native_map = [q_points[old][2] for old, _ in a_points]
    native_entries = homomorphism(a10, scalar, native_map)
    factor_entries = homomorphism(a10, b9, b_map)
    assert len(set(zip(native_map, b_map))) == 10
    assert b_map == [0, 1, 2, 3, 4, 5, 6, 7, 8, 8]
    assert native_map[8] == p and native_map[9] == n

    # The complete reconstruction is generated by its three named inputs.
    generated = {1, 3, 5}
    while True:
        expanded = generated | {
            operation[x][y] for operation in a10 for x in generated for y in generated
        }
        if expanded == generated:
            break
        generated = expanded
    assert generated == set(range(10))

    print(json.dumps({
        "status": "PASS", "base_size": 9, "unit_ideal_size": 5,
        "reconstruction_size": 10, "factors": [4, 9], "atomic_base_size": 8,
        "native_subpower_products": q_entries + j_entries,
        "reflection_entries": reflection_entries, "incompatible_unit_labels": [f_labels, g_labels],
        "A10_law_instances": sum(a_laws.values()), "B9_law_instances": sum(b_laws.values()),
        "regional_entries": regional_entries,
        "atomic_section_entries": section_entries,
        "subdirect_homomorphism_entries": native_entries + factor_entries,
        "generated_by": [1, 3, 5],
        "core_certificate": "subdirect product of proper native D2 and a legal atomic-region doubling",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
