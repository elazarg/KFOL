"""Audit the candidate's preservation under opposite unitizations.

The arbitrary-algebra proof is in appendix-core-basis.tex. This finite audit
checks the intermediate equations of the new absorption proof, every law on
the unitized tables, and the old six-state obstruction. It does not establish
completeness of the candidate.
"""

from collections import Counter
from itertools import permutations, product

from check_core_owned_reset import test_models
from core_basis import MIXED_JOIN, MIXED_OPERATIONS
from core_two_owner_unitization import unitize


def audit_candidate(tables, mixed=True):
    add, f, g = tables
    carrier = range(len(add))
    counts = Counter()
    for table in tables:
        for x in carrier:
            assert table[x][x] == x
        for x, y in product(carrier, repeat=2):
            assert table[x][y] == table[y][x]
        for x, y, z in product(carrier, repeat=3):
            assert table[x][table[y][z]] == table[table[x][y]][z]
        counts['associativity'] += len(carrier) ** 3
    for table in (f, g):
        for x, y, z in product(carrier, repeat=3):
            assert table[x][add[y][z]] == add[table[x][y]][table[x][z]]
        counts['distribution'] += len(carrier) ** 3
    for x, y in product(carrier, repeat=2):
        assert add[f[x][y]][g[x][y]] == add[x][y]
        assert f[x][g[x][y]] == g[x][f[x][y]]
    counts['coverage_and_birkhoff'] += len(carrier) ** 2
    if mixed:
        for h, k in ((f, g), (g, f)):
            for x, y, z in product(carrier, repeat=3):
                assert h[x][k[y][h[y][z]]] == h[x][k[y][h[x][h[y][z]]]]
            counts['mixed_absorption'] += len(carrier) ** 3
    return counts


def audit_join_absorption(add, f, g):
    """Check the intermediate equalities used in both new written proofs."""
    carrier = range(len(add))
    triples = 0
    for x, y, z in product(carrier, repeat=3):
        c = f[x][y]
        v, w = f[x][g[y][z]], f[x][g[y][f[x][z]]]
        q, r = g[y][f[y][z]], g[y][f[x][f[y][z]]]
        t = f[x][q]
        assert t == f[x][r] == f[y][v] == f[y][w]
        assert add[v][f[y][v]] == add[w][f[y][w]]
        assert add[t][v] == add[c][v]
        assert add[t][w] == add[c][w]
        assert add[c][v] == add[c][w]

        ex, ez = add[x][f[y][x]], add[z][f[y][z]]
        assert add[v][f[y][v]] == f[ex][g[y][ez]]
        assert add[w][f[y][w]] == f[ex][g[y][f[ex][ez]]]
        assert add[y][q] == q and f[y][q] == q
        assert add[c][t] == t and f[x][g[y][c]] == c
        middle = f[g[y][x]][q]
        assert add[r][middle] == middle
        assert add[middle][add[t][q]] == add[t][q]
        assert add[r][add[t][q]] == add[t][q]
        b, s = f[x][g[y][x]], g[y][c]
        assert add[b][add[x][c]] == add[x][c]
        assert add[s][add[y][c]] == add[y][c]
        assert add[q][g[y][z]] == add[y][g[y][z]]
        upper = add[x][add[q][g[y][z]]]
        assert add[r][upper] == upper
        assert add[g[y][f[x][z]]][upper] == upper
        triples += 1
    return triples


def check():
    models = test_models()
    triples = 0
    pairs = {}
    for add, operations in models:
        for f, g in permutations(operations, 2):
            triples += audit_join_absorption(add, f, g)
            tables = (add, f, g)
            key = tuple(tuple(tuple(row) for row in table) for table in tables)
            pairs[key] = tables
    totals = Counter()
    for tables in pairs.values():
        lifted = unitize(tables)
        totals.update(audit_candidate(lifted))
        unit = len(lifted[0]) - 1
        assert all(lifted[1][unit][x] == x and lifted[2][unit][x] == unit
                   for x in range(unit + 1))

    # The two orientations occur among the ordered pairs above. Also check
    # the iteration, including retention of the first endpoint, on the
    # largest stored obstruction to shallow observation.
    add, operations = next((add, ops) for add, ops in models if len(add) == 24)
    f, g = operations[:2]
    twice = unitize(unitize((add, f, g)), 1)
    totals.update(audit_candidate(twice))
    first, second = 2 * len(add), 4 * len(add) + 2
    assert all(twice[1][first][x] == x and twice[2][first][x] == first
               and twice[1][second][x] == second and twice[2][second][x] == x
               for x in range(second + 1))

    # Basic laws survive even when mixed absorption fails. The old witness
    # remains in the extension, and the new join form detects it as well.
    negative = (MIXED_JOIN, MIXED_OPERATIONS[0], MIXED_OPERATIONS[2])
    totals.update(audit_candidate(unitize(negative), mixed=False))
    for add, f, g in (negative, unitize(negative)):
        x, y, z = 0, 1, 5
        assert f[x][g[y][f[y][z]]] != f[x][g[y][f[x][f[y][z]]]]
        assert add[f[x][y]][f[x][g[y][z]]] != add[f[x][y]][f[x][g[y][f[x][z]]]]
    print(f'Candidate unitization: {len(models)} source models and {triples} '
          f'join-absorption triples; {len(pairs)} distinct ordered two-choice '
          'reducts unitized. All intermediate bounds and the full candidate '
          'passed, including the double unitization of the 24-state model: '
          + ', '.join(f'{value} {key}' for key, value in sorted(totals.items()))
          + '. The six-state failure survives in the old copy and is also '
            'detected by the new absorption form. Completeness is not asserted.')


if __name__ == '__main__':
    check()
