"""Check the mixed-choice meet proved from Gamma and mixed absorption.

The proof in the paper is for arbitrary algebras. These finite checks
verify the greatest-lower-bound assertion, its proof inequalities, and
preservation by the selected choice translations. They do not assume
that the join order is a lattice or that the algebra has a reset unit.
"""

import json
from itertools import permutations, product
from pathlib import Path

from core_basis import marker_join, marker_own


def check_model(add, operations):
    carrier = range(len(add))
    lower = [{z for z in carrier if add[z][x] == x} for x in carrier]
    intervals = common_bounds = translations = mixed = 0
    for i, j in permutations(range(len(operations)), 2):
        f, g = operations[i], operations[j]
        for q, r in product(carrier, repeat=2):
            if not (q in lower[r] and f[q][r] == r and g[q][r] == q):
                continue
            for a in carrier:
                v, p = f[a][q], f[a][r]
                bound = add[a][v]
                # This is the single mixed-absorption step in the proof.
                assert f[a][g[q][p]] == v
                assert lower[v] == lower[p] & lower[bound]
                intervals += 1
                for z in lower[p] & lower[bound]:
                    first, second = f[z][v], f[a][g[z][q]]
                    assert first in lower[v] and second in lower[v]
                    assert add[f[a][z]][v] == add[first][second]
                    assert z in lower[add[f[z][a]][first]]
                    common_bounds += 1
                for b in carrier:
                    value = f[b][v]
                    left, right = f[b][p], f[b][bound]
                    assert lower[value] == lower[left] & lower[right]
                    assert right == add[f[b][a]][value]
                    translations += 1
        for a, x, y in product(carrier, repeat=3):
            q, r = g[x][y], add[x][y]
            assert q in lower[r] and f[q][r] == r and g[q][r] == q
            v = f[a][q]
            assert lower[v] == lower[add[f[a][x]][f[a][y]]] & lower[add[a][v]]
            mixed += 1
    return intervals, common_bounds, translations, mixed


def check():
    models = []
    data = Path(__file__).with_name('data')
    for name in ('small', 'six', 'seven', 'eight'):
        models.extend(json.loads((data / f'core-{name}-models.json').read_text()))
    for owners in (3, 4):
        values = list(range(1, 1 << owners))
        index = {x: i for i, x in enumerate(values)}
        add = [[index[x | y] for y in values] for x in values]
        operations = [
            [[index[1 << i if 1 << i in (x, y) else x | y]
              for y in values] for x in values]
            for i in range(owners)
        ]
        models.append({'join': add, 'operations': operations})
    # The general deduction does not need owner exhaustion: test D_K too.
    for owners in range(3, 7):
        values = range(owners + 2)
        models.append({
            'join': [[marker_join(owners, x, y) for y in values] for x in values],
            'operations': [
                [[marker_own(owners, i, x, y) for y in values] for x in values]
                for i in range(owners)
            ],
        })
    totals = [0, 0, 0, 0]
    for model in models:
        for i, count in enumerate(check_model(model['join'], model['operations'])):
            totals[i] += count
    intervals, bounds, translations, mixed = totals
    print(f'Mixed meets: {len(models)} models, {intervals} interval instances, '
          f'{bounds} common-lower-bound proof checks, {translations} selected '
          f'translations, and {mixed} mixed-choice instances passed.')


if __name__ == '__main__':
    check()
