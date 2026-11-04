"""Audit reset expansion and selected-choice preservation at owned units.

The arbitrary-algebra derivation is in appendix-core-basis.tex. These checks
exercise its intermediate absorption and erasure equations on choice images,
including D_K, whose failure of exhaustion puts it outside the core variety.
"""

import json
from functools import reduce
from itertools import product
from pathlib import Path

from check_core_atomic_basis import operation_tables
from core_basis import marker_join, marker_own


def check_model(join, operations):
    carrier = range(len(join))
    owners = len(operations)
    add, ops, reset = operation_tables(
        carrier, lambda x, y: join[x][y],
        lambda i, x, y: operations[i][x][y], owners)
    counts = [0] * 5
    for u in carrier:
        for i, f in enumerate(ops):
            image = sorted({f[u, x] for x in carrier})
            assert all(f[u, x] == x for x in image)
            assert all(h[x, y] in image for h in [add] + ops
                       for x, y in product(image, repeat=2))
            counts[0] += 1
            others = [j for j in range(owners) if j != i]
            h_maps = {}
            for j in others:
                h_map = {}
                for z in image:
                    value = z
                    for k in others:
                        if k != j:
                            value = ops[k][u, value]
                    h_map[z] = value
                    assert add[u, value] == value
                h_maps[j] = h_map
                for z in image:
                    assert h_map[add[u, z]] == h_map[z]
            for v in image:
                if add[u, v] == v:
                    assert reduce(lambda a, b: add[a, b],
                                  (h_maps[j][v] for j in others)) == v
            for x in image:
                for j in others:
                    l_map = {z: f[x, h_maps[j][z]] for z in image}
                    for z in image:
                        assert l_map[f[x, z]] == l_map[z]
                        counts[1] += 1
                        for k in others:
                            if k != j:
                                assert l_map[ops[k][x, z]] == l_map[add[x, z]]
                                counts[2] += 1
            for c in image:
                p_maps = {j: {x: h_maps[j][ops[j][c, x]] for x in image}
                          for j in others}
                r_maps = {j: {x: f[x, p_maps[j][x]] for x in image}
                          for j in others}
                for x in image:
                    assert reset[c, x] == reduce(lambda a, b: add[a, b],
                                                (r_maps[j][x] for j in others))
                    counts[3] += 1
                for x, y in product(image, repeat=2):
                    v = f[x, y]
                    for j in others:
                        p, r = p_maps[j], r_maps[j]
                        assert add[p[v], f[p[x], p[y]]] == f[p[x], p[y]]
                        assert add[r[v], f[r[x], r[y]]] == f[r[x], r[y]]
                    w = f[reset[c, x], reset[c, y]]
                    assert add[w, reset[c, v]] == reset[c, v]
                    assert reset[c, v] == w
                    counts[4] += 1
    return counts


def check():
    models = []
    for owners in range(3, 6):
        native = tuple(range(1, 1 << owners))
        index = {x: i for i, x in enumerate(native)}
        join = [[index[x | y] for y in native] for x in native]
        ops = [[[index[1 << i if 1 << i in (x, y) else x | y]
                 for y in native] for x in native] for i in range(owners)]
        models.append((join, ops))
    data = Path(__file__).with_name('data')
    for name in ('small', 'six', 'seven', 'eight'):
        for model in json.loads((data / f'core-{name}-models.json').read_text()):
            models.append((model['join'], model['operations']))
    for name in ('core-owned-unit-observer-countermodel',
                 'core-owned-unit-depth-countermodel'):
        model = json.loads((data / (name + '.json')).read_text())
        models.append((model['join'], model['operations']))
    for owners in range(3, 7):
        carrier = range(owners + 2)
        join = [[marker_join(owners, x, y) for y in carrier] for x in carrier]
        ops = [[[marker_own(owners, i, x, y) for y in carrier] for x in carrier]
               for i in range(owners)]
        models.append((join, ops))
    totals = [0] * 5
    for join, ops in models:
        totals = [a + b for a, b in zip(totals, check_model(join, ops))]
    print(f'Owned-unit reset expansion: {len(models)} models, {totals[0]} '
          f'choice images; {totals[1]} absorption and {totals[2]} erasure '
          f'checks, {totals[3]} reset expansions, and {totals[4]} selected '
          'homomorphism triples, including both inequality directions. '
          'Filter covers, preservation of join with the unit by each '
          'partial observer, and the two intermediate product inequalities '
          'also passed.')


if __name__ == '__main__':
    check()
