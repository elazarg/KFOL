"""Certify failure of unrestricted word-upper meets in a core algebra.

A five-variable term has value 13, but the meet of ALL universally valid
word-join upper bounds is 16. A 91-pair invariant covers every word length
and arbitrary additional parameter variables. Two explicit upper terms
give the exact meet. The proof needs no search over native term functions.
"""

import json
from itertools import product
from pathlib import Path

from core_basis import marker_join, marker_own


def target(operations, values):
    add, f, g = operations
    a, b, c, d, e = values
    return add[d][f[g[a][c]][g[e][f[a][b]]]]


def uppers(operations, values):
    add, f, g = operations
    a, b, c, d, e = values
    left, right = g[a][c], g[e][f[a][b]]
    u = add[d][add[f[a][right]][f[c][right]]]
    v = add[d][add[f[e][left]][f[b][f[a][left]]]]
    return u, v


def check():
    data = Path(__file__).with_name('data')
    old = json.loads((data / 'core-owned-unit-depth-countermodel.json').read_text())
    add, f, g = operations = [old['join'], *old['operations'][:2]]
    assert old['operations'][2] == add
    carrier = range(24)
    assert len(add) == 24
    native = [
        [[marker_join(2, x, y) for y in range(4)] for x in range(4)],
        *[[[marker_own(2, i, x, y) for y in range(4)] for x in range(4)]
          for i in range(2)],
    ]

    # Check core membership directly, independently of the old model's audits.
    source = {tuple(x): a for x, a in zip(old['source'], old['map'])}
    assert set(source.values()) == set(carrier)
    assert all(len(x) == 6 and all(a in range(4) for a in x) for x in source)
    membership_checks = 0
    for h, operation in enumerate(operations):
        for x, y in product(source, repeat=2):
            z = tuple(native[h][a][b] for a, b in zip(x, y))
            assert z in source
            assert source[z] == operation[source[x]][source[y]]
            membership_checks += 1

    valuation = (3, 5, 6, 12, 20)
    # Native alpha=0, beta=1, n=2, p=3.
    observation = (1, 3, 0, 1, 0)
    assert target(operations, valuation) == 13
    assert target(native, observation) == 3
    assert {x for x in carrier if add[x][13] == 13} == {1, 12, 13}
    strict_uppers = {x for x in carrier if x != 13 and add[13][x] == x}
    assert strict_uppers == {9, 11, 14, 16}
    assert all(add[16][x] == x for x in strict_uppers)
    assert add[13][16] == 16 and 13 != 16

    excluded = {(0, 12), (2, 12), (3, 1), (3, 12), (3, 13)}
    relation = set(product(range(4), carrier)) - excluded
    assert len(relation) == 91
    generators = set(zip(observation, valuation))
    # Any extra variable, at ANY actual value, can use this native value.
    parameters = {(1 if a == 12 else 0, a) for a in carrier}
    coefficients = generators | parameters
    assert coefficients <= relation
    translation_checks = 0
    for h, operation in enumerate(operations):
        for (s, a), (t, b) in product(coefficients, relation):
            assert (native[h][s][t], operation[a][b]) in relation
            translation_checks += 1
    for (s, a), (t, b) in product(relation, repeat=2):
        assert (native[0][s][t], add[a][b]) in relation
    assert (3, 13) not in relation

    # Universal inequalities also follow from choice <= join and distribution.
    assert uppers(operations, valuation) == (14, 9)
    common_lower = {x for x in carrier if add[x][14] == 14 and add[x][9] == 9}
    assert common_lower == {x for x in carrier if add[x][16] == 16}
    for values in product(range(4), repeat=5):
        q = target(native, values)
        assert all(native[0][q][u] == u for u in uppers(native, values))

    print(f'Unrestricted upper-meet obstruction: {len(source)} source tuples, '
          f'{membership_checks} HSP comparisons, 24 quotient elements; '
          f'{translation_checks} translation checks and {len(relation) ** 2} '
          'joins certify the 91-pair invariant, including arbitrary extra '
          'parameters. The five-variable target is 13, while all valid '
          'word-join upper bounds have greatest lower bound 16.')


if __name__ == '__main__':
    check()
