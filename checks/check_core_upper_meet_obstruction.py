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
from core_two_owner_unitization import unitize


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

    # The first owned unit is already present. Adjoin the opposite unit.
    assert source[(1,) * 6] == 12
    for a in carrier:
        assert f[12][a] == a and g[12][a] == 12
    extended = unitize(operations, unit_owner=1)
    reference = unitize(native, unit_owner=1)
    aj, af, ag = extended
    nj, nf, ng = reference
    for a in range(49):
        assert af[12][a] == a and ag[12][a] == 12
        assert ag[48][a] == a and af[48][a] == 48
    # A pointed embedding of the nine-element reference in (D,beta,alpha)^3.
    embedding = [(1, 0, 3), (1, 1, 1), (1, 2, 3), (1, 3, 3),
                 (2, 0, 3), (2, 2, 2), (2, 2, 3), (2, 3, 3), (0, 0, 0)]
    assert len(set(embedding)) == 9
    assert embedding[1] == (1,) * 3 and embedding[8] == (0,) * 3
    for h, operation in enumerate(reference):
        for a, b in product(range(9), repeat=2):
            assert embedding[operation[a][b]] == tuple(
                native[h][x][y] for x, y in zip(embedding[a], embedding[b]))
    lifted_source = dict(source)
    lifted_source.update({tuple(x + 4 for x in row): a + 24
                          for row, a in source.items()})
    lifted_source[(8,) * 6] = 48
    assert set(lifted_source.values()) == set(range(49))
    for h, operation in enumerate(extended):
        for x, y in product(lifted_source, repeat=2):
            z = tuple(reference[h][a][b] for a, b in zip(x, y))
            assert z in lifted_source
            assert lifted_source[z] == operation[lifted_source[x]][lifted_source[y]]

    lifted_relation = relation | {(s + 4, a + 24) for s, a in relation} | {(8, 48)}
    lifted_coefficients = coefficients | {
        (s + 4, a + 24) for s, a in parameters} | {(8, 48)}
    assert len(lifted_relation) == 183
    assert len({a for s, a in lifted_coefficients}) == 49
    assert (1, 12) in lifted_coefficients and (8, 48) in lifted_coefficients
    assert (nj[1][8], aj[12][48]) in lifted_coefficients  # the named join
    for h, operation in enumerate(extended):
        for (s, a), (t, b) in product(lifted_coefficients, lifted_relation):
            assert (reference[h][s][t], operation[a][b]) in lifted_relation
    for (s, a), (t, b) in product(lifted_relation, repeat=2):
        assert (nj[s][t], aj[a][b]) in lifted_relation
    assert target(extended, valuation) == 13 and target(reference, observation) == 3
    assert all(aj[16][a] == a for s, a in lifted_relation
               if nj[3][s] == s and aj[13][a] == a)
    assert uppers(extended, valuation) == (14, 9)
    assert {a for a in range(49) if aj[a][14] == 14 and aj[a][9] == 9} == {
        a for a in range(49) if aj[a][16] == 16}
    print(f'Opposite-unit obstruction: {len(lifted_source)} source tuples, '
          f'{3 * len(lifted_source) ** 2} quotient comparisons and 243 '
          'embedding comparisons certify pointed membership; '
          f'{3 * len(lifted_coefficients) * len(lifted_relation)} translations '
          f'and {len(lifted_relation) ** 2} joins certify the lifted invariant. '
          'The same strict meet holds with four variables, both named units, '
          'their named join, and arbitrary additional parameters.')


if __name__ == '__main__':
    check()
