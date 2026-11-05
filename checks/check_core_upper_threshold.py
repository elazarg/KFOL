"""Certify failure of upper-word interpolation at a meet-irreducible bound.

The 17-element algebra is a subquotient of the existing 24-element core
certificate. Membership is checked directly against its power of D_{0,1}.
A finite invariant relation covers words of every length, including an
extra variable naming the threshold. Two explicit word-join upper bounds
nevertheless have the target as their greatest lower bound.
"""

import json
from itertools import product
from pathlib import Path

from core_basis import marker_join, marker_own


def check():
    data = Path(__file__).with_name('data')
    old = json.loads((data / 'core-owned-unit-depth-countermodel.json').read_text())
    old_ops = [old['join'], *old['operations'][:2]]
    assert old['operations'][2] == old['join']
    subset = set(range(24)) - {0, 5, 12}
    representatives = {10: 3, 11: 4, 23: 14, 22: 18}
    quotient = {a: representatives.get(a, a) for a in subset}
    carrier = sorted(set(quotient.values()))
    assert len(subset) == 21 and len(carrier) == 17
    operations = []
    for old_op in old_ops:
        op = {}
        for a, b in product(subset, repeat=2):
            assert old_op[a][b] in subset
            key = quotient[a], quotient[b]
            value = quotient[old_op[a][b]]
            assert key not in op or op[key] == value
            op[key] = value
        operations.append(op)
    add, f, g = operations

    source = {tuple(x): quotient[a]
              for x, a in zip(old['source'], old['map']) if a in subset}
    assert set(source.values()) == set(carrier)
    assert all(len(x) == 6 and all(0 <= a < 4 for a in x) for x in source)
    membership_checks = 0
    for h, op in enumerate(operations):
        for x, y in product(source, repeat=2):
            z = tuple(marker_join(2, a, b) if h == 0
                      else marker_own(2, h - 1, a, b)
                      for a, b in zip(x, y))
            assert z in source
            assert source[z] == op[source[x], source[y]]
            membership_checks += 1

    def below(a, b):
        return add[a, b] == b

    q, m, cover = 1, 13, 16
    assert {a for a in carrier if below(a, m)} == {q, m}
    strict_upper = [a for a in carrier if a != m and below(m, a)]
    assert cover in strict_upper and all(below(cover, a) for a in strict_upper)
    assert f[g[3, 6], g[2, 20]] == q

    # Native atoms alpha=0 and beta=1; markers n=2 and p=3.
    native = [
        {(a, b): marker_join(2, a, b) for a, b in product(range(4), repeat=2)},
        *[{(a, b): marker_own(2, i, a, b)
           for a, b in product(range(4), repeat=2)} for i in range(2)],
    ]
    generators = [(1, 3), (0, 6), (1, 2), (0, 20), (0, 13)]
    relation = {(0, a) for a in carrier} | {
        (s, a) for s in (1, 2) for a in carrier if a not in (q, m)}
    assert len(relation) == 47
    assert set(generators) <= relation
    translation_checks = 0
    for h, op in enumerate(operations):
        for (s, a), (t, b) in product(generators, relation):
            assert (native[h][s, t], op[a, b]) in relation
            translation_checks += 1
    for (s, a), (t, b) in product(relation, repeat=2):
        assert (native[0][s, t], add[a, b]) in relation
    assert native[1][native[2][1, 0], native[2][1, 0]] == 1
    assert all(s == 0 for s, a in relation if below(a, m))
    assert native[0][1, 0] != 0  # beta is not below alpha.

    # These are universal upper bounds by choice <= join and distribution.
    upper_left = add[f[3, g[2, 20]], f[6, g[2, 20]]]
    upper_right = add[f[2, g[3, 6]], f[20, g[3, 6]]]
    assert (upper_left, upper_right) == (3, 2)
    assert {a for a in carrier if below(a, upper_left) and below(a, upper_right)} == {q}
    for a, b, c, d in product(range(4), repeat=4):
        nj, nf, ng = native
        value = nf[ng[a, b], ng[c, d]]
        left = nj[nf[a, ng[c, d]], nf[b, ng[c, d]]]
        right = nj[nf[c, ng[a, b]], nf[d, ng[a, b]]]
        assert nj[value, left] == left and nj[value, right] == right

    print(f'Upper-threshold obstruction: {len(source)} source tuples, '
          f'{membership_checks} HSP comparisons, 17 quotient elements; '
          f'{translation_checks} generator-translation checks and '
          f'{len(relation) ** 2} joins certify the 47-pair invariant. '
          'The threshold has a unique cover; the target fails threshold '
          'interpolation at every word depth but is the meet of two '
          'explicit depth-two upper bounds.')


if __name__ == '__main__':
    check()
