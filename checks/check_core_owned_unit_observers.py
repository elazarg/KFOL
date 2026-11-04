"""Verify the owned-unit counterexample to shallow observation.

Membership is certified by explicit subalgebra quotients of powers of
D_{0,1}. The check uses no model finder or theorem prover. It verifies the
failed observed meet, failure of congruence compatibility, the monoliths,
and the exact observation depths two and three in the two examples.
"""

import json
from itertools import combinations, product
from pathlib import Path

from core_basis import marker_join, marker_own
from probe_residual import merge_congruence, root


def check():
    path = Path(__file__).with_name('data') / 'core-owned-unit-observer-countermodel.json'
    model = json.loads(path.read_text())
    add = model['join']
    f, g, unused = model['operations']
    assert unused == add
    carrier = range(len(add))
    assert len(add) == 10
    source = [tuple(x) for x in model['source']]
    quotient = dict(zip(source, model['map']))
    assert len(source) == len(quotient) == len(model['map']) == 18
    assert set(quotient.values()) == set(carrier)
    assert all(len(x) == 3 and all(0 <= a < 4 for a in x) for x in source)
    operations = [add, f, g]
    source_operations = [
        lambda x, y: marker_join(2, x, y),
        lambda x, y: marker_own(2, 0, x, y),
        lambda x, y: marker_own(2, 1, x, y),
    ]
    comparisons = 0
    for target, operation in zip(operations, source_operations):
        for x, y in product(source, repeat=2):
            z = tuple(operation(a, b) for a, b in zip(x, y))
            assert z in quotient
            assert quotient[z] == target[quotient[x]][quotient[y]]
            comparisons += 1
    c = quotient[1, 1, 1]
    assert c == model['root'] == 8
    assert all(f[c][x] == x and g[c][x] == c for x in carrier)

    lower = [{z for z in carrier if add[z][x] == x} for x in carrier]
    beta = add[c]
    a, x, y = 1, 2, 3
    value = f[a][g[x][y]]
    left = add[f[a][x]][f[a][y]]
    right = add[a][value]
    assert (value, left, right) == (0, 3, 1)
    assert lower[value] == lower[left] & lower[right]
    assert (beta[value], beta[left], beta[right]) == (9, 5, 7)
    assert lower[beta[left]] & lower[beta[right]] == lower[7]
    assert 9 != 7 and 9 in lower[7]

    signatures = [tuple(beta[f[a][x]] for a in carrier) for x in carrier]
    assert signatures[3] == signatures[5] == (5,) * 10
    assert (g[2][3], g[2][5]) == (2, 4)
    assert (beta[f[1][2]], beta[f[1][4]]) == (9, 7)
    assert signatures[g[2][3]] != signatures[g[2][5]]

    translations = [tuple(h[a][x] for x in carrier)
                    for h, a in product(operations, carrier)]
    protected = tuple(model['protected'])
    assert set(protected) == {7, 9}
    monolith = merge_congruence(list(carrier), *protected, translations)
    assert {frozenset(x for x in carrier if root(monolith, x) == root(monolith, a))
            for a in carrier} == {frozenset({7, 9}),
                                  *(frozenset({x}) for x in carrier if x not in (7, 9))}
    for a, b in combinations(carrier, 2):
        generated = merge_congruence(list(carrier), a, b, translations)
        assert root(generated, 7) == root(generated, 9)

    # Refine by every basic translation, retaining the previous observations.
    # The first refinement equals the selected-choice signatures above;
    # join and g cannot refine beta because beta preserves those operations.
    partition = beta
    counts = [len(set(partition))]
    for _ in range(2):
        keys = [tuple([partition[x]] + [partition[t[x]] for t in translations])
                for x in carrier]
        indices = {key: i for i, key in enumerate(dict.fromkeys(keys))}
        partition = [indices[key] for key in keys]
        counts.append(len(indices))
    assert counts == [5, 9, 10]
    print(f'Owned-unit observer counterexample: {comparisons} source operation '
          'comparisons certify an 18-state subalgebra quotient of size 10; '
          'the unit, absorbing owner, failed observed meet, incompatible '
          'one-translation signatures, 45 monolith checks, and observation '
          'class counts 5, 9, 10 passed.')


def check_deeper():
    path = Path(__file__).with_name('data') / 'core-owned-unit-depth-countermodel.json'
    model = json.loads(path.read_text())
    add = model['join']
    f, g, unused = model['operations']
    assert unused == add
    carrier = range(len(add))
    assert len(add) == 24
    source = [tuple(x) for x in model['source']]
    quotient = dict(zip(source, model['map']))
    assert len(source) == len(quotient) == len(model['map']) == 108
    assert set(quotient.values()) == set(carrier)
    assert all(len(x) == 6 and all(0 <= a < 4 for a in x) for x in source)
    comparisons = 0
    for i, target in enumerate([add, f, g]):
        for x, y in product(source, repeat=2):
            z = tuple(marker_join(2, a, b) if i == 0 else marker_own(2, i - 1, a, b)
                      for a, b in zip(x, y))
            assert z in quotient
            assert quotient[z] == target[quotient[x]][quotient[y]]
            comparisons += 1
    c = quotient[(1,) * 6]
    assert c == model['root'] == 12
    assert all(f[c][x] == x and g[c][x] == c for x in carrier)

    translations = [tuple(h[a][x] for x in carrier)
                    for h, a in product([add, f, g], carrier)]
    pair = tuple(model['pair'])
    assert pair == (4, 11)
    partition = add[c]
    counts = [len(set(partition))]
    for depth in range(1, 4):
        assert partition[pair[0]] == partition[pair[1]]
        keys = [tuple([partition[x]] + [partition[t[x]] for t in translations])
                for x in carrier]
        indices = {key: i for i, key in enumerate(dict.fromkeys(keys))}
        partition = [indices[key] for key in keys]
        counts.append(len(indices))
    assert counts == model['observation_class_counts'] == [11, 17, 20, 24]
    assert partition[pair[0]] != partition[pair[1]]
    values = list(pair)
    # The word is stored from the innermost translation to the outermost.
    assert model['distinguishing_word'] == [[0, 5], [1, 20], [0, 6]]
    for i, a in model['distinguishing_word']:
        values = [model['operations'][i][a][x] for x in values]
    observed = [add[c][x] for x in values]
    assert observed == model['protected'] == [13, 16]
    for a, b in combinations(carrier, 2):
        generated = merge_congruence(list(carrier), a, b, translations)
        assert root(generated, 13) == root(generated, 16)
    print(f'Owned-unit depth-three counterexample: {comparisons} source operation '
          'comparisons certify a 108-state subalgebra quotient of size 24; '
          'the unit, absorbing owner, 276 irreducibility checks, observation '
          'class counts 11, 17, 20, 24, and the distinguishing word passed.')


if __name__ == '__main__':
    check()
    check_deeper()
