"""Audit the ladder HSP maps, monoliths, and critical-depth lower bound.

The product factors are evaluated as actual three-owner winner sets. The
congruence check generates every principal congruence independently of the
written proof. Finite checks supplement, rather than replace, that proof.
"""

from collections import deque
from itertools import combinations, product

from core_ladders import ladder_certificate, ladder_join, ladder_own, level


def own(owner, x, y):
    atom = 1 << owner
    return atom if x == atom or y == atom else x | y


def pair_images(operations, pair):
    """All distinct images under one basic translation."""
    for table in operations:
        for coefficient in range(len(table)):
            a, b = sorted((table[pair[0]][coefficient], table[pair[1]][coefficient]))
            if a != b:
                yield a, b


def principal_congruence(operations, pair):
    reached = {pair}
    pending = deque([pair])
    while pending:
        for target in pair_images(operations, pending.popleft()):
            if target not in reached:
                reached.add(target)
                pending.append(target)
    parent = list(range(len(operations[0])))

    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for x, y in reached:
        parent[root(x)] = root(y)
    return {p for p in combinations(range(len(parent)), 2) if root(p[0]) == root(p[1])}


def check():
    source_pairs = principal_pairs = 0
    source_sizes = []
    for r in range(1, 7):
        source, images = ladder_certificate(r)
        mapping = dict(zip(source, images))
        assert len(mapping) == len(source)
        assert set(images) == set(range(2 * r + 1))
        factors = [((1 << (j % 2)), 3, 7) for j in range(r)]
        inverse = [{value: k for k, value in enumerate(factor)} for factor in factors]
        for owner, v, w in product(range(3), source, source):
            result = tuple(inverse[j][own(owner, factors[j][x], factors[j][y])]
                           for j, (x, y) in enumerate(zip(v, w)))
            assert result in mapping, (r, owner, v, w)
            assert mapping[result] == ladder_own(r, owner, mapping[v], mapping[w])
            source_pairs += 1
        source_sizes.append(len(source))

    for r in range(1, 11):
        carrier = range(2 * r + 1)
        operations = [[[ladder_own(r, i, x, y) for y in carrier] for x in carrier]
                      for i in range(3)]
        join = [[ladder_join(r, x, y) for y in carrier] for x in carrier]
        assert operations[2] == join
        for x, y in product(carrier, repeat=2):
            assert operations[2][operations[0][x][y]][operations[1][x][y]] == join[x][y]
        # Compatibility of the equivalence with sole nonsingleton block {c0,c1}.
        monolith = (r, r + 1)
        assert set(pair_images(operations, monolith)) <= {monolith}
        for pair in combinations(carrier, 2):
            assert monolith in principal_congruence(operations, pair), (r, pair)
            principal_pairs += 1
        # Every basic translation lowers level by at most one, including join.
        for table, x, y in product(operations, carrier, carrier):
            assert level(r, table[x][y]) >= level(r, x) - 1
        if r >= 2:
            # No short translated edge touches c0, so no chain can reach it.
            reached = {(2 * r - 1, 2 * r)}
            for depth in range(r - 1):
                assert all(r not in edge for edge in reached), (r, depth)
                reached |= {edge for pair in tuple(reached)
                            for edge in pair_images(operations, pair)}
    print(f'Core ladders: HSP maps at lengths 1..6 (source sizes {source_sizes}), '
          f'{source_pairs} source pair/owner checks; monoliths and level bound '
          f'at lengths 1..10, {principal_pairs} principal congruences.')


if __name__ == '__main__':
    check()
