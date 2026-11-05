"""Audit word reduction for every choice and join, with arbitrary parameters.

The written proof uses global sandwich reset, the quotient at a common
bound, and input erasure. These finite checks audit the sandwich proof
and close the complete transformation monoid in each supplied model.
"""

from collections import Counter
from itertools import permutations, product

from check_core_alternating_translations import compose
from check_core_owned_reset import test_models
from core_context_words import normalize


def global_resets(add, operations):
    result = []
    for a in range(len(add)):
        row = []
        for z in range(len(add)):
            value = add[a][z]
            for h in operations:
                value = h[z][value]
            row.append(value)
        result.append(tuple(row))
    return result


def audit_sandwich(add, operations, resets):
    n = len(add)
    tables = (*operations, add)
    counts = Counter()
    for f, g in product(tables, repeat=2):
        for a, b, z in product(range(n), repeat=3):
            v = f[a][g[b][z]]
            w = f[a][g[b][f[a][z]]]
            assert resets[b][v] == w
            counts['sandwiches'] += 1
    for f, g, h in permutations(operations, 3):
        for a, b, z in product(range(n), repeat=3):
            v = f[a][g[b][z]]
            w = f[a][g[b][f[a][z]]]
            u, r = f[z][g[z][a]], f[z][h[z][a]]
            assert add[u][r] == add[z][f[a][z]]
            assert f[a][g[b][u]] == v
            lr = f[a][g[b][r]]
            assert add[v][lr] == w
            assert r == h[z][f[a][z]]
            assert add[lr][h[v][w]] == h[v][w]
            assert h[v][w] == w
            counts['third_choice_steps'] += 1
    return counts


def audit_monoid(add, operations, resets):
    n = len(add)
    identity = tuple(range(n))
    generators = {(h, a): tuple(table[a])
                  for h, table in enumerate((*operations, add))
                  for a in range(n)}

    def evaluate(word):
        value = identity
        for letter in word:
            value = compose(value, generators[letter])
        return value

    maps = [identity]
    representatives = {identity: ()}
    counts = Counter(monoids=1)
    for P in maps:
        word = representatives[P]
        square = compose(P, P)
        assert compose(square, P) == square
        counts['elements'] += 1
        if word:
            t = word[0][1]
            for _, a in word[1:]:
                t = add[t][a]
            # Check every upper bound of this representative's coefficients.
            for b in range(n):
                if add[t][b] != b:
                    continue
                R = resets[b]
                RP = compose(R, P)
                distinct = tuple(dict.fromkeys(word))
                assert RP == compose(R, evaluate(distinct))
                assert compose(RP, R) == compose(RP, RP) == RP
                counts['bounded_resets'] += 1
            assert compose(P, resets[t]) == P
            counts['input_resets'] += 1
        for letter, L in generators.items():
            Q = compose(P, L)
            extended = word + (letter,)
            normal = normalize(extended)
            assert evaluate(normal) == Q
            assert normalize(normal) == normal
            assert set(normal) == set(extended)
            m = len(set(extended))
            assert len(normal) <= m * (m + 1) // 2
            counts['transitions'] += 1
            if Q not in representatives:
                representatives[Q] = normal
                maps.append(Q)
    return counts, len(maps)


def check():
    counts = Counter()
    largest = 0
    models = test_models()
    for add, operations in models:
        resets = global_resets(add, operations)
        counts.update(audit_sandwich(add, operations, resets))
        result, size = audit_monoid(add, operations, resets)
        counts.update(result)
        largest = max(largest, size)
    print(f'Full-signature translation words: {len(models)} models; '
          + ', '.join(f'{value} {key}' for key, value in sorted(counts.items()))
          + f'; largest monoid {largest}. '
          'Every monoid was closed completely. The written proof covers '
          'arbitrary word length and arbitrary algebras; branching terms '
          'and full finite basability are not settled by this result.')


if __name__ == '__main__':
    check()
