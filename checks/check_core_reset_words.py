"""Audit word reduction after a reset at a common parameter bound.

The appendix proves the result for arbitrary word length. This audit closes
finite transformation monoids and checks every product, including the
intertwining that transfers the reduction to the original translations.
"""

from collections import Counter
from itertools import permutations

from check_core_alternating_translations import compose
from check_core_owned_reset import test_models


def band_audit(generators, n):
    identity = tuple(range(n))
    generators = tuple(set(generators))
    words = {identity: ()}
    maps = [identity]
    transitions = 0
    for P in maps:
        word = words[P]
        for k, L in enumerate(generators):
            Q = compose(P, L)
            # The last occurrence can be deleted if its letter occurred
            # earlier, even when other letters intervene.
            if k in word:
                assert Q == P
            if Q not in words:
                words[Q] = word + (k,)
                maps.append(Q)
            transitions += 1
    products = 0
    for P in maps:
        assert compose(P, P) == P
        for Q in maps:
            PQ = compose(P, Q)
            assert PQ in words and compose(PQ, P) == PQ
            products += 1
    return maps, transitions, products


def audit(add, operations):
    n = len(add)
    counts = Counter()
    largest = 0
    for f, g in permutations(operations, 2):
        for t in range(n):
            R = tuple(f[z][g[z][t]] for z in range(n))
            below = [a for a in range(n) if add[a][t] == t]
            fixed = [a for a in below if R[a] == a]
            assert {R[a] for a in below} == set(fixed)
            assert all(add[a][t] == t and R[a] == a for a in fixed)
            generators = [tuple(h[a]) for h in (f, g) for a in fixed]
            maps, transitions, products = band_audit(generators, n)
            largest = max(largest, len(maps))
            counts.update(monoids=1, elements=len(maps),
                          transitions=transitions, products=products)
            for a in below:
                for h in (f, g):
                    L, normalized = tuple(h[a]), tuple(h[R[a]])
                    assert compose(R, L) == compose(normalized, R)
                    counts['intertwinings'] += 1
            observed = {compose(P, R) for P in maps}
            assert R in observed
            for U in observed:
                assert compose(U, R) == compose(R, U) == U
                assert compose(U, U) == U
                for V in observed:
                    UV = compose(U, V)
                    assert UV in observed and compose(UV, U) == UV
                    counts['reset_products'] += 1
            counts['reset_elements'] += len(observed)
    return counts, largest


def check():
    models = test_models()
    counts = Counter()
    largest = 0
    for add, operations in models:
        result, size = audit(add, operations)
        counts.update(result)
        largest = max(largest, size)
    print(f'Reset word reduction: {len(models)} models; '
          + ', '.join(f'{value} {key}' for key, value in sorted(counts.items()))
          + f'; largest coefficient monoid {largest}. '
          'All transformation monoids were closed completely. '
          'Unrestricted word length is covered by the written induction; '
          'removing the reset is not asserted.')


if __name__ == '__main__':
    check()
