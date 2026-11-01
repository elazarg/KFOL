"""Independent finite checks of the core arity obstruction and binary forms.

The generic local-model and arbitrary-term arguments are written proofs in
appendix-core-basis.tex. No bounded term search is used to justify them.
"""

from itertools import combinations, product

from core_basis import (binary_product, binary_profiles, binary_term,
                        binary_value, deletion_quotient, exhaustion_identity,
                        marker_join, marker_own)
from fragments import denote
from structure import own


def check_quotients():
    comparisons = local_sets = 0
    for count in range(3, 7):
        values = range(1, 1 << count)
        carrier = set(range(count + 2))
        for omitted in (*range(count), count + 1):
            q = lambda x: deletion_quotient(count, omitted, x)
            image = {q(x) for x in values}
            assert image == carrier - {omitted}
            for owner, x, y in product(range(count), values, values):
                assert q(own(owner, x, y)) == marker_own(count, owner, q(x), q(y))
                comparisons += 1
        # Every <=K-element set of generators lies in one of these images.
        for size in range(1, count + 1):
            for generators in combinations(carrier, size):
                omitted = next(e for e in (*range(count), count + 1)
                               if e not in generators)
                image = carrier - {omitted}
                assert set(generators) <= image
                assert all(marker_own(count, i, x, y) in image
                           for i, x, y in product(range(count), image, image))
                local_sets += 1
        # Union is the same derived core term in the countermodel.
        for a, b, c in product(range(count), repeat=3):
            if len({a, b, c}) != 3:
                continue
            for x, y in product(carrier, repeat=2):
                assert marker_own(count, c, marker_own(count, a, x, y),
                                  marker_own(count, b, x, y)) == marker_join(count, x, y)
        high, low = count + 1, count
        summands = [marker_own(count, i, high, i) for i in range(count)]
        cover = summands[0]
        for value in summands[1:]:
            cover = marker_join(count, cover, value)
        assert cover == low
        assert marker_join(count, high, cover) == high != low
        # Each owner's own membership survives its choice, at all native pairs.
        for i, x, y in product(range(count), values, values):
            assert (own(i, x, y) & (1 << i)) == ((x | y) & (1 << i))
    # Direct evaluation of the four-variable equation, independent of that proof.
    left, right = exhaustion_identity(3)
    for valuation in product(range(1, 8), repeat=4):
        assert denote(left, valuation) == denote(right, valuation)
    return comparisons, local_sets


def check_binary():
    counts = []
    comparisons = 0
    for count in (3, 4, 5):
        profiles = binary_profiles(count)
        assert len(profiles) == len(set(profiles)) == (1 << (count + 1)) + count + 1
        valuations = tuple(product(range(1, 1 << count), repeat=2))
        functions = [tuple(binary_value(p, x, y) for x, y in valuations)
                     for p in profiles]
        assert len(set(functions)) == len(profiles)
        lookup = dict(zip(profiles, functions))
        for p, function in zip(profiles, functions):
            term = binary_term(count, p)
            assert tuple(denote(term, v) for v in valuations) == function
        for i, p, q in product(range(count), profiles, profiles):
            result = binary_product(i, p, q)
            assert result in lookup
            native = tuple(own(i, x, y) for x, y in zip(lookup[p], lookup[q]))
            assert native == lookup[result]
            comparisons += 1
        # Actual closure from the two projections reaches every displayed form.
        generated = set(profiles[:2])
        while True:
            enlarged = generated | {binary_product(i, p, q)
                                   for i, p, q in product(range(count), generated, generated)}
            if enlarged == generated:
                break
            generated = enlarged
        assert generated == set(profiles)
        counts.append(len(profiles))
    return counts, comparisons


if __name__ == '__main__':
    maps, local = check_quotients()
    sizes, products = check_binary()
    print(f'Core obstruction: {maps} quotient comparisons and {local} local '
          'generator sets at K=3..6; owner-exhaustion failures passed. '
          f'Binary free algebras: {sizes} elements at K=3,4,5; '
          f'{products} products checked on every native valuation.')
