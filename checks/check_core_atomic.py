"""Singleton-collapse quotient and the explicit veto near-unanimity term.

The generic subvariety and optimal-arity arguments are written proofs.
Congruence distributivity and finite basability use Mitschke and Baker;
these computations are not a replacement for those external theorems.
"""

from itertools import product

from core_basis import atomic_image, atomic_own, veto_value
from structure import own


def check():
    maps = comparisons = 0
    for count in range(3, 7):
        values = range(1, 1 << count)
        image = lambda x: atomic_image(count, x)
        assert {image(x) for x in values} == set(range(count + 1))
        for x, y in product(values, repeat=2):
            # Equality in the quotient is exactly reset commutation in C_K.
            xy = y if y.bit_count() == 1 else x | y
            yx = x if x.bit_count() == 1 else x | y
            assert (image(x) == image(y)) == (xy == yx)
            for owner in range(count):
                assert image(own(owner, x, y)) == atomic_own(count, owner, image(x), image(y))
                maps += 1
        for x, y in product(range(count + 1), repeat=2):
            value = x if x == y else count  # Join in the flat quotient.
            for owner in range(count):
                value = atomic_own(count, owner, value, y)
            assert value == y
    for count in range(3, 9):
        operation = lambda r, x, y: atomic_own(count, r, x, y)
        for x, y, exceptional in product(range(count + 1), repeat=3):
            inputs = tuple(y if j == exceptional else x for j in range(count + 1))
            assert veto_value(count, inputs, operation) == x
            comparisons += 1
        # The same term is not near-unanimity in the original core.
        assert veto_value(count, (5,) + (3,) * count, own) == 7 != 3
        for arity in range(2, count + 1):
            # Near-unanimity would force these distinct outputs, but no
            # input column can be the common source supplied by that theorem.
            rows = [[(i + 1) % arity if j == i else i for j in range(arity)]
                    for i in range(arity)]
            assert all(any(rows[i][j] != i for i in range(arity)) for j in range(arity))
    print(f'Atomic quotient: {maps} homomorphism comparisons at K=3..6; '
          f'{comparisons} near-unanimity valuations at K=3..8; '
          'reset comparison, right projection, lower-bound valuations, '
          'and failure of near-unanimity in the original core passed.')


if __name__ == '__main__':
    check()
