"""Native soundness checks for the dissemilattice fragment and core embedding.

The classical generation and irreducible-family results are external theorems,
identified in appendix-core-basis.tex. These finite checks do not prove them.
"""

from itertools import permutations, product

from structure import own


def add(x, y):
    return max(x, y)


def mul(x, y):
    return 0 if x == 0 or y == 0 else max(x, y)


def check():
    triples = embeddings = 0
    for count in (3, 4, 5):
        values = range(1, 1 << count)
        for owner in range(count):
            for x in values:
                assert own(owner, x, x) == x
                assert x | x == x
            for x, y in product(values, repeat=2):
                assert own(owner, x, y) == own(owner, y, x)
                assert x | y == y | x
            for x, y, z in product(values, repeat=3):
                assert own(owner, own(owner, x, y), z) == own(owner, x, own(owner, y, z))
                assert (x | y) | z == x | (y | z)
                assert own(owner, x, y | z) == own(owner, x, y) | own(owner, x, z)
                triples += 1

        for a, b, c in permutations(range(count), 3):
            carrier = (1 << a, (1 << a) | (1 << b),
                       (1 << a) | (1 << b) | (1 << c))
            assert len(set(carrier)) == 3
            for x, y in product(range(3), repeat=2):
                assert carrier[add(x, y)] == carrier[x] | carrier[y]
                for owner in range(count):
                    operation = mul if owner == a else add
                    assert carrier[operation(x, y)] == own(owner, carrier[x], carrier[y])
                    embeddings += 1
            bb, nn, pp = carrier
            assert nn | own(a, bb, pp) == nn
            assert own(a, nn | bb, nn | pp) == pp
            assert nn != pp

    print(f'Core dissemilattice: seven sound laws on {triples} native triples; '
          f'{embeddings} embedding comparisons at K=3,4,5; '
          'reverse distributivity counterexamples passed.')


if __name__ == '__main__':
    check()
