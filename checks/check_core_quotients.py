"""Exact quotient and monolith certificates for the unrestricted core.

The Q_K construction and its generic proof are in appendix-core-basis.tex.
CoreQuotients.lean transfers all core identities to Q_3 and proves its
monolith is contained in every nonidentity compatible equivalence.
"""

from itertools import combinations, permutations, product

from core_basis import marker_join, marker_own, quotient_own, quotient_source
from probe_residual import merge_congruence, root


def check():
    comparisons = forced_pairs = 0
    for count in range(3, 9):
        source = quotient_source(count)
        values = range(count + 2)
        assert len(source) == count + 5
        assert set(source.values()) == set(values)
        assert all(x != 1 and y != 0 for x, y in source)
        for owner, x, y in product(range(count), source, source):
            z = tuple(marker_own(count, owner, a, b) for a, b in zip(x, y))
            assert z in source
            assert source[z] == quotient_own(count, owner, source[x], source[y])
            comparisons += 1
        for x, y in product(source, repeat=2):
            z = tuple(marker_join(count, a, b) for a, b in zip(x, y))
            assert z in source
            assert source[z] == marker_join(count, source[x], source[y])
        for a, b, c in permutations(range(count), 3):
            for x, y in product(values, repeat=2):
                assert quotient_own(count, c, quotient_own(count, a, x, y),
                                    quotient_own(count, b, x, y)) == marker_join(count, x, y)
        # All owners differ from union; owner 0 is already nonconservative.
        for owner in range(count):
            assert quotient_own(count, owner, owner, count) == owner
            assert marker_join(count, owner, count) == count != owner
        assert quotient_own(count, 0, 1, 2) == count not in (1, 2)
        def reset(x, y):
            value = marker_join(count, x, y)
            for owner in range(count):
                value = quotient_own(count, owner, value, y)
            return value

        assert reset(0, count + 1) == reset(count + 1, 0)
        assert reset(count + 1, count) == reset(count, count + 1)
        assert reset(0, count) != reset(count, 0)

        # The congruence with sole nontrivial class {a_0,n}.
        collapse = lambda x: count if x == 0 else x
        translations = [tuple(quotient_own(count, owner, x, y) for x in values)
                        for owner in range(count) for y in values]
        for operation in translations:
            assert collapse(operation[0]) == collapse(operation[count])
        # Every unequal pair generates a congruence containing that class.
        for x, y in combinations(values, 2):
            congruence = merge_congruence(list(values), x, y, translations)
            assert root(congruence, 0) == root(congruence, count)
            forced_pairs += 1
    print(f'Core quotients Q_K at K=3..8: {comparisons} product/map comparisons; '
          f'{forced_pairs} principal congruences contain the monolith. '
          'Derived union, surjectivity, and every-owner witnesses passed.')


if __name__ == '__main__':
    check()
