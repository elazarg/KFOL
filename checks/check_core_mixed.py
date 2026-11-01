"""Finite certificates for conservative cores and proper-owner fragments.

The arbitrary-cardinality conservative classification and fragment generation
are written proofs. CoreConservative.lean checks the structural lemma;
CoreMixed.lean checks the generic mixed law and the six-state countermodel.
These checks do not assert an unrestricted finite basis.
"""

from itertools import combinations, permutations, product

from core_basis import (MIXED_JOIN, MIXED_OPERATIONS, fragment_quotient,
                        marker_join, marker_own, mixed_absorption)
from probe_core_basis import binary_failure, evaluate, exhaustion_holds
from structure import own


def check_fragments():
    comparisons = maps = 0
    for count in (3, 4, 5):
        values = range(1, 1 << count)
        for size in range(1, count):
            for owners in combinations(range(count), size):
                images = []
                for observer in range(count):
                    q = {x: fragment_quotient(owners, observer, x) for x in values}
                    assert all((q[x] == size + 1) == bool(x & (1 << observer))
                               for x in values)
                    if observer not in owners:
                        assert set(q.values()) == set(range(size + 2))
                        if size >= 2:
                            # Expanded fragment: every unused owner is join.
                            # Restrict the source to R plus this observer.
                            allowed = sum(1 << i for i in (*owners, observer))
                            domain = [x for x in values if x & ~allowed == 0]
                            assert {q[x] for x in domain} == set(range(size + 2))
                            for owner, x, y in product(range(count), domain, domain):
                                target = (marker_own(size, owners.index(owner), q[x], q[y])
                                          if owner in owners else marker_join(size, q[x], q[y]))
                                assert q[own(owner, x, y)] == target
                                comparisons += 1
                    for x, y in product(values, repeat=2):
                        assert q[x | y] == marker_join(size, q[x], q[y])
                        for index, owner in enumerate(owners):
                            assert q[own(owner, x, y)] == marker_own(size, index, q[x], q[y])
                            comparisons += 1
                    images.append(q)
                    maps += 1
                assert len({tuple(q[x] for q in images) for x in values}) == len(values)
                # Union remains the derived core term in the expansion.
                def expanded(owner, x, y):
                    if owner in owners:
                        return marker_own(size, owners.index(owner), x, y)
                    return marker_join(size, x, y)

                for x, y in product(range(size + 2), repeat=2):
                    assert expanded(2, expanded(0, x, y), expanded(1, x, y)) == marker_join(size, x, y)
    # The raw two-choice reduct is the four-element bichain B.
    for owner, order in enumerate(((1, 2, 3, 0), (0, 2, 3, 1))):
        rank = {x: i for i, x in enumerate(order)}
        for x, y in product(range(4), repeat=2):
            assert marker_own(2, owner, x, y) == max((x, y), key=rank.get)
        assert all(marker_own(2, owner, x, y) in (0, 1)
                   for x, y in product((0, 1), repeat=2))
    assert marker_join(2, 0, 1) == 2  # Union is not a raw two-choice term.
    return maps, comparisons


def check_native():
    comparisons = 0
    for count in (3, 4, 5):
        values = range(1, 1 << count)
        for a, b in product(range(count), repeat=2):
            for x, y in product(values, repeat=2):
                if a != b:
                    assert own(a, x, y) | own(b, x, y) == x | y
                for z in values:
                    yz = own(a, y, z)
                    assert own(a, x, own(b, y, yz)) == own(a, x, own(b, y, own(a, x, yz)))
                    comparisons += 1
    return comparisons


def semilattice(table):
    values = range(len(table))
    return (all(table[x][x] == x for x in values)
            and all(table[x][y] == table[y][x] for x, y in product(values, repeat=2))
            and all(table[table[x][y]][z] == table[x][table[y][z]]
                    for x, y, z in product(values, repeat=3)))


def check_mixed_countermodel():
    add, ops = MIXED_JOIN, MIXED_OPERATIONS
    values = range(6)
    assert all(semilattice(table) for table in (add, *ops))
    for table in ops:
        assert all(table[x][add[y][z]] == add[table[x][y]][table[x][z]]
                   for x, y, z in product(values, repeat=3))
    for i, j in product(range(3), repeat=2):
        for x, y in product(values, repeat=2):
            assert ops[i][x][ops[j][x][y]] == ops[j][x][ops[i][x][y]]
            if i != j:
                assert add[ops[i][x][y]][ops[j][x][y]] == add[x][y]
    for a, b, c in permutations(range(3)):
        assert all(ops[c][ops[a][x][y]][ops[b][x][y]] == add[x][y]
                   for x, y in product(values, repeat=2))
    assert exhaustion_holds(add, ops)
    assert binary_failure(add, ops) is None
    left, right = mixed_absorption(0, 2)
    assert evaluate(left, (0, 1, 5), add, ops) == 3
    assert evaluate(right, (0, 1, 5), add, ops) == 0


def check_conservative():
    counts = []
    for size in range(2, 7):
        values = range(size)
        add = tuple(tuple(max(x, y) for y in values) for x in values)
        compatible = []
        # Conservative semilattices are exactly maxima in linear orders.
        for order in permutations(values):
            rank = {x: i for i, x in enumerate(order)}
            table = tuple(tuple(max((x, y), key=rank.get) for y in values) for x in values)
            if all(table[x][max(y, z)] == max(table[x][y], table[x][z])
                   for x, y, z in product(values, repeat=3)):
                compatible.append(table)
        for first, second in product(compatible, repeat=2):
            if all(max(first[x][y], second[x][y]) == max(x, y)
                   for x, y in product(values, repeat=2)):
                assert first == add or second == add
        counts.append(len(compatible))
    cycle = ((0, 0, 2), (0, 1, 1), (2, 1, 2))
    for pair in combinations(range(3), 2):
        assert all(cycle[x][y] in pair for x, y in product(pair, repeat=2))
        assert all(cycle[cycle[x][y]][z] == cycle[x][cycle[y][z]]
                   for x, y, z in product(pair, repeat=3))
    assert cycle[cycle[0][1]][2] == 2
    assert cycle[0][cycle[1][2]] == 0
    return counts


if __name__ == '__main__':
    maps, comparisons = check_fragments()
    native = check_native()
    check_mixed_countermodel()
    conservative = check_conservative()
    print(f'Core fragments: {maps} observer maps and {comparisons} choice comparisons '
          f'at K=3,4,5. Mixed law: {native} native valuations; six-state candidate '
          'countermodel passes all listed laws and the entire binary theory. '
          f'Conservative chain checks at sizes 2..6: {conservative} operations; '
          'three-variable lower-bound witness passed.')
