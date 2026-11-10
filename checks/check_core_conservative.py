"""Finite checks of the conservative core classification in the report.

Check all compatible conservative chain operations at sizes two through six,
pair coverage, and the three-variable obstruction. No candidate-basis search.
"""

from itertools import combinations, permutations, product


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
    counts = check_conservative()
    print(f'Conservative core classification: compatible chain checks at sizes 2..6: {counts}; '
          'pair coverage and three-variable obstruction passed.')
