"""Exact audit of free-join observers and the exhaustion criterion.

The arbitrary-cardinality representation proof is in the core-basis appendix.
These finite checks enumerate all total preorders in the stated sizes,
then every owner tuple up to permutation satisfying pair coverage.
"""
from itertools import combinations, combinations_with_replacement, product
import json


def join(k, a, b):
    return a if a == b else k + 1 if k + 1 in (a, b) else k


def choice(k, i, a, b):
    return i if i in (a, b) else join(k, a, b)


def preorders(n):
    return [ranks for ranks in product(range(n), repeat=n)
            if set(ranks) == set(range(max(ranks) + 1))]


def table(n, ranks):
    values = range(1, 1 << n)
    result = [[0] * (1 << n) for _ in range(1 << n)]
    for a, b in product(values, repeat=2):
        for x, y in product(range(n), repeat=2):
            if a >> x & 1 and b >> y & 1:
                if ranks[x] >= ranks[y]:
                    result[a][b] |= 1 << x
                if ranks[y] >= ranks[x]:
                    result[a][b] |= 1 << y
    for a, b, c in product(values, repeat=3):
        assert result[a][a] == a and result[a][b] == result[b][a]
        assert result[result[a][b]][c] == result[a][result[b][c]]
        assert result[a][b | c] == result[a][b] | result[a][c]
    return result


def exhausted(values, operations):
    # Enumerate all possible cover values, merging equal partial unions.
    for c in values:
        sums = {0}
        for operation in operations:
            outputs = {operation[c][x] for x in values}
            sums = {a | b for a in sums for b in outputs}
        if any(c | cover != cover for cover in sums):
            return False
    return True


def audit(n, k):
    values = range(1, 1 << n)
    orders = preorders(n)
    tables = [table(n, order) for order in orders]
    preferences = [sum(1 << (n * x + y)
                       for x, y in product(range(n), repeat=2) if r[x] > r[y])
                   for r in orders]
    models = core_models = map_entries = 0
    for indices in combinations_with_replacement(range(len(orders)), k):
        if any(preferences[a] & preferences[b] for a, b in combinations(indices, 2)):
            continue
        operations = [tables[i] for i in indices]
        maximal = [[all(orders[index][y] <= orders[index][x] for y in range(n))
                    for index in indices] for x in range(n)]
        criterion = all(any(row) for row in maximal)
        assert exhausted(values, operations) == criterion
        for a, b in product(values, repeat=2):
            assert all(operations[i][a][b] | operations[j][a][b] == a | b
                       for i, j in combinations(range(k), 2))
        for x in range(n):
            labels = []
            for y in range(n):
                preferred = [i for i, index in enumerate(indices)
                             if orders[index][y] > orders[index][x]]
                assert len(preferred) <= 1
                labels.append(k + 1 if y == x else preferred[0] if preferred else k)
            images = {}
            for a in values:
                atoms = [labels[y] for y in range(n) if a >> y & 1]
                image = atoms[0]
                for value in atoms[1:]:
                    image = join(k, image, value)
                images[a] = image
                assert (image == k + 1) == bool(a >> x & 1)
            for a, b in product(values, repeat=2):
                assert images[a | b] == join(k, images[a], images[b])
                for i, operation in enumerate(operations):
                    assert images[operation[a][b]] == choice(k, i, images[a], images[b])
                    map_entries += 1
            for i in range(k):
                if maximal[x][i]:
                    assert i not in images.values()
        models += 1
        core_models += criterion
    return {'atoms': n, 'owners': k, 'preorders': len(orders),
            'ambient_models_up_to_owner_permutation': models,
            'models_satisfying_exhaustion': core_models,
            'choice_homomorphism_entries': map_entries}


def check_cover_obstruction():
    # The four-element lattice is a core subpower, with owner 0 acting as meet.
    image = {x: tuple(4 if x >> i & 1 else 0 for i in range(2)) for x in range(4)}
    for a, b in product(range(4), repeat=2):
        assert image[a | b] == tuple(join(3, x, y) for x, y in zip(image[a], image[b]))
        for i in range(3):
            result = a & b if i == 0 else a | b
            assert image[result] == tuple(choice(3, i, x, y)
                                           for x, y in zip(image[a], image[b]))
    for atom in (1, 2):
        assert all(a == atom or b == atom
                   for a, b in product(range(4), repeat=2) if a | b == atom)
    assert 1 & 2 == 0 and 0 not in (1, 2, 1 | 2)


if __name__ == '__main__':
    results = [audit(n, k) for n, k in ((2, 3), (3, 3), (4, 3), (3, 4))]
    check_cover_obstruction()
    print(json.dumps({'status': 'all assertions passed', 'cases': results,
                      'four_element_cover_obstruction': 'verified'}, indent=2))
