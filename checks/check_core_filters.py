"""Check the principal-filter decomposition under Gamma alone.

The arbitrary-algebra proof is in the TR. These checks cover native
generators, stored HSP models, doubled ladders, and two families outside
the core variety that still satisfy Gamma.
"""

import json
from itertools import product
from pathlib import Path

from core_basis import MIXED_JOIN, MIXED_OPERATIONS, marker_join, marker_own
from core_observation import tables


def check_filters(add, operations):
    carrier = range(len(add))
    owners = range(len(operations))
    pairs = 0
    for c in carrier:
        domain = [x for x in carrier if add[c][x] == x]
        maps = [{x: operation[c][x] for x in domain}
                for operation in operations]
        projections = []
        for j in owners:
            projection = {}
            for x in domain:
                value = x
                for i in owners:
                    if i != j:
                        value = maps[i][value]
                projection[x] = value
            projections.append(projection)

        for x in domain:
            value = projections[0][x]
            for projection in projections[1:]:
                value = add[value][projection[x]]
            assert value == x
            for i, mapping in enumerate(maps):
                assert mapping[x] in domain
                assert add[mapping[x]][x] == x
                assert mapping[mapping[x]] == mapping[x]
                for j, other in enumerate(maps):
                    assert mapping[other[x]] == other[mapping[x]]
                    if i != j:
                        assert add[mapping[x]][other[x]] == x
            for projection in projections:
                assert projection[projection[x]] == projection[x]

        for x, y in product(domain, repeat=2):
            for operation in [add, *operations]:
                value = operation[x][y]
                assert value in domain
                for mapping in [*maps, *projections]:
                    assert mapping[value] == operation[mapping[x]][mapping[y]]
            for j, projection in enumerate(projections):
                a, b = projection[x], projection[y]
                for i, operation in enumerate(operations):
                    if i != j:
                        assert operation[a][b] == add[a][b]
            pairs += 1
    return len(add), pairs


def check():
    models = []
    for owners in range(3, 6):
        carrier = range(1, 1 << owners)
        add = [[(x | y) - 1 for y in carrier] for x in carrier]
        operations = [[[((1 << i) if (1 << i) in (x, y) else x | y) - 1
                        for y in carrier] for x in carrier]
                      for i in range(owners)]
        models.append((add, operations))
    for name in ('small', 'six', 'seven', 'eight'):
        path = Path(__file__).with_name('data') / f'core-{name}-models.json'
        for model in json.loads(path.read_text()):
            models.append((model['join'], model['operations']))
    # Neither of these countermodel families belongs to the core variety;
    # the filter theorem needs neither exhaustion nor mixed absorption.
    models.append((MIXED_JOIN, MIXED_OPERATIONS))
    for owners in range(3, 7):
        carrier = range(owners + 2)
        add = [[marker_join(owners, x, y) for y in carrier] for x in carrier]
        operations = [[[marker_own(owners, i, x, y) for y in carrier]
                       for x in carrier] for i in range(owners)]
        models.append((add, operations))
    for length in range(1, 13):
        _, _, add, operations = tables(length)
        models.append((add, operations))
    filters = pairs = 0
    for add, operations in models:
        local_filters, local_pairs = check_filters(add, operations)
        filters += local_filters
        pairs += local_pairs
    print(f'Join-filter decomposition: {len(models)} models, {filters} filters, '
          f'{pairs} input pairs; full endomorphisms, retractions, one-owner '
          'images, and the separating join cover checked.')


if __name__ == '__main__':
    check()
