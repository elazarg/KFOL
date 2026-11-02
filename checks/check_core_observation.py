"""Verify the nine-element obstruction to one-step reset observations.

This is an HSP certificate for a core model, not a countermodel to the
strengthened candidate basis. It refutes a proposed normalization lemma.
"""

import json
from itertools import combinations, product
from pathlib import Path

from core_basis import marker_own
from probe_core_observation import (failure_witness, observation_depth,
                                    refine, reset_observation)
from probe_residual import merge_congruence, root


def check():
    path = Path(__file__).with_name('data') / 'core-observation-countermodel.json'
    certificate = json.loads(path.read_text())
    add, operations = certificate['join'], certificate['operations']
    source = list(map(tuple, certificate['source']))
    images, observers = certificate['map'], certificate['observers']
    assert len(add) == 9 and len(source) == 36 and len(operations) == 3
    assert len(source) == len(set(source)) == len(images)
    mapping = dict(zip(source, images))
    assert set(images) == set(range(9))
    assert all(len(x) == len(observers) and
               all(0 <= a < 5 and a != j for a, j in zip(x, observers))
               for x in source)
    count = 0
    for i, x, y in product(range(3), source, source):
        value = tuple(marker_own(3, i, a, b) for a, b in zip(x, y))
        assert value in mapping
        assert mapping[value] == operations[i][mapping[x]][mapping[y]]
        count += 1
    for x, y in product(range(9), repeat=2):
        assert operations[2][operations[0][x][y]][operations[1][x][y]] == add[x][y]
    assert operations[2] == add

    # The named unit is also neutral in the join order.
    r = 2
    for x in range(9):
        value = add[r][x]
        for table in operations:
            value = table[x][value]
        assert value == x
        assert all(add[x][table[r][x]] == table[r][x] for table in operations)
    observation = reset_observation(add, operations, r)
    assert observation == [2, 3, 2, 3, 3, 3, 3, 8, 8]
    assert observation == add[r]
    first = refine(observation, operations)
    assert first == [0, 1, 2, 3, 4, 5, 6, 7, 7]
    assert refine(first, operations) == list(range(9))
    assert observation_depth(add, operations) == (2, r)
    assert failure_witness(add, operations) == certificate['observation_witness']
    assert [operations[1][x][4] for x in (7, 8)] == [4, 5]
    assert [operations[0][x][1] for x in (4, 5)] == [0, 1]
    assert [observation[x] for x in (0, 1)] == [2, 3]

    # Verify the stated monolith itself and its inclusion in every nonzero
    # principal congruence; no assumption of irreducibility is used.
    monolith = list(range(9))
    monolith[3] = 2
    translations = [table[x] for table in operations for x in range(9)]
    for translation in translations:
        assert root(monolith, translation[2]) == root(monolith, translation[3])
    for x, y in combinations(range(9), 2):
        congruence = merge_congruence(list(range(9)), x, y, translations)
        assert root(congruence, 2) == root(congruence, 3)
    print(f'Core observation obstruction: {count} source pair/owner checks; '
          '36 principal congruences contain the monolith {2,3}; '
          'neutral reset unit 2; one-step kernel identifies 7,8 and '
          'two steps distinguish them.')


if __name__ == '__main__':
    check()
