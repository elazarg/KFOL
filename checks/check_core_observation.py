"""Verify doubled ladders and the original nine-element HSP certificate.

This is an HSP certificate for a core model, not a countermodel to the
strengthened candidate basis. It refutes a proposed normalization lemma.
"""

import json
from itertools import combinations, product
from pathlib import Path

from core_basis import marker_own
from core_observation import (carrier, doubled_own, step_certificate, tables)
from probe_core_observation import (canonical, failure_witness, observation_depth,
                                    refine, reset_observation)
from probe_residual import merge_congruence, root


def check_original():
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

    # Identify the discovered example with the second doubled ladder.
    _, _, family_add, family_operations = tables(2)
    iso = [0, 1, 4, 5, 2, 6, 3, 7, 8]
    for x, y in product(range(9), repeat=2):
        assert iso[family_add[x][y]] == add[iso[x]][iso[y]]
        for i in range(3):
            assert iso[family_operations[i][x][y]] == operations[i][iso[x]][iso[y]]

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


def check_family():
    # The five-element base is a dissemilattice. Its expansion by join
    # belongs to the core by the seven-equation fragment theorem.
    _, _, add, operations = tables(1)
    for operation in (add, operations[0]):
        for x, y, z in product(range(5), repeat=3):
            assert operation[x][x] == x
            assert operation[x][y] == operation[y][x]
            assert operation[operation[x][y]][z] == operation[x][operation[y][z]]
    for x, y, z in product(range(5), repeat=3):
        f = operations[0]
        assert f[x][add[y][z]] == add[f[x][y]][f[x][z]]
    assert operations[1] == operations[2] == add

    source_checks = principal_checks = unit_checks = 0
    extension_principal_checks = 0
    for length in range(1, 13):
        mapping = step_certificate(length)
        assert len(mapping) == 8 * length + 4
        assert set(mapping.values()) == set(carrier(length + 1))
        for i, x, y in product(range(3), mapping, mapping):
            # A separate native interpretation of the three-state factor.
            second = (0 if i == length % 2 and 0 in (x[1], y[1])
                      else max(x[1], y[1]))
            value = doubled_own(length, i, x[0], y[0]), second
            assert value in mapping
            assert mapping[value] == doubled_own(length + 1, i, mapping[x], mapping[y])
            source_checks += 1

        values, indices, add, operations = tables(length)
        size = len(values)
        assert size == 4 * length + 1
        r, t = indices[length, 1], indices[length + 1, 1]
        for x in range(size):
            value = add[r][x]
            for operation in operations:
                value = operation[x][value]
            assert value == x
            assert all(add[x][operation[r][x]] == operation[r][x]
                       for operation in operations)
            unit_checks += 1
        for x, y in product(range(size), repeat=2):
            assert operations[2][operations[0][x][y]][operations[1][x][y]] == add[x][y]
        observation = reset_observation(add, operations, r)
        assert observation == add[r]
        partition = canonical(observation)
        pair = [indices[2 * length, bit] for bit in (0, 1)]
        for depth in range(length):
            assert partition[pair[0]] == partition[pair[1]]
            partition = refine(partition, operations)
        assert partition == list(range(size))
        # The explicit descending word, with its bit preserved at every step.
        endpoints = pair
        for j in reversed(range(length)):
            coefficient = indices[j, 1 - j % 2]
            endpoints = [operations[j % 2][x][coefficient] for x in endpoints]
        assert [observation[x] for x in endpoints] == [r, t]

        monolith = list(range(size))
        monolith[t] = r
        translations = [operation[x] for operation in operations for x in range(size)]
        for translation in translations:
            assert root(monolith, translation[r]) == root(monolith, translation[t])
        for x, y in combinations(range(size), 2):
            congruence = merge_congruence(list(range(size)), x, y, translations)
            assert root(congruence, r) == root(congruence, t)
            principal_checks += 1

        # Adjoining a common absorbing top preserves the core identities.
        # It erases the largest atomic quotient, while preserving the
        # monolith, neutral reset unit, and exact observation depth.
        infinity = size
        extended_add = [row + [infinity] for row in add] + [[infinity] * (size + 1)]
        extended_ops = [[row + [infinity] for row in operation]
                        + [[infinity] * (size + 1)] for operation in operations]
        for x in range(size + 1):
            value = extended_add[r][x]
            atomic = extended_add[infinity][x]
            for operation in extended_ops:
                value = operation[x][value]
                atomic = operation[x][atomic]
                assert extended_add[x][operation[r][x]] == operation[r][x]
            assert value == x and atomic == infinity
        extended_observation = reset_observation(extended_add, extended_ops, r)
        assert extended_observation == observation + [infinity]
        partition = canonical(extended_observation)
        for depth in range(length):
            assert partition[pair[0]] == partition[pair[1]]
            partition = refine(partition, extended_ops)
        assert partition == list(range(size + 1))
        extended_monolith = monolith + [infinity]
        translations = [operation[x] for operation in extended_ops
                        for x in range(size + 1)]
        for translation in translations:
            assert root(extended_monolith, translation[r]) == root(
                extended_monolith, translation[t])
        for x, y in combinations(range(size + 1), 2):
            congruence = merge_congruence(list(range(size + 1)), x, y, translations)
            assert root(congruence, r) == root(congruence, t)
            extension_principal_checks += 1
    print(f'Doubled ladders: lengths 1..12; {source_checks} inductive HSP '
          f'pair/owner checks; {principal_checks} principal congruences; '
          f'{unit_checks} neutral-unit checks; exact observation depth equals length.')
    print(f'Absorbing-top doubled ladders: {extension_principal_checks} principal '
          'congruences; trivial largest atomic quotient and unchanged exact depth.')


if __name__ == '__main__':
    check_original()
    check_family()
