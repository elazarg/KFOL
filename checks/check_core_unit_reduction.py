"""Check the reset-unit quotients and the smaller pointed generators.

The tests verify operations, kernels, quotient units, and the maps used in
the proof. They do not establish finite basability of the pointed variety.
"""

import json
from itertools import product
from pathlib import Path

from check_core_atomic_basis import assert_laws, operation_tables
from core_atomic_basis import expand_core
from core_basis import marker_join, marker_own
from core_unit_reduction import unit_reduction_laws


def check_quotients(carrier, tables):
    add, operations, resets = tables
    profiles = {x: tuple(resets[c, x] for c in carrier) for x in carrier}
    assert len(set(profiles.values())) == len(carrier)
    pairs = 0
    for c in carrier:
        q = {x: resets[c, x] for x in carrier}
        image = set(q.values())
        assert q[c] == c
        assert all(q[x] == x for x in image)
        assert all(add[x, q[x]] == q[x] for x in carrier)
        # A term evaluated in the normalized quotient is its original
        # evaluation followed by q; in particular the named c is a unit.
        assert all(q[resets[c, x]] == x for x in image)
        for x, y in product(carrier, repeat=2):
            assert q[add[x, y]] == q[add[q[x], q[y]]]
            for table in operations:
                assert q[table[x, y]] == q[table[q[x], q[y]]]
            pairs += 1
    return pairs


def check():
    equations = quotient_pairs = pointed_generators = quotient_maps = 0
    for owners in range(3, 7):
        laws = unit_reduction_laws(owners)
        assert len(laws) == owners + 6
        carrier = tuple(range(1, 1 << owners))

        def choice(i, x, y):
            return 1 << i if 1 << i in (x, y) else x | y

        tables = operation_tables(carrier, int.__or__, choice, owners)
        equations += assert_laws(laws, carrier, tables)
        quotient_pairs += check_quotients(carrier, tables)
        if owners == 3:
            expanded = [(name, expand_core(s, owners), expand_core(t, owners))
                        for name, s, t in laws]
            equations += assert_laws(expanded, carrier, tables)

        for omitted in range(owners):
            observer = tuple(x for x in range(owners + 2) if x != omitted)
            low, high = owners, owners + 1
            observer_tables = operation_tables(
                observer, lambda x, y: marker_join(owners, x, y),
                lambda i, x, y: marker_own(owners, i, x, y), owners)
            add, operations, resets = observer_tables
            equations += assert_laws(laws, observer, observer_tables)
            quotient_pairs += check_quotients(observer, observer_tables)
            units = {c for c in observer
                     if all(resets[c, x] == x for x in observer)}
            assert units == set(observer) - {high}
            pointed_generators += len(units)

            # The remaining reflection, at p, is the atomic quotient.
            # Collapsing n,p also maps the retained pointed (O_j,n)
            # onto that same pointed quotient, with constant [p]=[n].
            collapse = {x: high if x == low else x for x in observer}
            assert all(resets[high, x] == collapse[x] for x in observer)
            image = set(collapse.values())
            assert collapse[low] == high
            for x, y in product(observer, repeat=2):
                for table in operations:
                    assert collapse[table[x, y]] == collapse[
                        table[collapse[x], collapse[y]]]
            assert all(collapse[resets[high, x]] == x for x in image)
            quotient_maps += 1

    # These are HSP-certified core models from the exhaustive small-model
    # checks. Verify the global normalization on every element, including
    # roots that are not left reset units.
    models = 0
    nonclosed_image = False
    for name in ('core-small-models', 'core-six-models',
                 'core-seven-models', 'core-eight-models'):
        path = Path(__file__).with_name('data') / (name + '.json')
        for model in json.loads(path.read_text()):
            add, ops = model['join'], model['operations']
            carrier = tuple(range(len(add)))
            tables = operation_tables(carrier, lambda x, y: add[x][y],
                                      lambda i, x, y: ops[i][x][y], len(ops))
            quotient_pairs += check_quotients(carrier, tables)
            assert any(all(tables[2][c, x] == x for x in carrier)
                       for c in carrier)
            for c in carrier:
                image = {tables[2][c, x] for x in carrier}
                if any(table[x, y] not in image for table in tables[1]
                       for x, y in product(image, repeat=2)):
                    nonclosed_image = True
            models += 1
    assert nonclosed_image  # Normalized operations cannot simply be omitted.
    print(f'Core unit reduction: {equations} equation evaluations; '
          f'{quotient_pairs} root/input-pair checks; '
          f'{pointed_generators} pointed generators and {quotient_maps} '
          f'atomic quotient maps; {models} stored core models.')


if __name__ == '__main__':
    check()
