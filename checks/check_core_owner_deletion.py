"""Finite checks for deleting a globally absorbing owner at a reset unit.

The arbitrary-algebra proof is in appendix-core-basis.tex. The exhaustion
check enumerates possible joins incrementally, covering every assignment
without enumerating the full Cartesian power of the carrier.
"""

import json
from collections import Counter
from itertools import product
from pathlib import Path

from core_basis import marker_join, marker_own


def inspect(carrier, owners, add, choice, *, exhaustion=True):
    counts = Counter(models=1)
    for c, i in product(carrier, range(owners)):
        if any(choice(i, c, x) != c for x in carrier):
            continue
        counts['absorbers'] += 1
        remaining = [j for j in range(owners) if j != i]
        for j, x in product(remaining, carrier):
            value = choice(j, c, x)
            assert add(x, value) == value
            counts['neutrality'] += 1

        def reset(x, indices):
            value = add(c, x)
            for j in indices:
                value = choice(j, x, value)
            return value

        if any(reset(x, range(owners)) != x for x in carrier):
            continue
        counts['unit_absorbers'] += 1
        for x in carrier:
            assert reset(x, remaining) == x
            counts['reset_deletions'] += 1
        valid = True
        for s in carrier:
            sums = None
            for j in remaining:
                values = {choice(j, s, x) for x in carrier}
                sums = (values if sums is None else
                        {add(a, b) for a, b in product(sums, values)})
            for b in sums:
                counts['exhaustion_sums'] += 1
                valid = valid and add(s, b) == b
        assert valid == exhaustion
        counts['exhaustion_passes' if valid else 'exhaustion_failures'] += 1
    return counts


def check():
    counts = Counter()
    nonunit_witnesses = 0
    for owners in range(3, 6):
        def choice(i, x, y):
            return 1 << i if 1 << i in (x, y) else x | y

        counts += inspect(range(1, 1 << owners), owners, int.__or__, choice)
        # A native owner singleton is a global absorber but is not a
        # reset unit. The other owner singletons fail reduced exhaustion.
        top = (1 << owners) - 1
        for i in range(owners):
            c = 1 << i
            other_atoms = 0
            for j in range(owners):
                if j != i:
                    other_atoms |= choice(j, top, 1 << j)
            assert other_atoms == top ^ c
            value = c | other_atoms
            for j in range(owners):
                value = choice(j, other_atoms, value)
            assert value == top != other_atoms
            nonunit_witnesses += 1
    for name in ('small', 'six', 'seven', 'eight'):
        path = Path(__file__).with_name('data') / f'core-{name}-models.json'
        for model in json.loads(path.read_text()):
            add, operations = model['join'], model['operations']
            counts += inspect(
                range(len(add)), len(operations), lambda x, y: add[x][y],
                lambda i, x, y: operations[i][x][y])
    for owners in range(3, 7):
        for omitted in range(owners):
            carrier = [x for x in range(owners + 2) if x != omitted]
            counts += inspect(
                carrier, owners, lambda x, y: marker_join(owners, x, y),
                lambda i, x, y: marker_own(owners, i, x, y))
    assert counts['exhaustion_failures'] == 0

    # The omitted-owner exhaustion conclusion uses full owner exhaustion.
    # D_K retains all atoms and fails that hypothesis, despite having the
    # absorber, unit, and other-owner neutrality properties.
    negative = Counter()
    for owners in range(3, 7):
        negative += inspect(
            range(owners + 2), owners,
            lambda x, y: marker_join(owners, x, y),
            lambda i, x, y: marker_own(owners, i, x, y), exhaustion=False)
    assert negative['exhaustion_failures'] == sum(range(3, 7))
    print('Absorbing-owner deletion:', dict(counts))
    print(f'Native counterexamples without a reset unit: {nonunit_witnesses}')
    print('All-atom negative controls:', dict(negative))


if __name__ == '__main__':
    check()
