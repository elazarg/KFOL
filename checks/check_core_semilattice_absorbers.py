"""Audit the basic-law representation of semilattice absorber extensions.

The shift identities are checked on stored models, the six-state model
failing mixed absorption, and ambient D_3,D_4. Separately, explicit tagged
covers embed into the ambient unary algebra and native pointed observers.
The arbitrary-algebra proof is in appendix-core-basis.tex.
"""

from functools import reduce
from itertools import product
import json

from check_core_absorber_pointing import apply, normal_forms
from check_core_owned_reset import test_models
from core_basis import MIXED_JOIN, MIXED_OPERATIONS, marker_join, marker_own


def shift_audit():
    models = list(test_models()) + [(MIXED_JOIN, MIXED_OPERATIONS)]
    for k in (3, 4):
        carrier = range(k + 2)
        add = [[marker_join(k, x, y) for y in carrier] for x in carrier]
        choices = [[[marker_own(k, i, x, y) for y in carrier]
                    for x in carrier] for i in range(k)]
        models.append((add, choices))
    checked = pairs = shifts = cross_shifts = basis_shifts = merges = 0
    for add, choices in models:
        n, k = len(add), len(choices)
        if n > 25:
            continue
        checked += 1
        absorbers = [reduce(lambda x, y: h[x][y], range(n)) for h in choices]
        assert all(h[a][x] == a for h, a in zip(choices, absorbers)
                   for x in range(n))
        entries = []
        for c in range(n):
            row = [c]
            for j, i in product(range(k), repeat=2):
                value = add[c][absorbers[i]]
                for owner, h in enumerate(choices):
                    if owner != j:
                        value = h[c][value]
                row.append(value)
            entries.append(row)
        for c, d in product(range(n), repeat=2):
            s = add[c][d]
            if any(h[c][d] != s for h in choices):
                continue
            pairs += 1
            left = [x for x in range(n) if add[c][x] == x]
            right = [x for x in range(n) if add[d][x] == x]
            for h in choices:
                for x, y in product(left, repeat=2):
                    assert h[add[x][s]][add[y][s]] == add[h[x][y]][s]
                    shifts += 1
                for x, y in product(left, right):
                    assert h[add[x][s]][add[y][s]] == h[x][y]
                    cross_shifts += 1
            for value, shifted in zip(entries[c], entries[s]):
                assert add[value][d] == shifted
                basis_shifts += 1
            for h in [add] + list(choices):
                for value, shifted in zip(entries[c], entries[s]):
                    for other, other_shifted in zip(entries[d], entries[s]):
                        assert h[value][other] == h[shifted][other_shifted]
                        merges += 1
    return {'models': checked, 'coefficient_pairs': pairs,
            'filter_shift_entries': shifts, 'cross_filter_entries': cross_shifts,
            'unary_basis_shifts': basis_shifts, 'basis_index_merges': merges}


def tagged_cover_audit():
    k = 3
    omega, old_top = (1 << k) - 1, (1 << k) - 2
    carrier = range(omega + 1)
    atoms = [(1 << i) - 1 for i in range(k)]
    add = [[omega if omega in (x, y) else ((x + 1) | (y + 1)) - 1
            for y in carrier] for x in carrier]
    choices = [[[a if a in (x, y) else add[x][y] for y in carrier]
                for x in carrier] for a in atoms]
    native = [add] + choices
    forms = list(normal_forms(add, choices, atoms))
    extensive = (1 + 2 ** (k - 1)) ** k
    assert len(set(forms)) == len(forms) == extensive + (1 << k) - 1
    index = {value: i for i, value in enumerate(forms)}
    unary = [[[index[apply(h, x, y)] for y in forms] for x in forms]
             for h in native]
    assert all(p[old_top] == old_top and p[omega] == omega
               for p in forms[:extensive])
    assert all(len(set(p)) == 1 for p in forms[extensive:])
    assert all(h[p][q] < extensive for h in unary
               for p, q in product(range(extensive), repeat=2))
    reports = []
    # A semilattice without a bottom, and the four-element Boolean lattice.
    for masks in ((1, 2, 3), (0, 1, 2, 3)):
        positions = {mask: i for i, mask in enumerate(masks)}
        coefficients = [[positions[x | y] for y in masks] for x in masks]
        states = ([(c, p) for c in range(len(masks)) for p in range(extensive)]
                  + [(-1, p) for p in range(extensive, len(forms))])
        state_index = {value: i for i, value in enumerate(states)}
        maps = [[p for c, p in states]]
        for bound in range(len(masks)):
            maps.append([forms[p][0] if c == -1 else
                         old_top if coefficients[c][bound] == bound else omega
                         for c, p in states])
        assert len(set(zip(*maps))) == len(states)
        entries = 0
        for operation, h in enumerate(unary):
            targets = [h] + [native[operation]] * len(masks)
            for x, (c, p) in enumerate(states):
                for y, (d, q) in enumerate(states):
                    label = h[p][q]
                    if label >= extensive:
                        value = (-1, label)
                    elif c == -1:
                        assert d != -1
                        value = (d, label)
                    elif d == -1:
                        value = (c, label)
                    else:
                        value = (coefficients[c][d], label)
                    z = state_index[value]
                    for mapping, target in zip(maps, targets):
                        assert mapping[z] == target[mapping[x]][mapping[y]]
                        entries += 1
        reports.append({'coefficient_size': len(masks), 'cover_size': len(states),
                        'separating_maps': len(maps),
                        'homomorphism_entries': entries})
    return reports


if __name__ == '__main__':
    print(json.dumps({'status': 'all assertions passed', 'shifts': shift_audit(),
                      'tagged_covers': tagged_cover_audit()}, indent=2))
