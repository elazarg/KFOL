#!/usr/bin/env python3
"""Verify the B3 supported region and its global-absorber observers.

No external packages, scratch imports, or native-equality quotienting.
The two 378-element carriers are built from literal upset masks first.
Native maps then verify their identities, separation, and extensions to
global absorber assignments. This does not prove the presentation's
universal property or make a claim about the whole absorber extension.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path


def native_tables(k, marker=True):
    size = k + 2 if marker else k + 1
    def join(x, y):
        if x == y:
            return x
        if marker and k + 1 in (x, y):
            return k + 1
        return k
    join_table = [[join(x, y) for y in range(size)] for x in range(size)]
    tables = [join_table]
    for owner in range(k):
        tables.append([[owner if owner in (x, y) else join(x, y)
                        for y in range(size)] for x in range(size)])
    return tables


def flat_base(k):
    return dict(name=f'B{k}', k=k, elements=list(range(k + 1)),
                operations=native_tables(k, marker=False), top=k)


def nonflat_base():
    b = native_tables(2, marker=False)
    points = [(0, 1), (0, 2), (2, 1), (2, 2)]
    index = {p: i for i, p in enumerate(points)}
    tables = [[[index[tuple(op[x[c]][y[c]] for c in range(2))]
                for y in points] for x in points] for op in b]
    return dict(name='B2_square4', k=2, elements=points,
                operations=tables, top=3)


def coefficient_data(base):
    k, top, ops = base['k'], base['top'], base['operations']
    n = len(base['elements'])
    target = native_tables(k, marker=False)
    omega = []
    for phi in itertools.product(range(k + 1), repeat=n):
        if phi[top] != k:
            continue
        if base.get('proper', False) and all(i in phi for i in range(k)):
            continue
        if all(phi[op[x][y]] == target[o][phi[x]][phi[y]]
               for o, op in enumerate(ops) for x in range(n) for y in range(n)):
            omega.append(phi)
    assert omega
    size = len(omega)
    full = (1 << size) - 1
    z = [sum(1 << j for j, phi in enumerate(omega) if phi[d] == k)
         for d in range(n)]
    assert z[top] == full
    order = [[all(target[0][a][b] == b for a, b in zip(phi, psi))
              for psi in omega] for phi in omega]
    # The Z-neutral predicates must recover the entire order.
    for i in range(size):
        for j in range(size):
            by_z = all(not (mask >> i & 1) or (mask >> j & 1) for mask in z)
            assert order[i][j] == by_z
    upsets = []
    for mask in range(1 << size):
        if all(not (mask >> i & 1) or not order[i][j] or (mask >> j & 1)
               for i in range(size) for j in range(size)):
            upsets.append(mask)
    lattice = set(z) | {0, full}
    todo = list(lattice)
    at = 0
    while at < len(todo):
        a = todo[at]
        for b in tuple(todo):
            for c in (a & b, a | b):
                if c not in lattice:
                    lattice.add(c)
                    todo.append(c)
        at += 1
    assert lattice == set(upsets)
    # Atomic base observers are sufficient even if one adds no upper bit.
    assert len({tuple(phi[d] for phi in omega) for d in range(n)}) == n
    return omega, z, upsets


def check_case(base, supports, data, predicted=None):
    k, bops = base['k'], base['operations']
    omega, z, upsets = data
    m = len(supports)
    assert m == k == 3 and supports == (0, 1, 2)
    carrier = []
    for d in range(len(z)):
        choices = [[u for u in upsets if u & ~(z[d] & z[c]) == 0]
                   for c in supports]
        carrier.extend((d, tuple(us)) for us in itertools.product(*choices))
    positions = {a: i for i, a in enumerate(carrier)}
    assert len(positions) == len(carrier)
    n = len(carrier)
    if predicted is not None:
        assert n == predicted, (base['name'], supports, n, predicted)

    # Build the exact table without referring to native evaluations.
    operations = []
    for base_op in bops:
        table = [[-1] * n for _ in range(n)]
        for x, (d, us) in enumerate(carrier):
            for y in range(x, n):
                e, vs = carrier[y]
                tag = base_op[d][e]
                result = (tag, tuple((u | v) & z[tag] for u, v in zip(us, vs)))
                value = positions[result]
                table[x][y] = table[y][x] = value
        operations.append(table)
    for op in operations:
        assert all(op[x][x] == x for x in range(n))

    zeros = (0,) * m
    section = [positions[(d, zeros)] for d in range(len(z))]
    qmap = [section[d] for d, _ in carrier]
    assert all(qmap[qmap[x]] == qmap[x] for x in range(n))
    generators = list(section)
    for i, c in enumerate(supports):
        us = [0] * m
        us[i] = z[c]
        generators.append(positions[(c, tuple(us))])
    section_entries = 0
    for o, op in enumerate(operations):
        for d in range(len(z)):
            for e in range(len(z)):
                assert op[section[d]][section[e]] == section[bops[o][d][e]]
                section_entries += 1
    support_entries = 0
    for x, (d, _) in enumerate(carrier):
        for op in operations:
            assert op[section[d]][x] == x
            support_entries += 1
    # Verify the coefficient projection and q endomorphism directly.
    q_endomorphism_entries = 0
    for o, op in enumerate(operations):
        for x in range(n):
            for y in range(n):
                assert carrier[op[x][y]][0] == bops[o][carrier[x][0]][carrier[y][0]]
                assert qmap[op[x][y]] == op[qmap[x]][qmap[y]]
                q_endomorphism_entries += 1

    seen = set(generators)
    frontier = list(seen)
    at = 0
    while at < len(frontier):
        x = frontier[at]
        for y in tuple(frontier):
            for op in operations:
                result = op[x][y]
                if result not in seen:
                    seen.add(result)
                    frontier.append(result)
        at += 1
    assert len(seen) == n, (base['name'], supports, len(seen), n)

    # Include the zero-bit/base observer for each phi explicitly. Each other
    # observer reads exactly one retained-input index, never ORs all inputs.
    observers = []
    names = []
    for j, phi in enumerate(omega):
        observers.append(tuple(phi[d] for d, _ in carrier))
        names.append((j, -1))
        for i in range(m):
            observers.append(tuple(k + 1 if (us[i] >> j) & 1 else phi[d]
                                   for d, us in carrier))
            names.append((j, i))
    signatures = [tuple(h[x] for h in observers) for x in range(n)]
    assert len(set(signatures)) == n
    native = native_tables(k)
    native_q = list(range(k + 1)) + [k]
    q_observer_entries = 0
    for h in observers:
        for x in range(n):
            assert h[qmap[x]] == native_q[h[x]]
            q_observer_entries += 1
    hom_entries = 0
    for o, op in enumerate(operations):
        nt = native[o]
        for h in observers:
            for x in range(n):
                hx = h[x]
                # Check every ordered table entry, including both directions.
                for y in range(n):
                    assert h[op[x][y]] == nt[hx][h[y]], (
                        base['name'], supports, o, x, y)
                    hom_entries += 1
    exhaustion_entries = 0
    if base.get('proper', False):
        assert k >= 3
        for values in {tuple(sorted(set(h))) for h in observers}:
            omitted = [i for i in range(k) if i not in values]
            assert omitted
            assert all(native[omitted[0] + 1][x][y] == native[0][x][y]
                       for x in values for y in values)
            for c in values:
                for xs in itertools.product(values, repeat=k):
                    terms = [native[i + 1][c][xs[i]] for i in range(k)]
                    rhs = terms[0]
                    for term in terms[1:]:
                        rhs = native[0][rhs][term]
                    assert native[0][c][rhs] == rhs
                    exhaustion_entries += 1
        # The separating homomorphisms transfer these target identities to
        # the full carrier; no large-carrier (K+1)-tuple enumeration is used.
    extension_cases = 0
    recovered_generator_checks = 0
    global_absorber_checks = 0
    core_extension_entries = 0
    upper_extension_cases = 0
    atomic_extension_cases = 0
    native_extension_records = []
    for observer, (phi_index, selected) in zip(observers, names):
        phi = omega[phi_index]
        upper = selected if selected >= 0 and phi[supports[selected]] == k else None
        assigned = [k + 1 if i == upper else i for i in range(k)]
        if upper is not None:
            assert phi[supports[upper]] == k
            assert upper not in phi
        image = set(phi) | set(assigned)
        while True:
            closure = image | {op[x][y] for op in native for x in image for y in image}
            if closure == image:
                break
            image = closure
        for i, a in enumerate(assigned):
            for x in image:
                assert native[i + 1][a][x] == a
                global_absorber_checks += 1
        if k + 1 in image:
            assert upper is not None and upper not in image
            upper_extension_cases += 1
        else:
            assert image <= set(range(k + 1))
            atomic_extension_cases += 1
        shadows = []
        recovered = []
        for i, a in enumerate(assigned):
            b = native[0][k][a]
            for h in range(k):
                b = native[h + 1][k][b]
            shadows.append(b)
            c = phi[supports[i]]
            u = native[0][b][c]
            for h in range(k):
                u = native[h + 1][c][u]
            recovered.append(u)
            assert u == observer[generators[len(section) + i]]
            assert b == native[0][k][u]
            recovered_generator_checks += 1
        # Exhaustion is checked on the full range including the new absorbers.
        for c in image:
            for xs in itertools.product(image, repeat=k):
                value = native[1][c][xs[0]]
                for i in range(1, k):
                    value = native[0][value][native[i + 1][c][xs[i]]]
                assert native[0][c][value] == value
                core_extension_entries += 1
        native_extension_records.append(dict(phi=list(phi), selected=selected,
                                             upper=upper, absorbers=assigned,
                                             image=sorted(image), shadows=shadows,
                                             recovered=recovered))
        extension_cases += 1
    result = dict(base=base['name'], k=k, supports=list(supports),
                  base_size=len(z), omega_size=len(omega),
                  operator_lattice_size=len(upsets), carrier_size=n,
                  generators=len(set(generators)),
                  native_observers=len(observers),
                  section_entries=section_entries, support_entries=support_entries,
                  homomorphism_entries=hom_entries,
                  exhaustion_target_entries=exhaustion_entries,
                  q_endomorphism_entries=q_endomorphism_entries,
                  q_observer_entries=q_observer_entries,
                  extension_cases=extension_cases,
                  upper_extension_cases=upper_extension_cases,
                  atomic_extension_cases=atomic_extension_cases,
                  global_absorber_checks=global_absorber_checks,
                  recovered_generator_checks=recovered_generator_checks,
                  core_extension_entries=core_extension_entries)
    print(json.dumps(result, sort_keys=True), flush=True)
    return result, dict(carrier=carrier, operations=operations, omega=omega, observers=native_extension_records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path, help='write a portable JSON summary')
    args = parser.parse_args()
    ambient = flat_base(3)
    proper = flat_base(3)
    proper.update(name='B3_proper', proper=True)
    results, models = [], []
    for base in (ambient, proper):
        result, model = check_case(base, (0, 1, 2), coefficient_data(base), 378)
        results.append(result)
        models.append(model)
    full, reduced = models
    columns = [full['omega'].index(phi) for phi in reduced['omega']]
    positions = {point: i for i, point in enumerate(reduced['carrier'])}
    def restrict(mask):
        return sum(1 << j for j, old in enumerate(columns) if mask >> old & 1)
    comparison = [positions[(tag, tuple(restrict(mask) for mask in indices))]
                  for tag, indices in full['carrier']]
    assert len(set(comparison)) == 378
    comparison_entries = 0
    for a, b in zip(full['operations'], reduced['operations']):
        for x, y in itertools.product(range(378), repeat=2):
            assert comparison[a[x][y]] == b[comparison[x]][comparison[y]]
            comparison_entries += 1
    total = dict(cases=2, carrier_sizes=[378, 378],
                 homomorphism_entries=sum(r['homomorphism_entries'] for r in results),
                 observer_extensions=sum(r['extension_cases'] for r in results),
                 recovered_generator_checks=sum(r['recovered_generator_checks'] for r in results),
                 global_absorber_checks=sum(r['global_absorber_checks'] for r in results),
                 core_extension_entries=sum(r['core_extension_entries'] for r in results),
                 ambient_proper_isomorphism_entries=comparison_entries)
    print('PASS ' + json.dumps(total, sort_keys=True), flush=True)
    if args.json:
        args.json.write_text(json.dumps(dict(
            scope='Literal supported-envelope and observer-extension verification only; the universal supported-region theorem is proved separately. No claim about the full absorber extension.',
            cases=results, totals=total,
            observer_extensions=[model['observers'] for model in models]), indent=2) + '\n')


if __name__ == '__main__':
    main()
