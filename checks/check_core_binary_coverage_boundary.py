#!/usr/bin/env python3
"""Binary sourced coverage does not imply ternary sourced coverage.

Standard library only. Fifteen explicit native tuples and e generate a
235-element coefficient algebra. Its legal rigid upper clone satisfies
every binary-clause coverage identity but fails the displayed ternary law.
The universal binary assertion has a written coloring proof; this checker
also tests that coloring on every coefficient pair. Unused owners are join.
"""
from functools import reduce
from itertools import combinations, permutations, product
import json
import time

from check_core_five_edge_countermodel import check_new_laws, upper_clone


ROWS = tuple(permutations(range(3)))
NEUTRAL = (3,) * 6


def vector(owner, left, right):
    return tuple(owner if owner < 3 and owner in (a, b)
                 else a if a == b else max(3, a, b)
                 for a, b in zip(left, right))


def mixed(position, missing, markers):
    return tuple(4 if row in markers else 3 if sigma[position] == missing
                 else sigma[position] for row, sigma in enumerate(ROWS))


def witness():
    vertices, positions = [], []
    for position in range(3):
        for missing in range(3):
            neutral = {row for row, sigma in enumerate(ROWS)
                       if sigma[position] == missing}
            masks = [{row} for row in sorted(neutral)] if position < 2 else [neutral]
            for mask in masks:
                vertices.append(mixed(position, missing, mask))
                positions.append(position)
    assert len(vertices) == len(set(vertices)) == 15
    index = {value: i for i, value in enumerate(vertices)}
    edges = []
    for owner in range(3):
        groups = [[i for i, value in enumerate(vertices)
                   if positions[i] == position and owner in value]
                  for position in range(3)]
        assert list(map(len, groups)) == [4, 4, 2]
        edges.extend((owner, edge) for edge in product(*groups))
    for i, j, k in permutations(range(3)):
        x = mixed(0, k, {ROWS.index((k, i, j))})
        y = mixed(1, j, {ROWS.index((i, j, k))})
        edges.append((i, (index[x], index[y])))
    assert len(edges) == 102
    return vertices, edges


def coefficients(vertices):
    states, provenance, index = [], [], {}
    generators = [NEUTRAL] + vertices

    def add(value, term):
        if value not in index:
            index[value] = len(states)
            states.append(value)
            provenance.append(term)

    for i, value in enumerate(generators):
        add(value, ('generator', i))
    current = 0
    while current < len(states):
        for other in range(current + 1):
            for owner in range(4):
                add(vector(owner, states[current], states[other]),
                    ('operation', owner, current, other))
        current += 1
    assert len(states) == 235 and states[0] == NEUTRAL
    for i, term in enumerate(provenance):
        if term[0] == 'generator':
            assert states[i] == generators[term[1]]
        else:
            _, owner, left, right = term
            assert left < i and right < i
            assert states[i] == vector(owner, states[left], states[right])
    tables = [[[index[vector(owner, x, y)] for y in states] for x in states]
              for owner in range(4)]
    return states, tables, index


def criterion(states, tables):
    join, e = tables[-1], 0
    ideal = [x for x in range(len(states)) if join[e][x] == e]
    counts = dict(reflection=0, primeness=0, coverage=0)
    for x in ideal:
        owners = set(states[x]) & {0, 1, 2}
        assert len(owners) <= 1
        if owners:
            owner = next(iter(owners))
            assert all(value == owner for sigma, value in zip(ROWS, states[x])
                       if sigma[0] == owner)
    for operation in tables:
        for x in range(len(states)):
            assert join[e][operation[e][x]] != e or x in ideal
            counts['reflection'] += 1
        for x, y in product(ideal, repeat=2):
            a, b = operation[e][x], operation[e][y]
            assert join[a][b] != e or e in (a, b)
            counts['primeness'] += 1
    for i, j in combinations(range(4), 2):
        for x in ideal:
            assert e in (tables[i][e][x], tables[j][e][x])
            counts['coverage'] += 1
    return counts


def binary_coloring(states, tables):
    colors = []
    for value in states:
        owners = set(value) & {0, 1, 2}
        if not owners:
            colors.append(None)
        elif len(owners) == 1:
            colors.append(next(iter(owners)))
        else:
            markers = [row for row, item in enumerate(value) if item == 4]
            positions = [r for r in range(3)
                         if all(item == sigma[r] if sigma[r] in owners
                                else item in (3, 4)
                                for sigma, item in zip(ROWS, value))]
            assert len(owners) == 2 and len(markers) in (1, 2)
            assert len(positions) == 1
            color = (ROWS[markers[0]][(positions[0] + 1) % 3]
                     if len(markers) == 1 else min(owners))
            assert color in owners
            colors.append(color)
    checked = strict = 0
    for owner in range(3):
        operation = tables[owner]
        for x in range(len(states)):
            for y in range(x, len(states)):
                arm = operation[0][operation[x][y]]
                checked += 1
                if arm != 0 and tables[-1][0][arm] == 0:
                    assert owner in (colors[x], colors[y])
                    strict += 1
    return checked, strict


def atomic_fibers(states, tables):
    atomic = [tuple(min(value, 3) for value in state) for state in states]
    atomic.append(NEUTRAL)
    entries = common = 0
    for owner, operation in enumerate(tables):
        for x, y in product(range(len(atomic)), repeat=2):
            assert atomic[operation[x][y]] == vector(owner, atomic[x], atomic[y])
            entries += 1
            if atomic[x] == atomic[y]:
                assert operation[x][y] == tables[-1][x][y]
                common += 1
    return len(set(atomic)), entries, common


def main():
    start = time.monotonic()
    vertices, edges = witness()
    states, base, index = coefficients(vertices)
    criteria = criterion(states, base)
    binary_entries, strict_edges = binary_coloring(states, base)
    tables = upper_clone(base)
    laws = check_new_laws(tables)
    atomic_size, atomic_entries, fiber_entries = atomic_fibers(states, tables)
    epsilon = len(states)
    arms = []
    for owner, edge in edges:
        operation = tables[owner]
        value = reduce(lambda a, b: operation[a][b],
                       (index[vertices[x]] for x in edge), epsilon)
        assert value not in (0, epsilon) and tables[-1][0][value] == 0
        if len(edge) == 3:
            assert states[value] == (owner,) * 6
        arms.append(value)
    rhs = reduce(lambda a, b: tables[-1][a][b], arms)
    assert rhs == 0 and tables[-1][epsilon][rhs] == epsilon != rhs
    choices = [sorted(set(value) & {0, 1, 2}) for value in vertices]
    assert all(len(options) == 2 for options in choices)
    assert all(owner in choices[x] for owner, edge in edges for x in edge)
    colorings = 0
    for coloring in product(*choices):
        assert any(all(coloring[x] != owner for x in edge) for owner, edge in edges)
        colorings += 1
    print(json.dumps(dict(
        status='PASS', coefficient_size=len(states), clone_size=len(tables[0]),
        source_products=4 * len(states) ** 2, criterion_entries=criteria,
        new_Gamma_M_entries=laws, binary_pair_checks=binary_entries,
        strict_binary_edges=strict_edges, atomic_quotient_size=atomic_size,
        atomic_hom_entries=atomic_entries, common_fiber_entries=fiber_entries,
        vertices=len(vertices), binary_clauses=6, ternary_clauses=96,
        incident_owner_colorings=colorings, seconds=time.monotonic()-start,
        scope='K>=4; unused owners are join. Binary coverage is uniform, '
              'not a variable-bound check or a nonfinite-basis conclusion.'), indent=2))


if __name__ == '__main__':
    main()
