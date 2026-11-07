#!/usr/bin/env python3
"""Positive and negative fixed certificates for the exact typed-clone test.

Standard library only. The positive relation is checked literally, then
converted to a native cover. The negative certificate is the committed
five-edge example's finite atomic constraint obstruction and failed
compiled identity. No solver or new model search is used.
"""
from itertools import product
import json

from check_core_five_edge_countermodel import (
    coefficient_algebra, upper_clone, check_upper_clone_criterion,
)


def native(h, x, y):
    if h < 2 and h in (x, y):
        return h
    return x if x == y else max(2, x, y)


def vector(h, x, y):
    return tuple(native(h, a, b) for a, b in zip(x, y))


def positive():
    # Proper-native D01^3: three atomic units and four exterior points.
    generators = ((0, 2, 2), (2, 1, 2), (0, 1, 3))
    states = list(generators)
    seen = set(states)
    for x in states:
        for y in list(states):
            for h in range(4):
                z = vector(h, x, y)
                if z not in seen:
                    states.append(z)
                    seen.add(z)
    assert len(states) == 7
    index = {x: i for i, x in enumerate(states)}
    e = index[(2, 2, 2)]
    tables = [[[index[vector(h, x, y)] for y in states] for x in states]
              for h in range(4)]
    add = tables[-1]
    ideal = {x for x in range(7) if add[e][x] == e}
    eta = {x: next((h for h in range(2) if tables[h][e][x] != e), 2)
           for x in ideal}
    assert len(ideal) == 3 and set(eta.values()) == {0, 1, 2}

    # Independently check the old-table legality conditions R/P/C.
    for h in tables:
        for x in range(7):
            assert add[e][h[e][x]] != e or x in ideal
        for x, y in product(ideal, repeat=2):
            assert add[h[e][x]][h[e][y]] != e or e in (h[e][x], h[e][y])
    assert all(sum(h[e][x] != e for h in tables[:3]) <= 1 for x in ideal)

    relation = {(c, a) for c in range(7)
                for a in ((eta[c],) if c in ideal else range(3))}
    assert len(relation) == 15
    closure_clauses = 0
    for h, c, d, a, b in product(range(4), range(7), range(7), range(3), range(3)):
        assert ((c, a) not in relation or (d, b) not in relation
                or (tables[h][c][d], native(h, a, b)) in relation)
        closure_clauses += 1

    # Build the actual typed native cover, retaining the atomic label.
    source = {(c, a, a) for c, a in relation} | {(e, 2, 3)}
    todo = list(source)
    for c, a, v in todo:
        for d, b, w in list(todo):
            for h in range(4):
                z = tables[h][c][d], native(h, a, b), native(h, v, w)
                if z not in source:
                    source.add(z)
                    todo.append(z)
    epsilon = len(states)

    def image(s):
        c, _, v = s
        return epsilon if c == e and v == 3 else c

    def embedding(s):
        c, a, v = s
        return states[c] + (a, v)

    assert len({embedding(s) for s in source}) == len(source)
    assert {image(s) for s in source} == set(range(8))
    products_checked = 0
    for h, left, right in product(range(4), source, source):
        c, a, v = left
        d, b, w = right
        out = tables[h][c][d], native(h, a, b), native(h, v, w)
        assert out in source
        assert embedding(out) == vector(h, embedding(left), embedding(right))
        x, y = image(left), image(right)
        old = tables[h][e if x == epsilon else x][e if y == epsilon else y]
        expected = epsilon if old == e and epsilon in (x, y) else old
        assert image(out) == expected
        products_checked += 1
    return dict(base=7, clone=8, relation=len(relation),
                Boolean_variables=21, closure_clauses=closure_clauses,
                native_source=len(source), native_coordinates=5,
                cover_products=products_checked)


def negative():
    # K=4, with exactly the proper occurring owner set {0,1,2}.
    states, base = coefficient_algebra()
    legality = check_upper_clone_criterion(base)
    clone = upper_clone(base)
    e, epsilon = 0, len(states)
    edges = ((0, (0, 1)), (1, (0, 2)), (1, (1, 3)),
             (2, (0, 3)), (2, (1, 2)))
    assignments = 0
    for colors in product(range(4), repeat=4):
        # Label3 is neutral; each term is its selected two-input fold.
        assert not all(any(colors[v] == owner for v in vertices)
                       for owner, vertices in edges)
        assignments += 1
    # The neutral constraint is x_e=n. Its old realization is e.
    reset = clone[-1][epsilon][e]
    for h in clone:
        reset = h[e][reset]
    assert reset == epsilon
    rhs = e  # The guarded compiler includes x_e itself.
    owned_returns = []
    for owner, (left, right) in edges:
        term = base[owner][left + 1][right + 1]
        assert base[-1][e][term] == e
        assert base[owner][e][term] != e
        assert all(base[j][e][term] == e for j in range(4) if j != owner)
        arm = clone[owner][reset][term]
        assert arm < epsilon
        rhs = clone[-1][rhs][arm]
        owned_returns.append(term)
    assert rhs == e and clone[-1][reset][rhs] == epsilon
    return dict(base=len(states), clone=epsilon + 1,
                proper_owner_types=[0, 1, 2], old_legality_checks=legality,
                atomic_assignments_rejected=assignments,
                owned_return_terms=owned_returns,
                compiled_failure=dict(source=reset, right=rhs,
                                      source_join_right=epsilon))


if __name__ == "__main__":
    print(json.dumps(dict(status="PASS", positive=positive(), negative=negative()), indent=2))
