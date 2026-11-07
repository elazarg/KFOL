#!/usr/bin/env python3
"""Fixed native-cover certificates for atomic two-owner region doublings.

Standard library only. Rebuilds all lattices, reductions, and native sources;
does not import search output or assume the candidate identities.
"""
from itertools import product
import json


def native_join(x, y):
    return x if x == y else max(2, x, y)


NATIVE = (native_join,
          lambda x, y: 0 if 0 in (x, y) else native_join(x, y),
          lambda x, y: 1 if 1 in (x, y) else native_join(x, y))


def coordinate_product(h, x, y):
    return tuple(h(a, b) for a, b in zip(x, y))


left_relation = {(0, 0), (1, 1), (2, 2), (3, 3),
                 (1, 3), (3, 1), (2, 3), (3, 2)}
swap = (1, 0, 2, 3)
right_relation = {tuple(swap[x] for x in pair) for pair in left_relation}
relation_entries = 0
for relation in (left_relation, right_relation):
    for h, x, y in product(NATIVE, relation, relation):
        assert coordinate_product(h, x, y) in relation
        relation_entries += 1
    assert {x for x in relation if 3 not in x} == {(0, 0), (1, 1), (2, 2)}


def check(name, predecessors, r, types):
    size = len(predecessors)
    lattice = [x for x in range(1 << size)
               if all(not (x & (1 << i)) or x & p == p
                      for i, p in enumerate(predecessors))]
    assert r in lattice and set(types) <= set(lattice)
    owned_f = {x for x in types if types[x] == 0}
    owned_g = {x for x in types if types[x] == 1}
    neutral = {x for x in types if types[x] == 2}
    owned = owned_f | owned_g
    assert owned_f and owned_g and neutral
    c, d = min(neutral, key=int.bit_count), max(neutral, key=int.bit_count)
    assert all(c & x == c and d | x == d for x in neutral)

    def base(h, x, y):
        return ((x & y) | ((x | y) & r), x & y, x | y)[h]

    for h, x, y in product(range(3), types, types):
        z = base(h, x, y)
        assert z in types and types[z] == NATIVE[h](types[x], types[y])
    for x in lattice:
        assert (x & c in owned_f) == (x in owned_f)
        assert (x | d in owned_g) == (x in owned_g)
    for x, y in product(lattice, repeat=2):
        if x in owned_f:
            assert x & y in owned_f
        if x in owned_g:
            assert x | y in owned_g
        if x in types and y not in owned:
            if x not in owned_f:
                assert x & y not in owned
            if x not in owned_g:
                assert x | y not in owned
        if x & y in owned_f and x | y in owned_g:
            assert x in owned and y in owned

    # The shorter proof's two quotient maps and exact endpoint fibers.
    rho = {x: (x & c, x | d) for x in lattice}
    image_f, image_g = {rho[x] for x in owned_f}, {rho[x] for x in owned_g}
    a = tuple(max((x[i] for x in image_f), key=int.bit_count) for i in range(2))
    b = tuple(min((x[i] for x in image_g), key=int.bit_count) for i in range(2))
    theta = {x: tuple((v | lo) & hi for v, lo, hi in zip(rho[x], a, b))
             for x in lattice}
    assert {x for x in lattice if theta[x] == a} == owned_f
    assert {x for x in lattice if theta[x] == b} == owned_g
    assert len({theta[x] for x in neutral}) == 1
    for h, x, y in product(range(3), lattice, lattice):
        target = tuple(((u & v) | ((u | v) & pivot), u & v, u | v)[h]
                       for u, v, pivot in zip(theta[x], theta[y], theta[r]))
        assert theta[base(h, x, y)] == target

    # Independently construct the direct all-extension-edge HS cover.
    top_f = max(owned_f, key=int.bit_count)
    bottom_g = min(owned_g, key=int.bit_count)
    edges = [(i, j) for i, j in product(range(size), repeat=2)
             if (c & ~top_f) & (1 << i) and (bottom_g & ~d) & (1 << j)
             and predecessors[j] & (1 << i)]
    assert edges

    def shadow(x):
        return tuple(0 if not x & (1 << i) else 1 if x & (1 << j) else 2
                     for i, j in edges)

    source = {(x, tuple(3 if v == 2 else v for v in shadow(x))) for x in lattice}
    source |= {(x, (t,) * len(edges)) for x, t in types.items()}
    todo = list(source)
    for x, v in todo:
        for y, w in list(todo):
            for h in range(3):
                z = (base(h, x, y), coordinate_product(NATIVE[h], v, w))
                if z not in source:
                    source.add(z)
                    todo.append(z)
    states = {(x, bit) for x in lattice
              for bit in ((0,) if x in owned else (0, 1) if x in neutral else (1,))}
    quotient = {(x, v): (x, int(3 in v)) for x, v in source}
    assert set(quotient.values()) == states

    def embed_base(x):
        return tuple((2 if x & (1 << i) else 0) if r & (1 << i)
                     else (1 if x & (1 << i) else 2) for i in range(size))

    assert len({embed_base(x) for x in lattice}) == len(lattice)
    entries = 0
    for h, (x, v), (y, w) in product(range(3), source, source):
        z = base(h, x, y)
        out = (z, coordinate_product(NATIVE[h], v, w))
        assert out in source
        assert quotient[out] == (z, int((3 in v or 3 in w) and z not in owned))
        assert embed_base(z) == coordinate_product(NATIVE[h], embed_base(x), embed_base(y))
        entries += 1
    return dict(name=name, lattice=len(lattice), doubled=len(states),
                neutral_fibers=len(neutral), edges=len(edges),
                native_coordinates=size + len(edges), source=len(source),
                checked_products=entries, reduced_lattice=len(set(theta.values())))


# Ideals of a two-point chain; then a three-point chain with two neutral ideals.
results = [check("chain3", (0, 1), 1, {0: 0, 1: 2, 3: 1}),
           check("chain4_two_neutrals", (0, 1, 3), 1, {0: 0, 1: 2, 3: 2, 7: 1})]
# N-shaped four-point poset a<A, a<B, b<B.
results.append(check("nine_state", (0, 0, 1, 3), 3, {0: 0, 3: 2, 15: 1}))
# Product with a two-element lattice: the extra coordinate is absent from
# every extension edge, so retaining the base coordinate is essential.
results.append(check("nine_state_times_chain2", (0, 0, 1, 3, 0), 3,
                     {x | bit: t for x, t in {0: 0, 3: 2, 15: 1}.items()
                      for bit in (0, 16)}))
print(json.dumps(dict(status="PASS", relation_products=relation_entries,
                      fixtures=results), indent=2))
