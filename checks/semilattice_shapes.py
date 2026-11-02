"""Unlabeled finite join semilattices, by adjoining a minimal element.

Removing any minimal element from a non-singleton join semilattice leaves
a join subalgebra. The new element's strict upper set is a nonempty upset
U; its join with x is the least element of U intersected with the upper
set of x. Enumerating those upsets therefore supplies every shape.
"""

from functools import lru_cache
from itertools import permutations, product


def canonical(table):
    size = len(table)
    upper = [[j for j in range(size) if table[i][j] == j] for i in range(size)]
    lower = [[j for j in range(size) if table[i][j] == i] for i in range(size)]
    colors = [(len(lower[i]), len(upper[i])) for i in range(size)]
    while True:
        ranks = {color: j for j, color in enumerate(sorted(set(colors)))}
        previous = [ranks[color] for color in colors]
        colors = [(previous[i], tuple(sorted(previous[j] for j in upper[i])),
                   tuple(sorted(previous[j] for j in lower[i]))) for i in range(size)]
        if len(set(colors)) == len(ranks):
            break
    # Isomorphisms preserve each color. Enumerate every permutation within
    # each color class; this is exact canonicalization, not a graph heuristic.
    groups = [[i for i, color in enumerate(colors) if color == value]
              for value in sorted(set(colors))]
    best = None
    for blocks in product(*(permutations(group) for group in groups)):
        order = sum(blocks, ())
        inverse = [0] * size
        for i, x in enumerate(order):
            inverse[x] = i
        flattened = tuple(inverse[table[x][y]] for x in order for y in order)
        if best is None or flattened < best:
            best = flattened
    return tuple(tuple(best[i * size:(i + 1) * size]) for i in range(size))


def extensions(table):
    size = len(table)
    upper = [sum(1 << j for j in range(size) if table[i][j] == j) for i in range(size)]
    for upset in range(1, 1 << size):
        if any(upper[i] & ~upset for i in range(size) if upset >> i & 1):
            continue
        joins = []
        for i in range(size):
            common = upper[i] & upset
            least = next((j for j in range(size) if common >> j & 1 and
                          not common & ~upper[j]), None)
            if least is None:
                break
            joins.append(least)
        else:
            yield (tuple(tuple(row) + (joins[i],) for i, row in enumerate(table))
                   + (tuple(joins) + (size,),))


@lru_cache(None)
def shapes(size):
    if size == 1:
        return (((0,),),)
    assert size > 1
    return tuple(sorted({canonical(extended) for table in shapes(size - 1)
                         for extended in extensions(table)}))


def automorphisms(table):
    """Every order automorphism, with invariant degree classes as a filter."""
    size = len(table)
    colors = [(sum(table[x][y] == x for y in range(size)),
               sum(table[x][y] == y for y in range(size))) for x in range(size)]
    groups = [[i for i, color in enumerate(colors) if color == value]
              for value in sorted(set(colors))]
    for blocks in product(*(permutations(group) for group in groups)):
        mapping = [0] * size
        for group, block in zip(groups, blocks):
            for x, y in zip(group, block):
                mapping[x] = y
        if all(mapping[table[x][y]] == table[mapping[x]][mapping[y]]
               for x, y in product(range(size), repeat=2)):
            yield tuple(mapping)
