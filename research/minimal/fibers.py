"""Exact two-permutation fibers and deterministic atomic synthesis.

The generic arguments are in general.tex. Exhaustions here are finite
cross-checks, independent of the proposed fiber family where stated.
"""

from collections import deque
from itertools import product

from structure import Choice, Var, Win, neutral_join, own
from symmetric import Rename, swap


def cycles(permutation):
    unseen = set(range(len(permutation)))
    result = []
    while unseen:
        first = min(unseen)
        cycle = [first]
        unseen.remove(first)
        next_role = permutation[first]
        while next_role != first:
            cycle.append(next_role)
            unseen.remove(next_role)
            next_role = permutation[next_role]
        result.append(tuple(cycle))
    return tuple(result)


def reset_relative(first, base, count):
    """Return base when it is atomic; otherwise the union of both operands."""
    result = neutral_join(first, base)
    for r in range(count):
        result = Choice(r, result, base)
    return result


def cycle_patterns(length):
    """0 = identity singleton; 1 = successor singleton; 2 = their pair."""
    if length == 1:
        return {(0,)}
    if length == 2:
        return set(product(range(3), repeat=2))
    result = set(product((0, 2), repeat=length)) | set(product((1, 2), repeat=length))
    for j in range(length):
        row = [2] * length
        row[j] = 0
        row[(j - 1) % length] = 1
        result.add(tuple(row))
    return result


def cycle_size(length):
    return 1 if length == 1 else 9 if length == 2 else (1 << (length + 1)) + length - 1


def local_template(pattern, cycle, first, second):
    """A local cycle term, given its two orientation generators."""
    if len(cycle) == 1:
        return first
    if 0 in pattern and 1 in pattern:
        index = pattern.index(0)
        assert pattern[(index - 1) % len(cycle)] == 1
        return Choice(cycle[index], first, second)
    result = neutral_join(first, second)
    for index, bit in enumerate(pattern):
        if bit < 2:
            role = cycle[index] if bit == 0 else cycle[(index + 1) % len(cycle)]
            result = Choice(role, result, first if bit == 0 else second)
    return result


def two_permutation_term(permutation, patterns):
    """Actual term for any permitted atomic table, with full ambiguity support."""
    count = len(permutation)
    components = cycles(permutation)
    assert all(tuple(pattern) in cycle_patterns(len(cycle))
               for cycle, pattern in zip(components, patterns))

    def build(index, leaf_perm):
        if index == len(components):
            return Rename(tuple(leaf_perm), Var(0))
        cycle = components[index]
        first = build(index + 1, leaf_perm)
        shifted = list(leaf_perm)
        for i in cycle:
            shifted[i] = permutation[i]
        second = build(index + 1, shifted)
        return local_template(patterns[index], cycle, first, second)

    result = build(0, list(range(count)))
    full_support = neutral_join(Var(0), Rename(tuple(permutation), Var(0)))
    return reset_relative(full_support, result, count)


def atomic_closure(permutation):
    """Independent closure on atomic rows of all allowed permutation leaves."""
    count = len(permutation)
    components = cycles(permutation)
    generators = set()
    for bits in product((0, 1), repeat=len(components)):
        p = list(range(count))
        for cycle, bit in zip(components, bits):
            if bit:
                for i in cycle:
                    p[i] = permutation[i]
        generators.add(tuple(1 << p[i] for i in range(count)))
    values = set(generators)
    queue = deque(generators)
    while queue:
        first = queue.popleft()
        for second in list(values):
            # Union is independently available as the derived three-owner term.
            extensions = [tuple(a | b for a, b in zip(first, second))]
            extensions += [tuple(own(r, a, b) for a, b in zip(first, second))
                           for r in range(count)]
            for value in extensions:
                if value not in values:
                    values.add(value)
                    queue.append(value)
    return values


def atomic_map_term(mapping, base):
    """Any unary map on singleton roles, using mergers then a permutation."""
    count = len(mapping)
    representatives = {y: min(i for i, z in enumerate(mapping) if z == y) for y in set(mapping)}
    result = base
    for i, y in enumerate(mapping):
        representative = representatives[y]
        if i != representative:
            result = Choice(representative, result, Rename(swap(count, i, representative), result))
    p = {i: y for y, i in representatives.items()}
    unused_sources = [i for i in range(count) if i not in p]
    unused_targets = [i for i in range(count) if i not in p.values()]
    p.update(zip(unused_sources, unused_targets))
    return Rename(tuple(p[i] for i in range(count)), result)


def two_valued_term(count, arity, table, first, second):
    """Truth-table synthesis by singleton tests and Boolean DNF on atomic inputs."""
    def balanced(pieces, owner, empty):
        if not pieces:
            return Win(empty)
        if len(pieces) == 1:
            return pieces[0]
        middle = len(pieces) // 2
        return Choice(owner, balanced(pieces[:middle], owner, empty),
                      balanced(pieces[middle:], owner, empty))
    clauses = []
    for inputs, value in zip(product(range(count), repeat=arity), table):
        if value != first:
            continue
        literals = []
        for j, label in enumerate(inputs):
            mapping = [second] * count
            mapping[label] = first
            literals.append(atomic_map_term(mapping, Var(j)))
        clauses.append(balanced(literals, second, first))
    return balanced(clauses, first, second)
