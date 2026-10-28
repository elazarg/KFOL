"""The primary signature: owned choice plus internal role permutations.

The three-role unary classification and pair-test theorem have mathematical
proofs in symmetric.tex. Their constructions and finite checks live here.
"""

from collections import deque
from dataclasses import dataclass
from itertools import combinations, permutations, product

from structure import Choice, Var, Win, neutral_join, own


@dataclass(frozen=True)
class Rename:
    permutation: tuple
    child: object


def move(permutation, value):
    return sum(1 << permutation[i] for i in range(len(permutation)) if value & (1 << i))


def swap(count, first, second):
    result = list(range(count))
    result[first], result[second] = result[second], result[first]
    return tuple(result)


def evaluate(term, inputs):
    # Terms may reuse descriptions. Memoization avoids expanding their DAGs;
    # it changes no winner-set denotation and imposes no strategic sharing.
    memo = {}
    def go(t):
        key = id(t)
        if key not in memo:
            if isinstance(t, Win):
                result = 1 << t.role
            elif isinstance(t, Var):
                result = inputs[t.index]
            elif isinstance(t, Rename):
                result = move(t.permutation, go(t.child))
            else:
                result = own(t.role, go(t.left), go(t.right))
            memo[key] = result
        return memo[key]
    return go(term)


def constant(count, value):
    atoms = [Win(i) for i in range(count) if value & (1 << i)]
    result = atoms[0]
    for atom in atoms[1:]:
        result = neutral_join(result, atom)
    return result


def regular(count, extra, rows, base=None):
    """Earlier bare-signature synthesis, with substitution at the input."""
    base = Var(0) if base is None else base
    result = base
    for k in range(count):
        if extra & (1 << k):
            gate = neutral_join(base, Win(k))
            for i in range(count):
                if i != k and not rows[i] & (1 << k):
                    gate = Choice(i, gate, base)
            result = neutral_join(result, gate)
    return result


def reset_atoms(term, count, base=None):
    """On extensive inputs: fix each singleton, preserve ambiguous outputs."""
    base = Var(0) if base is None else base
    for i in range(count):
        term = Choice(i, term, base)
    return term


def pair_separator(count, pair):
    """Return two genuine terms differing exactly on the prescribed pair."""
    assert pair.bit_count() == 2
    k = next(i for i in range(count) if not pair & (1 << i))
    full = (1 << count) - 1
    x = Var(0)
    first = neutral_join(x, constant(count, full & ~(1 << k)))
    for i in range(count):
        if i != k and not pair & (1 << i):
            first = neutral_join(first, Rename(swap(count, i, k), x))
    return reset_atoms(first, count), reset_atoms(constant(count, full), count)


def provenance(term, statuses, count):
    """Constant plus permutation-relation images on a fixed status cell.

    A coefficient is a tuple of output masks, one per source role. Each
    nonzero coefficient is a union of permutation graphs. This is a sound
    representation; it is not claimed canonical at K>=4.
    """
    arity = len(statuses)
    zero = (0,) * count
    zeros = (zero,) * arity
    memo = {}
    def go(t):
        key = id(t)
        if key not in memo:
            if isinstance(t, Win):
                result = 1 << t.role, zeros
            elif isinstance(t, Var):
                status = statuses[t.index]
                if status < count:
                    result = 1 << status, zeros
                else:
                    coefficients = list(zeros)
                    coefficients[t.index] = tuple(1 << i for i in range(count))
                    result = 0, tuple(coefficients)
            elif isinstance(t, Rename):
                extra, coefficients = go(t.child)
                result = move(t.permutation, extra), tuple(
                    tuple(move(t.permutation, image) for image in coefficient)
                    for coefficient in coefficients)
            else:
                first, second = go(t.left), go(t.right)
                atom = 1 << t.role
                if any(extra == atom and all(c == zero for c in coeffs)
                       for extra, coeffs in (first, second)):
                    result = atom, zeros
                else:
                    result = first[0] | second[0], tuple(
                        tuple(a | b for a, b in zip(c, d))
                        for c, d in zip(first[1], second[1]))
            memo[key] = result
        return memo[key]
    return go(term)


def realize(form, inputs):
    extra, coefficients = form
    for value, coefficient in zip(inputs, coefficients):
        for i, image in enumerate(coefficient):
            if value & (1 << i):
                extra |= image
    return extra


def small_values(count):
    return tuple(s for s in range(1, 1 << count) if s.bit_count() <= 2)


def unary_closure_three():
    """Exact algebraic closure, independently of the proposed normal forms."""
    ps = [tuple(move(p, s) for s in range(1, 8)) for p in permutations(range(3))]
    functions = {tuple(range(1, 8))} | {(s,) * 7 for s in range(1, 8)}
    queue = deque(functions)
    while queue:
        first = queue.popleft()
        for p in ps:
            result = tuple(p[s - 1] for s in first)
            if result not in functions:
                functions.add(result)
                queue.append(result)
        for second in list(functions):
            for role in range(3):
                result = tuple(own(role, a, b) for a, b in zip(first, second))
                if result not in functions:
                    functions.add(result)
                    queue.append(result)
    return functions


def partial_permutations_three():
    for rank in range(4):
        for domain in combinations(range(3), rank):
            for image in permutations(range(3), rank):
                yield dict(zip(domain, image))


def ambiguity_action(partial, value):
    return (7 ^ sum(1 << j for j in partial.values())) | sum(
        1 << target for source, target in partial.items() if value & (1 << source))


def transformation(mapping, base):
    """Realize any map on singleton roles; preserve the full set."""
    representatives = {y: min(i for i, z in enumerate(mapping) if z == y) for y in set(mapping)}
    result = base
    for i, y in enumerate(mapping):
        representative = representatives[y]
        if i != representative:
            result = Choice(representative, result, Rename(swap(3, i, representative), result))
    p = {i: y for y, i in representatives.items()}
    unused_sources = [i for i in range(3) if i not in p]
    unused_targets = [i for i in range(3) if i not in p.values()]
    p.update(zip(unused_sources, unused_targets))
    return Rename(tuple(p[i] for i in range(3)), result)


def unary_template_three(partial, rows):
    """Actual term realizing any allowed partial-permutation/row normal form."""
    rank = len(partial)
    x = Var(0)
    extension = next(p for p in permutations(range(3))
                     if all(p[i] == j for i, j in partial.items()))
    y = Rename(extension, x)
    if rank >= 2:
        extra = 7 ^ sum(1 << j for j in partial.values())
        transported_rows = [0] * 3
        for i in range(3):
            transported_rows[extension[i]] = rows[i] & ~(1 << extension[i])
        return regular(3, extra, transported_rows, y)
    if rank == 1:
        source, target = next(iter(partial.items()))
        b, c = [i for i in range(3) if i != target]
        extra = (1 << b) | (1 << c)
        inflated = regular(3, extra, (0, 0, 0), y)
        desired = {extension[i]: rows[i] for i in range(3)}
        def selector(first, second):
            if first != second:
                return inflated if first == b else Rename(swap(3, b, c), inflated)
            return Choice(first, inflated, Rename(swap(3, b, c), inflated))
        selected = []
        for index in (0, 1):
            outputs = []
            for role in (b, c):
                available = [i for i in (b, c) if desired[role] & (1 << i)]
                outputs.append(available[min(index, len(available) - 1)])
            selected.append(selector(*outputs))
        combined = neutral_join(*selected)
        addition = rows[source] & ~(1 << target)
        final_rows = tuple(addition if i == target else 0 for i in range(3))
        return regular(3, addition, final_rows, combined)
    inflated = regular(3, 7, (0, 0, 0), x)
    selected = []
    for index in range(3):
        mapping = []
        for row in rows:
            available = [i for i in range(3) if row & (1 << i)]
            mapping.append(available[min(index, len(available) - 1)])
        selected.append(transformation(mapping, inflated))
    return neutral_join(neutral_join(selected[0], selected[1]), selected[2])
