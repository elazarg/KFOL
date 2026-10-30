"""Exact general-K quotient of unary terms on ambiguous inputs.

Rows are output coordinates. The full mask denotes constant presence;
every other row is a nonempty source set of size at most K-2. The matching
criterion checks realizability, not just well-formedness. See the intrinsic-core and complexity sections of the paper.
"""

from itertools import permutations, product

from structure import Var, Win, neutral_join
from symmetric import Rename


def apply(rows, value):
    full = (1 << len(rows)) - 1
    return sum(1 << k for k, row in enumerate(rows)
               if row == full or row & value)


def compose(outer, inner):
    """Composition outer after inner, in canonical row form."""
    count = len(outer)
    full = (1 << count) - 1
    result = []
    for row in outer:
        sources = 0
        if row == full:
            sources = full
        else:
            for i in range(count):
                if row & (1 << i):
                    sources |= inner[i]
        result.append(full if sources.bit_count() >= count - 1 else sources)
    return tuple(result)


def matching(rows, forced=None):
    """Perfect matching of the allowed graph, optionally containing an edge.

    A forced edge is (source, target). Constant rows allow every source.
    The augmenting-path algorithm keeps the forced source locked.
    """
    count = len(rows)
    source_to_target = [-1] * count
    locked = -1
    if forced is not None:
        locked, target = forced
        if not rows[target] & (1 << locked):
            return None
        source_to_target[locked] = target

    def augment(target, seen):
        for source in range(count):
            if source == locked or source in seen or not rows[target] & (1 << source):
                continue
            seen.add(source)
            previous = source_to_target[source]
            if previous == -1 or augment(previous, seen):
                source_to_target[source] = target
                return True
        return False

    for target in range(count):
        if forced is not None and target == forced[1]:
            continue
        if not augment(target, set()):
            return None
    return tuple(source_to_target)


def witnesses(rows):
    """Return generating permutations, or None if the rows are unrealizable."""
    count = len(rows)
    full = (1 << count) - 1
    if any(not row or row > full or
           (row != full and row.bit_count() > count - 2) for row in rows):
        return None
    result = set()
    for target, row in enumerate(rows):
        if row == full:
            continue
        for source in range(count):
            if row & (1 << source):
                p = matching(rows, (source, target))
                if p is None:
                    return None
                result.add(p)
    return tuple(sorted(result)) if result else (tuple(range(count)),)


def canonical(extra, relation):
    """Input relation uses output-to-source row masks before saturation."""
    count = len(relation)
    full = (1 << count) - 1
    return tuple(full if extra & (1 << k) or row.bit_count() >= count - 1
                 else row for k, row in enumerate(relation))


def all_rows(count):
    full = (1 << count) - 1
    choices = [row for row in range(1, full + 1)
               if row == full or row.bit_count() <= count - 2]
    return {rows for rows in product(choices, repeat=count) if witnesses(rows) is not None}


def factorpower(count):
    """Independent finite closure of nonempty permutation unions."""
    generators = []
    for p in permutations(range(count)):
        rows = [0] * count
        for source, target in enumerate(p):
            rows[target] |= 1 << source
        generators.append(tuple(rows))
    result = set(generators)
    queue = list(result)
    for relation in queue:
        for p in generators:
            union = tuple(a | b for a, b in zip(relation, p))
            if union not in result:
                result.add(union)
                queue.append(union)
    return result


def synthesize(rows):
    """An actual owned-choice/role-switch term realizing the ambiguity action."""
    ps = witnesses(rows)
    if ps is None:
        raise ValueError("unrealizable rows")
    count = len(rows)
    full = (1 << count) - 1
    pieces = [Rename(p, Var(0)) for p in ps]
    pieces.extend(Win(k) for k, row in enumerate(rows) if row == full)
    # Balanced joins keep expansion to ordinary tree syntax polynomial.
    def combine(terms):
        if len(terms) == 1:
            return terms[0]
        middle = len(terms) // 2
        return neutral_join(combine(terms[:middle]), combine(terms[middle:]))
    return combine(pieces)
