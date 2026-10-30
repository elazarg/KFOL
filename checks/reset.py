"""The reset calculus: canonical prerequisite tables and antimatroids.

Only variables and Reset occur in this fragment. Its equations are uniform
over every winner set with at least three roles. See the reset section of the paper for proofs.
"""

from collections import deque
from dataclasses import dataclass

from structure import Var


@dataclass(frozen=True)
class Reset:
    left: object
    right: object


@dataclass(frozen=True)
class Normal:
    root: int
    guards: tuple


def minimal(masks):
    result = []
    for mask in sorted(set(masks), key=lambda a: (a.bit_count(), a)):
        if not any(old & mask == old for old in result):
            result.append(mask)
    return tuple(result)


def normal(term, arity):
    if isinstance(term, Var):
        return Normal(term.index, tuple((0,) if j == term.index else () for j in range(arity)))
    first, second = normal(term.left, arity), normal(term.right, arity)
    return Normal(second.root, tuple(minimal(second.guards[j] +
        tuple(a | (1 << second.root) for a in first.guards[j])) for j in range(arity)))


def selected(form, ambiguous):
    return sum(1 << j for j, family in enumerate(form.guards)
               if any(a & ambiguous == a for a in family))


def evaluate(term, inputs):
    if isinstance(term, Var):
        return inputs[term.index]
    right = evaluate(term.right, inputs)
    return right if right.bit_count() == 1 else evaluate(term.left, inputs) | right


def realize(form, inputs):
    ambiguous = sum(1 << j for j, value in enumerate(inputs) if value.bit_count() > 1)
    outputs = selected(form, ambiguous)
    result = 0
    for j, value in enumerate(inputs):
        if outputs & (1 << j):
            result |= value
    return result


def compose(outer, inner):
    """Substitution on canonical tables; a guard sees each inner root."""
    arity = len(inner[0].guards)
    def transport(mask):
        return sum(1 << r for r in {inner[i].root for i in range(len(inner)) if mask & (1 << i)})
    return Normal(inner[outer.root].root, tuple(minimal(
        transport(a) | b
        for i, family in enumerate(outer.guards) for a in family for b in inner[i].guards[j])
        for j in range(arity)))


def order_trigger(form, trigger):
    """Greedy feasible order of a prerequisite set, or None."""
    reached = 0
    order = []
    while reached != trigger:
        candidates = selected(form, reached) & trigger & ~reached
        if not candidates:
            return None
        bit = candidates & -candidates
        reached |= bit
        order.append(bit.bit_length() - 1)
    return order


def admissible(form):
    """Exact polynomial realizability criterion for a prerequisite table."""
    arity = len(form.guards)
    full = (1 << arity) - 1
    if not 0 <= form.root < arity or form.guards[form.root] != (0,):
        return False
    for j, family in enumerate(form.guards):
        if minimal(family) != family:
            return False
        if j != form.root and 0 in family:
            return False
        for trigger in family:
            if trigger < 0 or trigger > full or trigger & (1 << j):
                return False
            # DSC completeness: each prerequisite itself enables its members.
            if any(trigger & (1 << k) and not any(b & trigger == b for b in form.guards[k])
                   for k in range(arity)):
                return False
    return True


def synthesize(form):
    if not admissible(form):
        raise ValueError("table is not realizable")
    paths = []
    for j, family in enumerate(form.guards):
        for trigger in family:
            path = Var(j)
            for i in reversed(order_trigger(form, trigger)):
                path = Reset(path, Var(i))
            paths.append(path)
    result = paths[0]
    for path in paths[1:]:
        # Same-root reset is exactly union of the two results.
        result = Reset(result, path)
    assert normal(result, len(form.guards)) == form
    return result


def feasible(form):
    support = selected(form, (1 << len(form.guards)) - 1)
    return frozenset(a for a in range(1 << len(form.guards))
                     if a & ~support == 0 and a & ~selected(form, a) == 0)


def basis(family, subset):
    result = 0
    for a in family:
        if a & subset == a:
            result |= a
    return result


def frontier(family, subset, arity):
    return sum(1 << j for j in range(arity)
               if basis(family, subset | (1 << j)) & (1 << j))


def product_families(first, second):
    return frozenset({0} | {a | b for a in first for b in second if b})


def antimatroids(arity):
    """Independent exhaustive family enumeration; practical through arity four."""
    full = (1 << arity) - 1
    if not arity:
        return [frozenset({0})]
    result = []
    # Empty set and the full support are mandatory.
    for flags in range(1 << (full - 1)):
        family = frozenset({0, full} | {a for a in range(1, full) if flags & (1 << (a - 1))})
        if not all(any(a ^ (1 << j) in family for j in range(arity) if a & (1 << j))
                   for a in family if a):
            continue
        if all(a | b in family for a in family for b in family):
            result.append(family)
    return result


def selector_closure(arity):
    """Independent reset closure on complete status tables."""
    generators = {tuple([1 << j] * (1 << arity)) for j in range(arity)}
    result = set(generators)
    queue = deque(generators)
    while queue:
        first = queue.popleft()
        for second in list(result):
            for a, b in ((first, second), (second, first)):
                value = tuple(a[s] | b[s] if s & b[0] else b[0] for s in range(1 << arity))
                if value not in result:
                    result.add(value)
                    queue.append(value)
    return result


def form_from_family(family, arity):
    roots = [j for j in range(arity) if 1 << j in family]
    if len(roots) != 1:
        raise ValueError("requires one feasible singleton")
    return Normal(roots[0], tuple(minimal(
        s for s in range(1 << arity) if frontier(family, s, arity) & (1 << j))
        for j in range(arity)))


def witness(first, second):
    """A countervaluation in the three-element chain, or None for equal tables."""
    arity = len(first.guards)
    if first == second:
        return None
    for outer, other in ((first, second), (second, first)):
        for j, family in enumerate(outer.guards):
            for trigger in family:
                if not any(b & trigger == b for b in other.guards[j]):
                    # {base} < {base,third} < {base,third,marker}.
                    inputs = tuple(7 if i == j else 3 if trigger & (1 << i) else 1
                                   for i in range(arity))
                    assert realize(first, inputs) != realize(second, inputs)
                    return inputs
    raise AssertionError("distinct minimal antichains must separate")
