"""Canonical guard semantics for reset and one fixed owner's H operation.

The native AST and set evaluator are shared with fragments.py. Owner-output
guards require ambiguity; other-output guards may also require not being
the owner's singleton. Marker feasibility removes the latter requirement
from the source variable itself. No constants, union, or other owners occur.
"""

from dataclasses import dataclass

from reset import minimal


@dataclass(frozen=True)
class Normal:
    root: int
    other: tuple

    @property
    def owner(self):
        return tuple(minimal(m for m, _ in family) for family in self.other)


@dataclass(frozen=True)
class Observed:
    root: int
    guards: tuple


def weaker(first, second):
    """A guard is weaker when every assignment satisfying second satisfies it."""
    m, n = first
    other_m, other_n = second
    return m & other_m == m and n & (other_m | other_n) == n


def normalize_other(guards, source):
    guards = {(m, n & ~m & ~(1 << source)) for m, n in guards}
    return tuple(sorted(guard for guard in guards
                        if not any(other != guard and weaker(other, guard)
                                   for other in guards)))


def normal(term, owner, arity):
    # Numbered roles never equal None: this compiles the outsider's single
    # table. The owner's table is recovered by forgetting all negative tests.
    form = observation_normal(term, None, owner, arity)
    return Normal(form.root, form.guards)


def realize(form, inputs, owner):
    ambiguous = sum(1 << j for j, value in enumerate(inputs) if value.bit_count() > 1)
    not_owner = sum(1 << j for j, value in enumerate(inputs) if value != 1 << owner)
    result = 0
    for j, value in enumerate(inputs):
        if any(m & ambiguous == m for m in form.owner[j]):
            result |= value & (1 << owner)
        if any(m & ambiguous == m and n & not_owner == n for m, n in form.other[j]):
            result |= value & ~(1 << owner)
    return result


def observation_normal(term, observer, other, arity):
    """An observer may have its own H and one other owner's H available."""
    assert observer != other
    if term.op == 'var':
        j = term.args[0]
        return Observed(j, tuple(((0, 0),) if i == j else () for i in range(arity)))
    if term.op == 'reset':
        left, right = (observation_normal(t, observer, other, arity) for t in term.args)
        gate = 1 << right.root
        return Observed(right.root, tuple(normalize_other(right.guards[j] +
            tuple((m | gate, n) for m, n in left.guards[j]), j) for j in range(arity)))
    assert term.op == 'h' and term.args[0] in (observer, other)
    root, left, right = (observation_normal(t, observer, other, arity) for t in term.args[1:])
    m_gate = 1 << root.root
    n_gate = 0 if term.args[0] == observer else (1 << left.root) | (1 << right.root)
    return Observed(root.root, tuple(normalize_other(root.guards[j] +
        tuple((m | m_gate, n | n_gate) for m, n in left.guards[j] + right.guards[j]), j)
        for j in range(arity)))


def observe(form, inputs, observer, other):
    ambiguous = sum(1 << j for j, value in enumerate(inputs) if value.bit_count() > 1)
    outside = sum(1 << j for j, value in enumerate(inputs) if value != 1 << other)
    return any(value & (1 << observer) and any(
        m & ambiguous == m and n & outside == n for m, n in form.guards[j])
        for j, value in enumerate(inputs))


def observation_countervaluation(left, right, observer, other, count=3):
    assert observer != other and count >= 3
    background = next(i for i in range(count) if i not in (observer, other))
    k, a, b = 1 << observer, 1 << other, 1 << background
    for first, second in ((left, right), (right, left)):
        for j, family in enumerate(first.guards):
            for m, n in family:
                if any(weaker(guard, (m, n)) for guard in second.guards[j]):
                    continue
                return tuple((k | a if m & (1 << i) else k) if i == j else
                             (a | b if m & (1 << i) else b if n & (1 << i) else a)
                             for i in range(len(first.guards)))
    assert left == right
    return None


def countervaluation(left, right, owner=0, count=3):
    """One outsider table supplies every full winner-set separator."""
    assert count >= 3
    b = next(i for i in range(count) if i != owner)
    return observation_countervaluation(Observed(left.root, left.other),
                                        Observed(right.root, right.other), b, owner, count)
