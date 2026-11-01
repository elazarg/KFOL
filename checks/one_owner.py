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


def well_formed(form):
    """Necessary canonical shape; realizability additionally needs saturation."""
    arity = len(form.other)
    if not 0 <= form.root < arity or form.other[form.root] != ((0, 0),):
        return False
    full = (1 << arity) - 1
    for j, family in enumerate(form.other):
        if any(m < 0 or n < 0 or (m | n) & ~full for m, n in family):
            return False
        if normalize_other(family, j) != family:
            return False
        if j != form.root and any(m & (1 << j) or not m & (1 << form.root)
                                  for m, _ in family):
            return False
    return True


def guard_path(form, source, guard, owner=0):
    """Synthesize one safe spine covering guard, or return None.

    The hole always has the table's root. An excursion through w makes w
    ambiguous; H can also require its companion z not to be the owner atom.
    Every retained contribution must already be permitted by the target.
    """
    from fragments import h, reset, var

    root = form.root
    if source == root:
        return var(root)
    goal_m, goal_n = guard
    permitted = goal_m | goal_n | (1 << source)
    arity = len(form.other)

    def allowed(j, m, n):
        n &= ~m & ~(1 << j)
        return any(weaker(g, (m, n)) for g in form.other[j])

    # Frames are recorded from outside to inside, with one hole each.
    frames = [('reset', root)]
    m, n = 1 << root, 0
    while True:
        changed = False
        for w in range(arity):
            if not goal_m & (1 << w):
                continue
            for z in range(arity):
                if not permitted & (1 << z):
                    continue
                tests = n | (1 << w) | (1 << z)
                next_m = m | (1 << w)
                next_n = tests & ~next_m
                if (next_m, next_n) == (m, n):
                    continue
                if allowed(w, m, tests) and allowed(z, m, tests):
                    frames.extend([('h', root, z), ('reset', w)])
                    m, n = next_m, next_n
                    changed = True
        if not changed:
            break

    if allowed(source, m, n):
        frames.append(('reset', root))
    else:
        for z in range(arity):
            tests = n | (1 << source) | (1 << z)
            if permitted & (1 << z) and allowed(source, m, tests) and allowed(z, m, tests):
                frames.append(('h', root, z))
                break
        else:
            return None
    term = var(source)
    for frame in reversed(frames):
        term = (reset(term, var(frame[1])) if frame[0] == 'reset' else
                h(owner, var(frame[1]), term, var(frame[2])))
    return term


def synthesize(form, owner=0):
    """Polynomial recognition and O(arity * guards) native-tree synthesis."""
    from fragments import reset, var

    if not well_formed(form):
        raise ValueError("table is not canonical")
    result = var(form.root)
    for source, family in enumerate(form.other):
        for guard in family:
            path = guard_path(form, source, guard, owner)
            if path is None:
                raise ValueError("table is not realizable")
            result = reset(path, result)
    return result


def admissible(form):
    if not well_formed(form):
        return False
    return all(guard_path(form, j, guard) is not None
               for j, family in enumerate(form.other) for guard in family)


def compose(outer, inner):
    """Substitution on canonical one-owner tables."""
    if len(inner) != len(outer.other) or not inner:
        raise ValueError("one inner table is required for each outer input")
    arity = len(inner[0].other)
    if any(len(form.other) != arity for form in inner):
        raise ValueError("inner tables must have a common arity")

    def roots(mask):
        result = 0
        for i, form in enumerate(inner):
            if mask & (1 << i):
                result |= 1 << form.root
        return result

    return Normal(inner[outer.root].root, tuple(normalize_other(tuple(
        (c | roots(a), d | roots(b))
        for i, family in enumerate(outer.other) for a, b in family
        for c, d in inner[i].other[j]), j) for j in range(arity)))
