"""Mixed blocking policies: exact small tables and least-guard separators.

The scalar and bit-parallel evaluators use native set operations. The
guard compiler uses positive membership tests, not those evaluators.
The experiments test written classifications; they are not their proofs.
"""
from dataclasses import dataclass
from itertools import product
from random import Random

from check_fragments import Valuations, cnfs, satisfiable
from fragments import denote, policy, reset, right_comb, var


@dataclass(frozen=True)
class Guard:
    source: int
    many: int = 0
    clear: tuple = ()             # (input index, blocking set)


def strengthen(g, many=0, clear=()):
    many |= g.many
    tests = set(g.clear + clear)
    tests = {(i, d) for i, d in tests if i != g.source and not many & (1 << i)}
    tests = {(i, d) for i, d in tests
             if not any(i == j and d != e and d & e == d for j, e in tests)}
    return Guard(g.source, many, tuple(sorted(tests)))


def covers(weak, strong):
    return (weak.source == strong.source and weak.many & strong.many == weak.many
            and all(i == strong.source or strong.many & (1 << i)
                    or any(i == j and d & e == d for j, e in strong.clear)
                    for i, d in weak.clear))


def compact(guards):
    unique = set(guards)
    return tuple(sorted((g for g in unique if not any(
        h != g and covers(h, g) for h in unique)),
        key=lambda g: (g.source, g.many, g.clear)))


def compile_guards(term, roles, observer=None, cover_union=False):
    """None retains common tests; an observer removes trivial endpoint tests."""
    if term.op == 'var':
        return term.args[0], (Guard(term.args[0]),)
    if term.op == 'reset':
        _, left = compile_guards(term.args[0], roles, observer, cover_union)
        root, right = compile_guards(term.args[1], roles, observer, cover_union)
        return root, compact(right + tuple(strengthen(g, 1 << root) for g in left))
    assert term.op == 'policy'
    d, x, y, z = term.args
    rx, gx = compile_guards(x, roles, observer, cover_union)
    ry, gy = compile_guards(y, roles, observer, cover_union)
    _, gz = compile_guards(z, roles, observer, cover_union)
    many, clear = 1 << rx, ()
    if observer is not None:
        universe = ((1 << roles)-1) ^ (1 << observer)
        d &= universe
        if d == universe:
            many |= 1 << ry
        elif d:
            clear = ((ry, d),)
    else:
        clear = ((ry, d),)
    last = [strengthen(g, many, clear) for g in gz]
    if cover_union:
        # A newly formed pair of tests at ry forces ambiguity or contains
        # the observer. The latter is absorbed by gy's unguarded root leaf.
        for j, g in enumerate(last):
            union = 0
            for i, e in g.clear:
                if i == ry:
                    union |= e
            if union == (1 << roles)-1:
                last[j] = strengthen(g, 1 << ry)
    return rx, compact(gx + tuple(strengthen(g, 1 << rx) for g in gy) + tuple(last))


def implies(left, right):
    return all(any(covers(h, g) for h in right) for g in left)


def equal(left, right):
    return implies(left, right) and implies(right, left)


def guard_value(g, values, observer):
    return bool(values[g.source] & (1 << observer)) and all(
        values[i].bit_count() > 1 for i in range(len(values)) if g.many & (1 << i)
    ) and all(values[i].bit_count() > 1 or values[i] == 1 << observer
              or not values[i] & d for i, d in g.clear)


def narrowest(g, policies, roles, observer, arity):
    """Least flags when the atomic passing patterns have the required minimum."""
    others = [r for r in range(roles) if r != observer]
    values = []
    for i in range(arity):
        if i == g.source:
            values.append((1 << observer) | ((1 << others[0]) if g.many & (1 << i) else 0))
        elif g.many & (1 << i):
            values.append((1 << others[0]) | (1 << others[1]))
        else:
            required = [d for j, d in g.clear if j == i]
            candidates = [r for r in others if all(not d & (1 << r) for d in required)]
            assert candidates
            def pattern(r):
                return {d for d in policies if not d & (1 << r)}
            common = set.intersection(*(pattern(r) for r in candidates))
            r = next(r for r in candidates if pattern(r) == common)
            values.append(1 << r)
    return tuple(values)


def arbitrary(rng, depth, arity, policies):
    if not depth or rng.randrange(5) == 0:
        return var(rng.randrange(arity))
    if rng.randrange(3) == 0:
        return reset(*(arbitrary(rng, depth-1, arity, policies) for _ in range(2)))
    return policy(rng.choice(policies),
                  *(arbitrary(rng, depth-1, arity, policies) for _ in range(3)))


def check_tables():
    rng = Random(1107)
    # Endpoint tests are included in every nested configuration.
    configurations = [(k, tuple((1 << j)-1 for j in range(k+1)), None)
                      for k in (3, 4, 5)]
    configurations += [(5, (7, 9), 1), (5, (7, 11), 0),
                       (5, (3, 13), 2), (5, (3, 5), 3),
                       (4, (3, 13), 2), (4, (7, 9), 1), (4, (7, 13), 0),
                       (5, (7, 25), 1)]
    for roles, policies, generic in configurations:
        arity = 3
        terms = [var(i) for i in range(arity)] + [
            arbitrary(rng, 3, arity, policies) for _ in range(67)]
        tables, cache = Valuations(roles, arity), {}
        rows = [tables.evaluate(t, cache) for t in terms]
        observers = range(roles) if generic is None else (generic,)
        for k in observers:
            cover_union = generic is not None and policies[0] | policies[1] == (1 << roles)-1
            forms = [compile_guards(t, roles, None if generic is not None else k, cover_union)[1]
                     for t in terms]
            effective = tuple(d & ~ (1 << k) for d in policies)
            proper = tuple(d for d in effective if 0 < d < ((1 << roles)-1) ^ (1 << k))
            for i, j in product(range(len(terms)), repeat=2):
                expected = rows[i][k] == rows[j][k] if generic is None else rows[i] == rows[j]
                assert equal(forms[i], forms[j]) == expected, (roles, policies, k, i, j)
                if not implies(forms[i], forms[j]):
                    g = next(g for g in forms[i] if not any(covers(h, g) for h in forms[j]))
                    values = narrowest(g, policies if generic is not None else proper,
                                       roles, k, arity)
                    assert guard_value(g, values, k)
                    assert not any(guard_value(h, values, k) for h in forms[j])
                    assert denote(terms[i], values) & (1 << k)
                    assert not denote(terms[j], values) & (1 << k)
            for i, term in enumerate(terms):
                for _ in range(12):
                    values = tuple(rng.randrange(1, 1 << roles) for _ in range(arity))
                    assert bool(denote(term, values) & (1 << k)) == any(
                        guard_value(g, values, k) for g in forms[i])
                    index = sum((v-1) * tables.base**(arity-j-1) for j, v in enumerate(values))
                    assert sum(((r >> index) & 1) << a for a, r in enumerate(rows[i])) == denote(term, values)
        print(f"Mixed policies: K={roles}, D={policies}, 70 terms / 4900 ordered pairs; "
              f"exact tables and least-guard separators passed ({'all observers' if generic is None else 'complete observer '+str(generic)}).",
              flush=True)
    # With three regions on three roles no observer is complete for that
    # comparison, but the covered-union normalization remains semantically exact.
    terms = [arbitrary(rng, 4, 3, (3, 5)) for _ in range(100)]
    for term in terms:
        form = compile_guards(term, 3, cover_union=True)[1]
        for values in product(range(1, 8), repeat=3):
            for k in range(3):
                assert bool(denote(term, values) & (1 << k)) == any(
                    guard_value(g, values, k) for g in form)
    print("Covered-union normalization: 100 depth-four terms, all three-role valuations and observers.", flush=True)


def reduction(cnf, variables, positive, negative):
    z, c = var(variables), var(variables+1)
    base = right_comb([var(i) for i in range(variables)], z)
    branches = []
    for clause in cnf:
        branch = c
        for i, sign in reversed(clause):
            branch = (positive if sign else negative)(z, var(i), branch)
        branches.append(branch)
    rhs = right_comb(branches, base)
    return reset(c, rhs), rhs


def calibrated_reduction(cnf, variables, outside):
    """Pin the only possible fresh marker to the shared blocking atom.

    D={0,1}, E={0,2}; optional fourth role 3 is outside both.
    Calibration inputs force patterns B, C, and (when present) T.
    """
    z, c = var(variables), var(variables+1)
    u, v = var(variables+2), var(variables+3)
    calibration = [u, v]
    tests = [(5, u), (3, v)]
    if outside:
        w = var(variables+4)
        calibration.append(w)
        tests += [(3, w), (5, w)]
    base = right_comb([var(i) for i in range(variables)] + calibration, z)
    branches = []
    for clause in cnf:
        branch = c
        for i, sign in reversed(clause):
            branch = policy(3 if sign else 5, z, var(i), branch)
        branches.append(branch)
    bad = [policy(3, z, u, c), policy(5, z, v, c)]
    bad += [reset(c, a) for a in calibration]
    rhs = right_comb(branches + bad, base)
    lhs = c
    for d, a in reversed(tests):
        lhs = policy(d, z, a, lhs)
    return reset(lhs, rhs), rhs


def check_reductions():
    for roles, d, e, observer, n in ((3, 1, 2, None, 2), (3, 3, 5, 0, 2),
                                     (4, 3, 5, 0, 2), (5, 7, 9, 0, 1)):
        tables, cache = Valuations(roles, n+2), {}
        for cnf in cnfs(n):
            pair = reduction(cnf, n, lambda *t: policy(d, *t), lambda *t: policy(e, *t))
            rows = [tables.evaluate(t, cache) for t in pair]
            valid = rows[0] == rows[1] if observer is None else rows[0][observer] == rows[1][observer]
            assert valid == (not satisfiable(cnf, n)), (roles, d, e, observer, cnf)
            if observer is not None:
                # The player quotient also records every nonobserver atom.
                # Equal roots make all these extra coordinates agree.
                for r in range(roles):
                    if r != observer:
                        def atomic(table):
                            others = 0
                            for s, row in enumerate(table):
                                if s != r:
                                    others |= row
                            return table[r] & ~others
                        assert atomic(rows[0]) == atomic(rows[1])
        print(f"Mixed reductions: K={roles}, D={d}, E={e}, observer={observer}; "
              f"{len(cnfs(n))} CNFs, all {tables.count} valuations each.", flush=True)
    # Three overlapping sets define a nonempty policy disjoint from the third.
    tables, cache = Valuations(3, 4), {}
    intersection = lambda x, y, z: reset(policy(3, x, y, z), policy(5, x, y, z))
    for cnf in cnfs(2):
        rows = [tables.evaluate(t, cache) for t in reduction(
            cnf, 2, intersection, lambda *t: policy(6, *t))]
        assert (rows[0] == rows[1]) == (not satisfiable(cnf, 2))
    # An observationally valid equation can fail as a full equation.
    contradiction = (((0, True),), ((0, False),))
    left, right = reduction(contradiction, 1, lambda *t: policy(7, *t), lambda *t: policy(9, *t))
    assert denote(left, (1, 10, 16)) == 27 and denote(right, (1, 10, 16)) == 11
    print("Three pairwise-overlapping policies: all 604 two-variable CNFs passed; "
          "full equality / hard-observer distinction witnessed.", flush=True)


def check_calibration():
    for roles, n, outside in ((3, 2, False), (4, 1, True)):
        tables = Valuations(roles, n+4+int(outside))
        for cnf in cnfs(n):
            tables.check(calibrated_reduction(cnf, n, outside), not satisfiable(cnf, n))
        print(f"Calibrated overlapping policies: K={roles}, {len(cnfs(n))} CNFs; "
              f"all {tables.count} winner-set valuations each.", flush=True)
    # Duplicating any one of the four regions provides a complete observer.
    # The contradictory calibrated equation is then no longer fully valid.
    contradiction = (((0, True),), ((0, False),))
    left, right = calibrated_reduction(contradiction, 1, True)
    # Fixed labels 3,5 duplicate T at the new role 4. Calibrators stay 1,2,3;
    # the fresh marker is the duplicate outsider, with y the shared blocker.
    values = (1, 6, 16, 2, 4, 8)
    assert denote(left, values) != denote(right, values)
    print("Duplicating a four-region pattern destroys the calibrated UNSAT identity.")


if __name__ == '__main__':
    check_tables()
    check_reductions()
    check_calibration()
