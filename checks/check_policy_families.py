"""Finite checks of the arbitrary-family pattern criterion and native reductions.

Passing patterns and guard compilation are independent of the bit-parallel
winner-set evaluator. These checks supplement the written general proof.
"""
from itertools import combinations, product
from random import Random

from check_fragments import Valuations, cnfs, satisfiable
from check_mixed_policies import (Guard, arbitrary, compact, covers, equal,
                                 guard_value, implies, narrowest)
from fragments import denote, policy, reset, right_comb, var


def patterns(roles, policies):
    return tuple(frozenset(j for j, d in enumerate(policies) if not d & (1 << r))
                 for r in range(roles))


def classify(roles, policies):
    pats = patterns(roles, policies)
    distinct = set(pats)
    closed = all(p & q in distinct for p in pats for q in pats)
    chain = all(p <= q or q <= p for p in pats for q in pats)
    duplicate = next((r for r in range(roles) if pats.count(pats[r]) > 1), None)
    return closed and (chain or duplicate is not None), duplicate


def strengthen(g, roles, many=0, clear=()):
    many |= g.many
    unions = {}
    for i, d in g.clear + clear:
        unions[i] = unions.get(i, 0) | d
    for i, d in unions.items():
        if i != g.source and d == (1 << roles)-1:
            many |= 1 << i
    tests = tuple(sorted((i, d) for i, d in unions.items()
                         if d and i != g.source and not many & (1 << i)))
    return Guard(g.source, many, tests)


def compile_guards(term, roles):
    if term.op == 'var':
        return term.args[0], (Guard(term.args[0]),)
    if term.op == 'reset':
        _, left = compile_guards(term.args[0], roles)
        root, right = compile_guards(term.args[1], roles)
        return root, compact(right + tuple(strengthen(g, roles, 1 << root) for g in left))
    d, x, y, z = term.args
    rx, gx = compile_guards(x, roles)
    ry, gy = compile_guards(y, roles)
    _, gz = compile_guards(z, roles)
    return rx, compact(gx + tuple(strengthen(g, roles, 1 << rx) for g in gy)
                       + tuple(strengthen(g, roles, 1 << rx, ((ry, d),)) for g in gz))


def obstruction(roles, policies):
    """Return the missing meet, optional unique observer, and two minimal groups."""
    pats = patterns(roles, policies)
    distinct = set(pats)
    for p, q in combinations(sorted(distinct, key=lambda p: tuple(sorted(p))), 2):
        meet = p & q
        if meet not in distinct:
            observer = None
        elif p != meet and q != meet and len(distinct) == roles:
            observer = pats.index(meet)
        else:
            continue
        allowed = {s for r, s in enumerate(pats) if r != observer and meet <= s}
        minimal = sorted((s for s in allowed if not any(t < s for t in allowed)),
                         key=lambda p: tuple(sorted(p)))
        assert len(minimal) >= 2
        return meet, observer, (minimal[:1], minimal[1:])
    raise AssertionError('No obstruction for a classified hard family')


def derived_policy(group, meet, policies):
    """OR of conjunctions of passing tests, as a native term macro."""
    def operation(x, y, z):
        branches = []
        for pat in group:
            branch = z
            for j in sorted(pat - meet):
                branch = policy(policies[j], x, y, branch)
            branches.append(branch)
        result = branches[0]
        for branch in branches[1:]:
            result = reset(result, branch)
        return result
    return operation


def reduction(cnf, variables, roles, policies):
    meet, observer, groups = obstruction(roles, policies)
    pos, neg = (derived_policy(g, meet, policies) for g in groups)
    z, marker = var(variables), var(variables+1)
    calibration = [] if observer is None else [r for r in range(roles) if r != observer]
    inputs = [var(variables+2+i) for i in range(len(calibration))]
    baseline = right_comb([var(i) for i in range(variables)] + inputs, z)
    branches = []
    for clause in cnf:
        branch = marker
        for i, sign in reversed(clause):
            branch = (pos if sign else neg)(z, var(i), branch)
        branches.append(branch)
    head = marker
    for i in range(variables):
        for j in sorted(meet):
            head = policy(policies[j], z, var(i), head)
    for r, inp in zip(calibration, inputs):
        branches.append(reset(marker, inp))
        for d in policies:
            if d & (1 << r):
                branches.append(policy(d, z, inp, marker))
            else:
                head = policy(d, z, inp, head)
    rhs = right_comb(branches, baseline)
    return reset(head, rhs), rhs, variables+2+len(calibration)


def check():
    rng = Random(1109)
    configurations = [(3, tuple(d for d in range(1, 7) if mask & (1 << (d-1))))
                      for mask in range(64)]
    configurations += [(4, tuple(rng.sample(range(1, 15), rng.randrange(3, 8))))
                       for _ in range(40)]
    configurations += [(4, (13, 11, 7))]  # three minimal patterns after calibration
    # Meet-closed passing patterns 000, 001, 010, 011, 100, with a duplicate.
    configurations += [(6, (0b110101, 0b110011, 0b001111)),
                       (5, (0b10101, 0b10011, 0b01111)),
                       (5, (29, 27, 23)),  # a repeated least pattern
                       (5, (3, 27, 7))]    # every pair easy, triple hard
    easy_count = hard_count = 0
    for roles, policies in configurations:
        easy, observer = classify(roles, policies)
        if easy and observer is not None:
            terms = [var(i) for i in range(3)] + [arbitrary(rng, 3, 3, policies)
                                                 for _ in range(37)] if policies else [var(i) for i in range(3)]
            tables, cache = Valuations(roles, 3), {}
            rows = [tables.evaluate(t, cache) for t in terms]
            forms = [compile_guards(t, roles)[1] for t in terms]
            for i, j in product(range(len(terms)), repeat=2):
                assert equal(forms[i], forms[j]) == (rows[i] == rows[j]), (roles, policies, i, j)
                if not implies(forms[i], forms[j]):
                    g = next(g for g in forms[i] if not any(covers(h, g) for h in forms[j]))
                    values = narrowest(g, policies, roles, observer, 3)
                    assert denote(terms[i], values) & (1 << observer)
                    assert not denote(terms[j], values) & (1 << observer)
            easy_count += 1
        elif not easy:
            # All one-variable CNFs on every mixed valuation, with actual
            # expansions using only the supplied native policy symbols.
            sample = cnfs(1) if roles == 3 or policies in ((3, 27, 7), (13, 11, 7)) else ((), ((),), (((0, True),), ((0, False),)))
            cache_by_arity = {}
            for formula in sample:
                left, right, arity = reduction(formula, 1, roles, policies)
                if ((1 << roles)-1) ** arity > 12_000_000:
                    # Exhaustive tables would have (2^K-1)^(K+2) rows.
                    # Check UNSAT pointwise and SAT with an explicit marker.
                    if not satisfiable(formula, 1):
                        for _ in range(200):
                            values = tuple(rng.randrange(1, 1 << roles) for _ in range(arity))
                            assert denote(left, values) == denote(right, values)
                    else:
                        meet, k, groups = obstruction(roles, policies)
                        pats = patterns(roles, policies)
                        a = next(r for r in range(roles) if pats[r] == groups[1][0])
                        b = next(r for r in range(roles) if pats[r] == groups[0][0])
                        if k is None:
                            k = next(r for r in range(roles) if r not in (a, b))
                            calibration = []
                        else:
                            calibration = [1 << r for r in range(roles) if r != k]
                        found = False
                        for truth in (False, True):
                            if all(any(truth == sign for _, sign in clause) for clause in formula):
                                values = (1 << (a if truth else b), (1 << a) | (1 << b), 1 << k, *calibration)
                                assert denote(left, values) != denote(right, values)
                                found = True
                        assert found
                    continue
                if arity not in cache_by_arity:
                    cache_by_arity[arity] = (Valuations(roles, arity), {})
                tables, cache = cache_by_arity[arity]
                assert (tables.evaluate(left, cache) == tables.evaluate(right, cache)) == (not satisfiable(formula, 1)), (roles, policies, formula)
            hard_count += 1
        # General union-of-tests normalization is exact even in hard cases.
        if policies:
            for _ in range(8):
                term = arbitrary(rng, 4, 3, policies)
                form = compile_guards(term, roles)[1]
                for _ in range(20):
                    values = tuple(rng.randrange(1, 1 << roles) for _ in range(3))
                    for k in range(roles):
                        assert bool(denote(term, values) & (1 << k)) == any(guard_value(g, values, k) for g in form)
    for pair in combinations((3, 27, 7), 2):
        assert classify(5, pair)[0]
    assert not classify(5, (3, 27, 7))[0]
    print(f'Policy families: {easy_count} easy and {hard_count} hard configurations; exact tables, separators, and expanded native reductions passed.', flush=True)


if __name__ == '__main__':
    check()
