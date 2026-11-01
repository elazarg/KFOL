"""Actual two-owner terms versus policy-independent guard comparison.

The scalar evaluator uses the original two owned choices. Guard tables
do not use an owned-choice expansion or enumerate equilibrium profiles.
"""
from itertools import product
from random import Random

from fragments import denote, g, policy, reset, var
from one_owner import Observed, normalize_other, weaker


def normal(term, arity):
    if term.op == 'var':
        j = term.args[0]
        return Observed(j, tuple(((0, 0),) if i == j else () for i in range(arity)))
    if term.op == 'reset':
        left, right = (normal(t, arity) for t in term.args)
        return Observed(right.root, tuple(normalize_other(right.guards[j] +
            tuple((m | 1 << right.root, n) for m, n in left.guards[j]), j)
            for j in range(arity)))
    root, left, right = (normal(t, arity) for t in term.args[-3:])
    return Observed(root.root, tuple(normalize_other(root.guards[j] +
        tuple((m | 1 << root.root, n) for m, n in left.guards[j]) +
        tuple((m | 1 << root.root, n | 1 << left.root) for m, n in right.guards[j]), j)
        for j in range(arity)))


def observe(form, values, blockers, observer):
    many = sum(1 << j for j, value in enumerate(values) if value.bit_count() > 1)
    clear = sum(1 << j for j, value in enumerate(values)
                if value.bit_count() > 1 or value == 1 << observer or not value & blockers)
    return any(value & 1 << observer and any(m & many == m and n & clear == n
               for m, n in form.guards[j]) for j, value in enumerate(values))


def separator(left, right, blockers, count):
    r = next(i for i in range(count) if blockers & 1 << i)
    c = next(i for i in range(count) if not blockers & 1 << i)
    k = next(i for i in range(count) if i not in (r, c))
    for first, second in ((left, right), (right, left)):
        for j, guards in enumerate(first.guards):
            for m, n in guards:
                if any(weaker(h, (m, n)) for h in second.guards[j]):
                    continue
                return tuple((1 << k | 1 << r if m & 1 << i else 1 << k) if i == j else
                             (1 << r | 1 << c if m & 1 << i else
                              1 << c if n & 1 << i else 1 << r)
                             for i in range(len(first.guards)))
    assert left == right
    return None


def arbitrary(rng, depth, arity, constructor):
    if not depth or rng.randrange(5) == 0:
        return var(rng.randrange(arity))
    if rng.randrange(3) == 0:
        return reset(*(arbitrary(rng, depth-1, arity, constructor) for _ in range(2)))
    return constructor(*(arbitrary(rng, depth-1, arity, constructor) for _ in range(3)))


def replace_policy(term, blockers):
    if term.op == 'var':
        return term
    if term.op == 'reset':
        return reset(*(replace_policy(t, blockers) for t in term.args))
    return policy(blockers, *(replace_policy(t, blockers) for t in term.args[-3:]))


def check():
    rng = Random(1103)
    x, y, z = map(var, range(3))
    for count in (3, 4, 5):
        for values in product(range(1, 1 << count), repeat=3):
            assert denote(g(0, 1, x, y, z), values) == denote(policy(3, x, y, z), values)
        terms = [x, y, z] + [arbitrary(rng, 3, 3, lambda *t: g(0, 1, *t)) for _ in range(120)]
        forms = [normal(t, 3) for t in terms]
        signatures = {}
        for term, form in zip(terms, forms):
            vals = (product(range(1, 1 << count), repeat=3) if count == 3 else
                    (tuple(rng.randrange(1, 1 << count) for _ in range(3)) for _ in range(300)))
            signature = []
            for values in vals:
                actual = denote(term, values)
                for observer in range(count):
                    assert bool(actual & 1 << observer) == observe(form, values, 3, observer)
                signature.append(actual)
            if count == 3:
                assert signatures.setdefault(tuple(signature), form) == form
        for blockers in range(1, (1 << count)-1):
            for i in range(12):
                changed = replace_policy(terms[i], blockers)
                for _ in range(100):
                    values = tuple(rng.randrange(1, 1 << count) for _ in range(3))
                    actual = denote(changed, values)
                    for observer in range(count):
                        assert bool(actual & 1 << observer) == observe(forms[i], values, blockers, observer)
            for _ in range(200):
                i, j = rng.randrange(len(terms)), rng.randrange(len(terms))
                values = separator(forms[i], forms[j], blockers, count)
                if values is not None:
                    assert denote(replace_policy(terms[i], blockers), values) != denote(
                        replace_policy(terms[j], blockers), values)
        print(f"Chain guards: K={count}, 123 native G terms; all nontrivial policies, "
              "guard semantics, and explicit separator checks passed.", flush=True)
    # An outsider's K=3 observation is weaker than the complete owner view.
    left, right = g(0, 1, x, y, z), reset(reset(z, y), x)
    for values in product(range(1, 8), repeat=3):
        assert bool(denote(left, values) & 4) == bool(denote(right, values) & 4)
    assert denote(left, (6, 4, 1)) == 7 and denote(right, (6, 4, 1)) == 6
    print("At K=3 the third role sees reset; an owner's observation separates it.")


if __name__ == '__main__':
    check()
