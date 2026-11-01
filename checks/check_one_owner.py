"""Independent finite checks of the one-owner guard-table calculus."""

from itertools import product
from random import Random

from fragments import denote, h, reset, var
from one_owner import (countervaluation, normal, observe, observation_countervaluation,
                       observation_normal, realize)


def arbitrary(rng, arity, owner, depth):
    if not depth or rng.randrange(5) == 0:
        return var(rng.randrange(arity))
    if rng.randrange(3) == 0:
        return reset(arbitrary(rng, arity, owner, depth - 1),
                     arbitrary(rng, arity, owner, depth - 1))
    return h(owner, *(arbitrary(rng, arity, owner, depth - 1) for _ in range(3)))


def check():
    rng = Random(1101)
    for count, arity, samples in ((3, 3, 400), (4, 3, 100), (5, 4, 100)):
        owner = count - 1
        terms = [var(i) for i in range(arity)]
        terms += [arbitrary(rng, arity, owner, 4) for _ in range(samples)]
        forms = [normal(t, owner, arity) for t in terms]
        seen = {}
        for term, form in zip(terms, forms):
            values = (product(range(1, 1 << count), repeat=arity) if count == 3 else
                      (tuple(rng.randrange(1, 1 << count) for _ in range(arity))
                       for _ in range(300)))
            signature = []
            for valuation in values:
                actual = denote(term, valuation)
                assert actual == realize(form, valuation, owner), (term, form, valuation)
                root = valuation[form.root]
                assert (actual.bit_count() > 1) == (root.bit_count() > 1)
                assert (actual == 1 << owner) == (root == 1 << owner)
                signature.append(actual)
            if count == 3:
                signature = tuple(signature)
                assert seen.setdefault(signature, form) == form
        for _ in range(2000):
            i, j = rng.randrange(len(terms)), rng.randrange(len(terms))
            valuation = countervaluation(forms[i], forms[j], owner, count)
            if valuation is None:
                assert forms[i] == forms[j]
            else:
                assert all(value.bit_count() <= 2 for value in valuation)
                assert denote(terms[i], valuation) != denote(terms[j], valuation)
        print(f"One-owner H: K={count}, {len(terms)} terms; exact guard semantics "
              "and 2000 canonical-table separator tests passed.")
    for count in (3, 4):
        for owner in range(count):
            for x, y in product(range(1, 1 << count), repeat=2):
                values = (x, y)
                assert denote(h(owner, var(1), var(0), var(0)), values) == denote(
                    reset(var(0), var(1)), values)
    print("One-owner H: reset derivability passed for every owner at K=3,4.")


def check_observers():
    rng = Random(1102)
    def two_owners(depth):
        if not depth or rng.randrange(5) == 0:
            return var(rng.randrange(3))
        if rng.randrange(3) == 0:
            return reset(two_owners(depth - 1), two_owners(depth - 1))
        return h(rng.randrange(2), *(two_owners(depth - 1) for _ in range(3)))
    terms = [var(i) for i in range(3)] + [two_owners(3) for _ in range(300)]
    for observer, other in ((0, 1), (1, 0)):
        forms = [observation_normal(term, observer, other, 3) for term in terms]
        signatures = {}
        for term, form in zip(terms, forms):
            signature = []
            for values in product(range(1, 8), repeat=3):
                actual = bool(denote(term, values) & (1 << observer))
                assert actual == observe(form, values, observer, other)
                signature.append(actual)
            assert signatures.setdefault(tuple(signature), form) == form
        for _ in range(2000):
            i, j = rng.randrange(len(terms)), rng.randrange(len(terms))
            witness = observation_countervaluation(forms[i], forms[j], observer, other)
            if witness is not None:
                assert bool(denote(terms[i], witness) & (1 << observer)) != bool(
                    denote(terms[j], witness) & (1 << observer))
    # Both participating owners have identical observations of this equation,
    # but the third player's observation separates it.
    y1, y2, z, c = map(var, range(4))
    base = reset(y1, reset(y2, z))
    right = reset(h(0, z, y1, c), reset(h(1, z, y2, c), base))
    left = reset(c, right)
    for observer, other in ((0, 1), (1, 0)):
        assert observation_normal(left, observer, other, 4) == observation_normal(
            right, observer, other, 4)
    assert denote(left, (1, 2, 3, 4)) == 7
    assert denote(right, (1, 2, 3, 4)) == 3
    print("Two-owner observations: 303 terms, both owners on all 7^3 valuations; "
          "4000 separators and the outsider-only disagreement passed.")


def check_five_states():
    def view(value, owner, observer):
        return (value.bit_count() > 1, value == 1 << owner,
                bool(value & (1 << observer)))

    def reset_view(left, right):
        return (True, False, left[2] or right[2]) if right[0] else right

    def h_view(root, left, right):
        return ((True, False, root[2] or
                 (not left[1] and not right[1] and (left[2] or right[2])))
                if root[0] else root)

    def four(v):
        return 'P' if v[2] else 'A' if v[1] else 'N' if v[0] else 'B'

    def reset_four(x, y):
        return 'P' if x == 'P' and y == 'N' else y

    def h_four(x, y, z):
        return ('P' if y != 'A' and z != 'A' and 'P' in (y, z) else 'N') if x == 'N' else x

    states = set()
    comparisons = 0
    x, y, z = map(var, range(3))
    for count in (3, 4, 5):
        owner, observer = count - 1, 0
        values = range(1, 1 << count)
        current = {view(value, owner, observer) for value in values}
        assert len(current) == 5
        if states:
            assert states == current
        states = current
        for a, b, c in product(values, repeat=3):
            inputs = (a, b, c)
            av, bv, cv = (view(value, owner, observer) for value in inputs)
            assert view(denote(reset(x, y), inputs), owner, observer) == reset_view(av, bv)
            assert view(denote(h(owner, x, y, z), inputs), owner, observer) == h_view(av, bv, cv)
            assert four(reset_view(av, bv)) == reset_four(four(av), four(bv))
            assert four(h_view(av, bv, cv)) == h_four(four(av), four(bv), four(cv))
            comparisons += 1
    concrete = (1, 2, 3, 7)
    for values in product(concrete, repeat=3):
        assert denote(reset(x, y), values) in values
        assert denote(h(0, x, y, z), values) in values
    # All three-element candidates satisfying the root absorption bounds.
    def r(x, y):
        return (2 if x == 2 else 1) if y == 1 else y
    surviving = 0
    for row in product((1, 2), repeat=9):
        def hh(x, y, z):
            return row[3*y + z] if x == 1 else x
        if not all(hh(a, b, b) == r(b, a) and hh(b, b, c) == r(c, b)
                   and hh(a, b, a) == r(b, a) for a, b, c in product(range(3), repeat=3)):
            continue
        surviving += 1
        first = all(r(hh(a, b, c), r(r(c, b), a)) == r(r(c, b), a)
                    for a, b, c in product(range(3), repeat=3))
        second = all(r(r(c, a), hh(a, b, c)) == hh(a, b, c)
                     for a, b, c in product(range(3), repeat=3))
        assert first or second
    assert surviving == 4
    print(f"Four-state generator: {comparisons} homomorphism comparisons at K=3,4,5; "
          "conservative concrete subalgebra and all 512 smaller candidates passed.")


if __name__ == '__main__':
    check()
    check_observers()
    check_five_states()
