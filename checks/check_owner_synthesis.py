"""Independent checks of one-owner table recognition and native-tree synthesis.

Compare saturation with exhaustive four-state term closure through arity three,
and with an independent finite graph of safe spines on every canonical table
at arity four (one root, the others obtained by renaming). Neither reference
checker uses the saturation rules.
"""

from collections import deque
from itertools import product
from random import Random

from check_one_owner import arbitrary
from fragments import denote, h, reset
from one_owner import (Normal, admissible, compose, normal, normalize_other, realize,
                       synthesize)


def families(arity, root, source):
    others = [i for i in range(arity) if i not in (root, source)]
    guards = []
    for levels in product(range(3), repeat=len(others)):
        m, n = 1 << root, 0
        for i, level in zip(others, levels):
            if level == 1:
                n |= 1 << i
            elif level == 2:
                m |= 1 << i
        guards.append((m, n))
    return sorted({normalize_other(tuple(g for i, g in enumerate(guards)
                                         if mask & (1 << i)), source)
                   for mask in range(1 << len(guards))})


def tables(arity, root=0):
    choices = [(((0, 0),),) if j == root else families(arity, root, j)
               for j in range(arity)]
    for table in product(*choices):
        yield Normal(root, table)


def safe_spine(form, source, goal):
    """BFS of all allowed path states, retaining both masks and the current root."""
    arity = len(form.other)
    goal_m, goal_n = goal

    def permitted(j, m, n):
        return any(a & ~m == 0 and b & ~(m | n | (1 << j)) == 0
                   for a, b in form.other[j])

    start = (form.root, 0, 0)
    seen, queue = {start}, deque([start])
    while queue:
        v, m, n = queue.popleft()
        if v == source:
            # The current guard is safe and covers the requested minimal one.
            return True
        next_m = m | (1 << v)
        if next_m & ~goal_m:
            continue
        for w in range(arity):
            candidates = [n & ~next_m]
            for z in range(arity):
                tests = (n | (1 << w) | (1 << z)) & ~next_m
                if permitted(z, next_m, tests):
                    candidates.append(tests)
            for tests in candidates:
                if tests & ~(goal_m | goal_n | (1 << source)):
                    continue
                state = (w, next_m, tests)
                if state not in seen and permitted(w, next_m, tests):
                    seen.add(state)
                    queue.append(state)
    return False


def four_closure(arity):
    """Complete term-function closure, computed directly in the four-state algebra."""
    valuations = tuple(product(range(4), repeat=arity))
    known = {bytes(row[j] for row in valuations) for j in range(arity)}
    while True:
        old = tuple(known)
        for x, y in product(old, repeat=2):
            known.add(bytes(3 if a == 3 and b == 2 else b for a, b in zip(x, y)))
        for x, y, z in product(old, repeat=3):
            known.add(bytes(3 if a == 2 and b != 0 and c != 0 and (b == 3 or c == 3)
                            else a for a, b, c in zip(x, y, z)))
        if len(known) == len(old):
            return known


def size(term):
    if term.op == 'var':
        return 1
    children = term.args if term.op == 'reset' else term.args[1:]
    return 1 + sum(map(size, children))


def substitute(term, inner):
    if term.op == 'var':
        return inner[term.args[0]]
    if term.op == 'reset':
        return reset(*(substitute(child, inner) for child in term.args))
    return h(term.args[0], *(substitute(child, inner) for child in term.args[1:]))


def check():
    values = (1, 2, 3, 7)
    codes = {v: i for i, v in enumerate(values)}
    for arity in range(1, 4):
        closed = four_closure(arity)
        accepted = set()
        for root in range(arity):
            for form in tables(arity, root):
                signature = bytes(codes[realize(form, row, 0)]
                                  for row in product(values, repeat=arity))
                assert admissible(form) == (signature in closed), form
                if admissible(form):
                    term = synthesize(form)
                    assert normal(term, 0, arity) == form
                    assert signature == bytes(codes[denote(term, row)]
                                              for row in product(values, repeat=arity))
                    accepted.add(signature)
        assert accepted == closed
        print(f"Owner synthesis: arity {arity}, all {len(closed)} term functions "
              "agree with independent four-state closure.", flush=True)

    accepted = checked = 0
    for form in tables(4):
        expected = all(safe_spine(form, j, g)
                       for j, family in enumerate(form.other) for g in family)
        assert admissible(form) == expected, form
        checked += 1
        if expected:
            accepted += 1
            term = synthesize(form)
            assert normal(term, 0, 4) == form
            guards = sum(map(len, form.other))
            assert size(term) <= (12 * 4 + 10) * guards + 1
    print(f"Owner synthesis: all {checked} four-input canonical tables with root 0; "
          f"{accepted} realizable, matching exhaustive safe-spine search.", flush=True)

    rng = Random(1103)
    for arity in (5, 6, 8):
        for _ in range(250):
            original = arbitrary(rng, arity, 0, 5)
            form = normal(original, 0, arity)
            term = synthesize(form)
            assert normal(term, 0, arity) == form
            guards = sum(map(len, form.other))
            assert size(term) <= (12 * arity + 10) * guards + 1
            for _ in range(15):
                row = tuple(rng.randrange(1, 16) for _ in range(arity))
                assert denote(original, row) == denote(term, row)
        print(f"Owner synthesis: 250 terms at arity {arity}; synthesis, linear "
              "size bound, and native winner-set evaluations passed.", flush=True)

    for _ in range(250):
        outer = arbitrary(rng, 3, 0, 3)
        inner = [arbitrary(rng, 4, 0, 3) for _ in range(3)]
        form = compose(normal(outer, 0, 3), [normal(t, 0, 4) for t in inner])
        assert form == normal(substitute(outer, inner), 0, 4)
        assert normal(synthesize(form), 0, 4) == form
    print('Owner synthesis: 250 clone substitutions agree with native term substitution.',
          flush=True)

    invalid = [Normal(0, ()), Normal(1, (((0, 0),),)),
               Normal(0, (((0, 0),), ((0, 0),))),
               Normal(0, (((0, 0),), ((3, 0),))),
               Normal(0, (((0, 0),), ((1, 2),))),
               Normal(0, (((0, 0),), ((5, 0),)))]
    for form in invalid:
        assert not admissible(form)
        try:
            synthesize(form)
        except ValueError:
            pass
        else:
            raise AssertionError(form)


if __name__ == '__main__':
    check()
