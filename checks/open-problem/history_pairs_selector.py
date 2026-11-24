"""Compare one-selector cap tables with the complete binary clone, at K=3.

The two groups of logical rows range independently over all monochromatic
budgets on two inputs. The cap requires the conjunction of their two c-flags.
Use explicit binary term-operation enumeration as a logical feasibility
oracle, and the offer-game solver on the resulting ternary operation tables.
"""

from functools import lru_cache
from itertools import product
from math import prod
from operator import or_
from functools import reduce

from explicit_table import FULL, K, recognize

A, B, C = 1, 2, 4
MENUS = tuple(range(1, FULL + 1))
BINARY = tuple(product(MENUS, repeat=2))
TERNARY = tuple(product(MENUS, repeat=3))


def choice(owner, left, right):
    return owner if owner in (left, right) else left | right


def union(xs):
    return reduce(or_, xs, 0)


def binary_clone():
    result = {tuple(v[i] for v in BINARY) for i in range(2)}
    while True:
        closed = {tuple(choice(r, a, b) for a, b in zip(s, t))
                  for s, t, r in product(result, result, (A, B, C))}
        if closed <= result:
            return result
        result.update(closed)


def profile_r(row, r, coalition):
    val = tuple(r if coalition >> x & 1 else FULL ^ r for x in range(2))
    return row[BINARY.index(val)] == r


def greatest(group, domain):
    while True:
        good = domain
        for h, tail in group:
            if not tail & domain:
                good &= ~(1 << h)
        if good == domain:
            return good
        domain = good


def by_closure(group, color, value):
    winning = 0
    for k in (A, B, C):
        domain = sum(1 << i for i in range(2) if k == color or value[i] != color)
        pool = greatest(group, domain)
        if any(value[i] & k for i in range(2) if pool >> i & 1):
            winning |= k
    return winning


def bounded(group, color, word):
    for head, tail in group:
        for k in (A, B, C):
            if k == color:
                continue
            v = tuple(k if i == head else color if tail >> i & 1 else FULL ^ k for i in range(2))
            if word[BINARY.index(v)] & k:
                return False
    return True


def groups_for(owner, clone):
    possible = [(h, tail) for h in range(2) for tail in (0, 1 << (1 - h))]
    groups = set()
    for mask in range(1 << len(possible)):
        group = [(h, t) for j, (h, t) in enumerate(possible) if mask >> j & 1]
        group = tuple((h, t) for h, t in group if t == 0 or (h, 0) not in group)
        groups.add(group)
    seen = []
    for group in sorted(groups):
        words = {word for word in clone if bounded(group, owner, word)}
        values = tuple(by_closure(group, owner, v) for v in BINARY)
        assert values == tuple(union(w[i] for w in words) for i in range(len(BINARY)))
        if words:
            assert values in words
            seen.append((words, values))
    return seen


@lru_cache(None)
def core_table(table):
    return recognize(dict(zip(TERNARY, table)), 3)


def check():
    clone = binary_clone()
    assert len(clone) == 20
    cap = {w for w in clone if all(profile_r(w, C, Z) == (Z == 3) for Z in range(4))}
    left, right = groups_for(A, clone), groups_for(B, clone)
    count = accepted = 0
    for (a_words, a_max), (b_words, b_max) in product(left, right):
        expected = bool(a_words & b_words & cap)
        values = []
        for y, x, z in TERNARY:
            i = BINARY.index((x, z))
            mode = a_max[i] if y == A else b_max[i] if y == B else x | z
            values.append(C if x == z == C else y | mode)
        actual = core_table(tuple(values))
        assert expected == actual
        count += 1
        accepted += actual
    print(f"{len(clone)} logical operations, {count} group pairs with two nonempty envelopes, "
          f"{accepted} realizable caps; all {core_table.cache_info().currsize} distinct "
          "ternary full tables agree.")


if __name__ == "__main__":
    check()
