"""Independent finite checks of the conservative model and residual results."""

from itertools import combinations, product
from collections import deque
from forest import comb, conservative_tables, forest_tables, laws, lift_free, principal


def check_one_constant():
    for k in range(3, 7):
        values = tuple(range(1, 1 << k))
        fixed = 1
        identity, constant = values, (fixed,) * len(values)
        found = {identity, constant}
        queue = deque(found)
        while queue:
            first = queue.popleft()
            for second in list(found):
                for r in range(k):
                    owner = 1 << r
                    result = tuple(owner if a == owner or b == owner else a | b
                                   for a, b in zip(first, second))
                    if result not in found:
                        found.add(result)
                        queue.append(result)
        assert len(found) == 2 ** (k - 1) + 2
        assert all(f == constant or all(s & f[s-1] == s for s in values) for f in found)
        assert all(f == constant for f in found if f[1] == fixed)
        for f in found:
            if all(f[(1 << i)-1] == 1 << i for i in range(k)):
                expected = tuple(s if s.bit_count() == 1 else s | fixed for s in values)
                assert f in (identity, expected)
        print(f"One constant at K={k}: all {len(found)} contexts satisfy the rigidity dichotomy", flush=True)


def check_classification():
    for n, expected in ((1, 1), (2, 3), (3, 16), (4, 125)):
        equations = {op for op in conservative_tables(n) if laws(op)}
        orders = set(forest_tables(n))
        assert equations == orders and len(orders) == expected
        for op in equations:
            assert lift_free(op) == (True, (1, 4, 18, 140)[n-1])
        print(f"{n} elements: {expected} conservative models; two laws, parent forests, and full free-algebra lifting agree", flush=True)
    assert len(set(forest_tables(5))) == 1296


def check_combs():
    for n in range(1, 8):
        op = comb(n)
        size = len(op)
        assert laws(op)
        collapse = lambda x: 1 if x == 0 else x
        assert all(collapse(op[x][y]) == op[collapse(x)][collapse(y)]
                   for x, y in product(range(size), repeat=2))
        for a, b in combinations(range(size), 2):
            theta = principal(op, a, b)
            assert theta[0] == theta[1]
        bottom = principal(op, 0, 1)
        assert all((bottom[x] == bottom[y]) == (x == y or {x, y} <= {0, 1})
                   for x, y in product(range(size), repeat=2))
        print(f"Comb with {size} elements: every nontrivial principal congruence contains the exact two-point monolith", flush=True)
    assert lift_free(comb(2)) == (True, 2980)
    print("Five-element comb satisfies every reset identity: full F_5 lifting (2980 functions) passed", flush=True)


if __name__ == '__main__':
    check_one_constant()
    check_classification()
    check_combs()
