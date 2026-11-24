"""Verify the finite local identities used to pad source rows with three clones.

The check includes mixed assignments at the three clones, foreign singleton
profiles on a diagonal, the permanent guard rows, and the relation recovering
a diagonal marked bit from three individually marked probes.
"""
from itertools import product

from history_pairs_index import OWNERS, R, S, UNIVERSE, choose, fold


def gadget(x, y, z):
    return choose(S, choose(R, x, y), z)


def view(k, menu):
    if menu & k:
        return k
    if menu in OWNERS:
        return menu
    return 0


def projected_gate(k, owner, left, right):
    if owner != k and owner in (left, right):
        return owner
    if k in (left, right):
        return k
    return left if left == right else 0


def coherent(k, tup):
    diag, *singles = tup
    return ((diag == k) == any(x == k for x in singles) and
            all((diag == r) == (x == r) for r in OWNERS if r != k for x in singles))


def check():
    menus = range(1, UNIVERSE + 1)
    guards = [(0, R, 2), (0, S, 4), (1, R, 1), (1, S, 4), (2, S, 3)]
    for H in range(1, 8):
        for owner in OWNERS:
            fails = [row for row in guards if H >> row[0] & 1 and
                     (row[1] != owner or not H & row[2])]
            assert fails
    for k in OWNERS:
        for h, r, posting in guards:
            if r != k:
                vals = [k if i == h else r if posting >> i & 1 else UNIVERSE ^ k
                        for i in range(3)]
                assert not gadget(*vals) & k
        for old in menus:
            assert gadget(old, old, old) == old
        for assigned in range(8):
            vals = [k if assigned >> i & 1 else UNIVERSE ^ k for i in range(3)]
            assert view(k, gadget(*vals)) == (k if assigned else 0)
        for r, x, y in product(OWNERS, menus, menus):
            assert view(k, choose(r, x, y)) == projected_gate(k, r, view(k, x), view(k, y))
        states = [t for t in product((0, *OWNERS), repeat=4) if coherent(k, t)]
        assert len(states) == 10
        for a, b, r in product(states, states, OWNERS):
            result = tuple(projected_gate(k, r, x, y) for x, y in zip(a, b))
            assert coherent(k, result)
    print('All three observers: 5 guard rows, 21 pure supports by owner, '
          '8 assignments of marked clones and 900 relation-closure checks passed.')


if __name__ == '__main__':
    check()
