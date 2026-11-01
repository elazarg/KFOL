"""Independent finite certificates for the four-variable basis obstruction.

The generic transfer of every three-variable identity is proved in Lean.
Here the proper-subalgebra embeddings use the native winner-set evaluator.
"""

from itertools import product

from fragments import denote, h, reset, var


def counter_reset(x, y):
    return y if 3 in (x, y) else max(x, y)


def counter_h(x, y, z):
    if x == 3:
        return x
    if 3 not in (y, z):
        return max(x, y, z)
    other = z if y == 3 else y
    return 2 if x == 0 and other == 2 else x


def check():
    x, y, z, u = map(var, range(4))
    native_reset, native_h = reset(x, y), h(0, x, y, z)
    # owner=A=1, other=B=2, ambiguous=N=3, winning=P=7.
    embeddings = {
        3: {0: (3, 3), 1: (7, 3), 2: (7, 7)},
        2: {0: (3, 3), 1: (7, 7), 3: (1, 1)},
        0: {1: (3, 3), 2: (7, 7), 3: (1, 1)},
        1: {0: (3, 3), 2: (7, 7), 3: (2, 2)},
    }
    for omitted, embed in embeddings.items():
        assert set(embed) == set(range(4)) - {omitted}
        assert len(set(embed.values())) == 3
        for a, b in product(embed, repeat=2):
            result = counter_reset(a, b)
            assert result in (a, b)
            assert embed[result] == tuple(denote(native_reset, (embed[a][i], embed[b][i]))
                                          for i in range(2))
        for a, b, c in product(embed, repeat=3):
            result = counter_h(a, b, c)
            assert result in (a, b, c)
            assert embed[result] == tuple(denote(native_h, (embed[a][i], embed[b][i], embed[c][i]))
                                          for i in range(2))
    left = h(0, reset(u, x), y, z)
    right = reset(reset(u, x), h(0, x, y, z))
    for count in (3, 4):
        for inputs in product(range(1, 1 << count), repeat=4):
            assert denote(left, inputs) == denote(right, inputs)
    assert counter_h(counter_reset(1, 0), 2, 3) == 1
    assert counter_reset(counter_reset(1, 0), counter_h(0, 2, 3)) == 2
    print('Owner basis: every proper-subalgebra embedding and the four-variable '
          'counterexample passed; root expansion checked on all winner-set '
          'valuations at K=3,4.')


if __name__ == '__main__':
    check()
