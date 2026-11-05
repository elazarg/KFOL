"""Verify the five-coordinate obstruction to flattening a unary polynomial.

The complement of the target's principal ideal is invariant under every
coefficient translation. Upward closure also covers arbitrary inserted
extensive maps and joins, so the proof excludes all expression sizes.
"""

from itertools import product

from core_basis import marker_join, marker_own


def check():
    base = [
        [[marker_join(2, x, y) for y in range(4)] for x in range(4)],
        *[[[marker_own(2, h, x, y) for y in range(4)]
           for x in range(4)] for h in range(2)],
    ]

    def op(h, u, v):
        return tuple(base[h][x][y] for x, y in zip(u, v))

    def below(u, v):
        return op(0, u, v) == v

    def generated(generators):
        elements = list(dict.fromkeys(generators))
        seen = set(elements)
        for u in elements:
            for v in elements[:]:
                for h in range(3):
                    w = op(h, u, v)
                    if w not in seen:
                        seen.add(w)
                        elements.append(w)
        assert all(op(h, u, v) in seen
                   for h, u, v in product(range(3), elements, elements))
        return seen

    a = (0, 3, 3, 3, 1)
    b = (3, 0, 1, 3, 2)
    c = (3, 3, 3, 1, 0)
    x = (0, 0, 1, 1, 3)
    q = op(1, op(2, a, x), op(2, b, op(1, c, x)))
    assert q == (0, 0, 1, 1, 2)
    coefficients = generated((a, b, c))
    algebra = generated((a, b, c, x))
    assert coefficients <= algebra and q in algebra

    # Check the invariant relations independently of the generated tables.
    relation_checks = 0
    for forbidden in ((0, 1), (1, 0)):
        relation = set(product(range(4), repeat=2)) - {forbidden}
        for h, u, v in product(range(3), relation, relation):
            assert op(h, u, v) in relation
            relation_checks += 1
    for d in coefficients:
        assert (d[0], d[2]) != (0, 1)
        assert (d[1], d[3]) != (0, 1)
        assert (d[2], d[4]) != (1, 0)
        assert (d[1], d[4]) != (0, 1)

    ideal = {u for u in algebra if below(u, q)}
    outside = algebra - ideal
    assert x in outside and coefficients <= outside
    assert q not in outside
    translations = 0
    for h, d, u in product(range(3), coefficients, algebra):
        value = op(h, d, u)
        assert value not in ideal or u in ideal
        translations += 1
    upward_pairs = 0
    for u, v in product(outside, algebra):
        if below(u, v):
            assert v in outside
            upward_pairs += 1
    for u, v in product(outside, repeat=2):
        assert op(0, u, v) in outside

    assert (len(algebra), len(coefficients), len(outside)) == (48, 18, 47)
    print(f'Branching obstruction: {len(algebra)} ambient states, '
          f'{len(coefficients)} coefficients, {len(outside)} invariant states; '
          f'{relation_checks} relation checks, {translations} translation '
          f'checks, {upward_pairs} upward pairs, {len(outside) ** 2} joins. '
          'The target lies outside the invariant, excluding all expression '
          'sizes by the written proof. This is not a countermodel to the '
          'candidate basis: the algebra is a core subalgebra of D_2^5.')


if __name__ == '__main__':
    check()
