"""Exact finite witnesses for the refuted probabilistic open-game laws.

The paper gives the generic derivation from Definitions 11--12 of
arXiv:2009.06831v1. This checker evaluates the resulting closed forms for
the free Boolean source F, point-selecting echo H, and nonconvex selector K.
It is not a general open-game composer or a replacement for the pinned
GameTheory v1 Lean proofs.
"""

from fractions import Fraction as F
from itertools import product


def cleaned(law):
    return {point: mass for point, mass in law.items() if mass}


def boolean_law(p):
    return cleaned({(0,): 1 - p, (1,): p})


def independent(left, right):
    return {x + y: a * b for x, a in left.items() for y, b in right.items()}


def marginal(law, coordinates):
    result = {}
    for point, mass in law.items():
        projected = tuple(point[i] for i in coordinates)
        result[projected] = result.get(projected, F(0)) + mass
    return cleaned(result)


def diagonal(law):
    return {(point[0], point[0]): mass for point, mass in law.items()}


def mixture(weight, left, right):
    return cleaned({point: weight * left.get(point, F(0))
                    + (1 - weight) * right.get(point, F(0))
                    for point in left.keys() | right.keys()})


def left_bracketing_admits(law):
    """Raw (F;H);H: independently factor both cuts and apply echo lifting."""
    first_two = marginal(law, (0, 1))
    last = marginal(law, (2,))
    first = marginal(first_two, (0,))
    second = marginal(first_two, (1,))
    return (law == independent(first_two, last)
            and first_two == independent(first, second)
            and first == second == last)


def right_bracketing_admits(law):
    """Raw F;(H;H): the point-history pair law lifts to the diagonal."""
    first = marginal(law, (0,))
    last_two = marginal(law, (1, 2))
    return law == independent(first, last_two) and last_two == diagonal(first)


def check():
    fair = boolean_law(F(1, 2))
    iid = independent(independent(fair, fair), fair)
    paired = independent(fair, diagonal(fair))
    assert left_bracketing_admits(iid) and not right_bracketing_admits(iid)
    assert right_bracketing_admits(paired) and not left_bracketing_admits(paired)
    assert iid[(0, 0, 1)] == F(1, 8) and paired.get((0, 0, 1), 0) == 0
    assert all(iid[point] == F(1, 8) for point in product(range(2), repeat=3))

    grid = tuple(F(i, 8) for i in range(9))
    for p in grid:
        mu = boolean_law(p)
        left = independent(independent(mu, mu), mu)
        right = independent(mu, diagonal(mu))
        assert left_bracketing_admits(left)
        assert right_bracketing_admits(right)
        assert right_bracketing_admits(left) == (p in (0, 1))
        assert left_bracketing_admits(right) == (p in (0, 1))

    # At a point history Definition 11 gives convex closure. Thus Id;K
    # selects this barycenter, whereas K selects just the two point laws.
    point0, point1 = boolean_law(F(0)), boolean_law(F(1))
    assert mixture(F(1, 2), point0, point1) == fair
    assert fair != point0 and fair != point1

    # Tensoring two unconstrained decisions requires an independent law.
    # Both diagonal atoms are products; their fair mixture is not one.
    pair0, pair1 = diagonal(point0), diagonal(point1)
    fair_diagonal = mixture(F(1, 2), pair0, pair1)
    assert marginal(fair_diagonal, (0,)) == marginal(fair_diagonal, (1,)) == fair
    assert fair_diagonal != independent(fair, fair)

    # Convex-equivalent sources F0 and F cease to be equivalent after ;H:
    # conv(E(F0;H)) has equal coordinates; E(F;H) admits independent fair bits.
    assert all(x == y for x, y in fair_diagonal)
    assert (0, 1) in independent(fair, fair)

    # On the right, post-closing can only mix laws supported on y=z.
    # This linear support constraint is preserved by all finite mixtures.
    # The displayed grid mixtures verify this control independently.
    right_laws = [independent(boolean_law(p), diagonal(boolean_law(p))) for p in grid]
    for first, second, weight in product(right_laws, right_laws, grid):
        assert all(y == z for x, y, z in mixture(weight, first, second))
    assert any(y != z for x, y, z in iid)
    # Raw left equilibrium remains available after both closure steps.
    assert left_bracketing_admits(iid)
    print("Mixed open-game obstruction: left-unit witness, incomparable "
          "bracketings, tensor nonconvexity, and failed convex repairs passed "
          "with exact rational laws.")


if __name__ == "__main__":
    check()
