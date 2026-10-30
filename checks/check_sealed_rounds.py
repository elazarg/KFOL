"""Check sealed-round certificates; generic proofs are in the paper.

Support rectangles are cross-checked against unilateral deviations. This
does not implement full SE belief consistency or quantify over all real
continuation selections. SealedRounds.lean checks the algebraic certificates.
"""

from fractions import Fraction as F
from itertools import permutations, product

from sealed_rounds import (
    atom, constant_equilibrium_outcome, diagonal_table, evaluate_rate,
    expected, is_nash, lottery, mix, nash_rectangles, parallel,
    possible_winners, public_point_outcomes, synthesize_rate,
)


def check_stages():
    values = (atom(0), atom(1), atom(2), lottery(F(1, 2), F(1, 2), 0))
    grid = tuple(F(i, 4) for i in range(5))
    checked = 0
    for entries in product(values, repeat=4):
        table = (entries[:2], entries[2:])
        rectangles = nash_rectangles(table)
        assert rectangles
        for p, q in product(grid, repeat=2):
            assert is_nash(table, (0, 1), p, q) == any(
                rectangle.contains(p, q) for rectangle in rectangles)
        for rectangle in rectangles:
            for p, q in rectangle.corners():
                assert is_nash(table, (0, 1), p, q)
        transposed = tuple(tuple(table[j][i] for j in range(2)) for i in range(2))
        assert {(r.column, r.row) for r in rectangles} == {
            (r.row, r.column) for r in nash_rectangles(transposed, (1, 0))}
        if all(value in (atom(0), atom(1), atom(2)) for value in entries):
            for permutation in permutations(range(3)):
                def transport(value):
                    result = [F(0)] * 3
                    for role, mass in enumerate(value):
                        result[permutation[role]] = mass
                    return tuple(result)
                transported = tuple(tuple(transport(value) for value in row)
                                    for row in table)
                assert nash_rectangles(transported, permutation[:2]) == rectangles
        checked += 1
    print(f"Sealed rounds: {checked} rational 2x2 tables, complete Nash rectangles "
          "versus grid deviations; exchange and role transport passed.")


def check_parallel_and_rates():
    rates = sorted({F(p, q) for q in range(1, 13) for p in range(q + 1)})
    for left, right in product(rates, repeat=2):
        result = constant_equilibrium_outcome(diagonal_table(left, right))
        assert result == (parallel(left, right), 1 - parallel(left, right), 0)
    small = tuple(F(p, 8) for p in range(9))
    for a, b, c in product(small, repeat=3):
        assert parallel(parallel(a, b), c) == parallel(a, parallel(b, c))
        assert parallel(a, min(b, c)) == min(parallel(a, b), parallel(a, c))
        assert parallel(a, max(b, c)) == max(parallel(a, b), parallel(a, c))
    for q in range(1, 101):
        for p in range(q + 1):
            value = F(p, q)
            assert evaluate_rate(synthesize_rate(value)) == value
    print(f"Sealed rounds: {len(rates) ** 2} diagonal games, parallel-sum laws, "
          "and rational synthesis through denominator 100 passed.")


def check_infinite_family():
    games = [atom(0)]
    for n in range(1, 25):
        games.append(constant_equilibrium_outcome(
            ((games[-1], atom(1)), (atom(1), atom(0)))))
        assert games[-1] == (F(1, n + 1), F(n, n + 1), 0)
    for n, m in product(range(1, 25), repeat=2):
        probe = (games[m][0], F(0), games[m][1])
        observed = possible_winners(public_point_outcomes(0, games[n], probe))
        wanted = {0, 1} if n < m else {0, 2} if m < n else {0, 1, 2}
        assert observed == wanted
    probe = (F(1, 2), F(0), F(1, 2))
    assert possible_winners((games[1],)) == possible_winners((games[2],)) == {0, 1}
    assert possible_winners(public_point_outcomes(0, games[1], probe)) == {0, 1, 2}
    assert possible_winners(public_point_outcomes(0, games[2], probe)) == {0, 2}
    print("Sealed rounds: 24 linear-size reciprocal games and 576 threshold "
          "contexts; the equal-winner-set composition obstruction passed.")


def check_nonconvexity():
    # G = (0 wins or_2 1 wins) or_0 2 wins. If the first child gives
    # player 0 positive probability, the root must choose that child.
    grid = tuple(F(i, 20) for i in range(21))
    for x, root_left in product(grid, repeat=2):
        left = (x, 1 - x, F(0))
        actual = mix(root_left, left, atom(2))
        rational_root = root_left == 1 or x == 0
        assert rational_root == (root_left * x >= x)
        if rational_root:
            assert actual[0] == 0 or actual[2] == 0
    midpoint = mix(F(1, 2), atom(0), atom(2))
    assert midpoint[0] > 0 and midpoint[2] > 0
    # Independent copies at a player-1 root can select these two equilibria
    # and mix between them, so distribution semantics is not idempotent.
    assert midpoint == (F(1, 2), F(0), F(1, 2))
    assert public_point_outcomes(1, atom(0), atom(2)) == {atom(0), atom(2)}
    print("Sealed rounds: public nonconvex outcome set and failure of "
          "distribution-level idempotency passed.")


if __name__ == "__main__":
    check_stages()
    check_parallel_and_rates()
    check_infinite_family()
    check_nonconvexity()
