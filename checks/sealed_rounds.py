"""Exact rational models for completely revealed commit--reveal rounds.

A round has two active players with two actions each. Its four continuation
values are winner distributions. Support enumeration represents the complete
mixed Nash set by rectangles of row/column probabilities. This is a local
stage model, not an implementation of SE for arbitrary information sets.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product


def atom(role, count=3):
    return tuple(F(i == role) for i in range(count))


def lottery(*coordinates):
    value = tuple(map(F, coordinates))
    assert min(value) >= 0 and sum(value) == 1
    return value


def mix(weight, left, right):
    return tuple(weight * a + (1 - weight) * b for a, b in zip(left, right))


@dataclass(frozen=True)
class Interval:
    low: F = F(0)
    high: F = F(1)

    def contains(self, value):
        return self.low <= value <= self.high

    def constrain(self, slope, intercept):
        """Intersect with slope * value + intercept >= 0."""
        low, high = self.low, self.high
        if slope > 0:
            low = max(low, -intercept / slope)
        elif slope < 0:
            high = min(high, -intercept / slope)
        elif intercept < 0:
            return None
        return Interval(low, high) if low <= high else None


@dataclass(frozen=True)
class Rectangle:
    row: Interval
    column: Interval

    def contains(self, p, q):
        return self.row.contains(p) and self.column.contains(q)

    def corners(self):
        return product((self.row.low, self.row.high),
                       (self.column.low, self.column.high))


def expected(table, p, q):
    return mix(p, mix(q, table[0][0], table[0][1]),
               mix(q, table[1][0], table[1][1]))


def is_nash(table, owners, p, q):
    """Independent check against every pure unilateral deviation."""
    actual = expected(table, p, q)
    return all(expected(table, candidate, q)[owners[0]] <= actual[owners[0]]
               for candidate in (F(0), F(1))) and all(
        expected(table, p, candidate)[owners[1]] <= actual[owners[1]]
        for candidate in (F(0), F(1)))


def nash_rectangles(table, owners=(0, 1)):
    """All equilibria, including degenerate continua and zero coordinates.

    For each pair of permitted supports, best-response conditions constrain
    the opponent's mixing probability by affine inequalities. The resulting
    sets are closed rectangles. Boundaries may have several representations.
    """
    row_owner, column_owner = owners
    row0 = table[0][1][row_owner] - table[1][1][row_owner]
    row_slope = (table[0][0][row_owner] - table[1][0][row_owner]) - row0
    col0 = table[1][0][column_owner] - table[1][1][column_owner]
    col_slope = (table[0][0][column_owner] - table[0][1][column_owner]) - col0
    supports = ((0,), (1,), (0, 1))
    intervals = (Interval(F(1), F(1)), Interval(F(0), F(0)), Interval())
    rectangles = set()
    for row_index, column_index in product(range(3), repeat=2):
        p, q = intervals[row_index], intervals[column_index]
        for row in supports[row_index]:
            sign = 1 if row == 0 else -1
            if q is not None:
                q = q.constrain(sign * row_slope, sign * row0)
        for column in supports[column_index]:
            sign = 1 if column == 0 else -1
            if p is not None:
                p = p.constrain(sign * col_slope, sign * col0)
        if p is not None and q is not None:
            rectangles.add(Rectangle(p, q))
    return frozenset(rectangles)


def constant_equilibrium_outcome(table, owners=(0, 1)):
    """Certify a singleton outcome set on every Nash rectangle.

    Each outcome coordinate is bilinear in p,q. Constancy at the four corners
    therefore proves constancy on a whole rectangle, including its interior.
    """
    rectangles = nash_rectangles(table, owners)
    assert rectangles
    outcomes = {expected(table, p, q)
                for rectangle in rectangles for p, q in rectangle.corners()}
    assert len(outcomes) == 1, outcomes
    return outcomes.pop()


def parallel(left, right):
    return left * right / (left + right) if left + right else F(0)


def diagonal_table(left, right, winner=0, loser=1):
    lose = atom(loser)
    return ((mix(left, atom(winner), lose), lose),
            (lose, mix(right, atom(winner), lose)))


def public_point_outcomes(owner, left, right):
    """Endpoints of the exact selected point or indifference segment."""
    if left[owner] > right[owner]:
        return frozenset((left,))
    if right[owner] > left[owner]:
        return frozenset((right,))
    return frozenset((left, right))


def possible_winners(outcomes):
    return frozenset(i for value in outcomes for i, mass in enumerate(value)
                     if mass > 0)


def synthesize_rate(value):
    """A syntax tree using complement and U(x)=x parallel 1 only."""
    value = F(value)
    assert 0 <= value <= 1
    if value == 0:
        return ("zero",)
    if value == 1:
        return ("one",)
    p, q = value.numerator, value.denominator
    if 2 * p <= q:
        return ("U", synthesize_rate(F(p, q - p)))
    return ("C", ("U", synthesize_rate(F(q - p, p))))


def evaluate_rate(term):
    if term[0] == "zero":
        return F(0)
    if term[0] == "one":
        return F(1)
    value = evaluate_rate(term[1])
    return parallel(value, F(1)) if term[0] == "U" else 1 - value
