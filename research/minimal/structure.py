"""Small exact semantics for arbitrary-arity owned-choice terms.

This module implements the generic observational quotient proved in
Perspectives.lean. Role renaming is external; there is no internal
permutation constructor. Finite tests are in check_structure.py.
"""

from dataclasses import dataclass
from itertools import product


def own(role, left, right):
    atom = 1 << role
    return atom if left == atom or right == atom else left | right


@dataclass(frozen=True)
class Win:
    role: int


@dataclass(frozen=True)
class Var:
    index: int


@dataclass(frozen=True)
class Choice:
    role: int
    left: object
    right: object


def evaluate(term, inputs):
    if isinstance(term, Win):
        return 1 << term.role
    if isinstance(term, Var):
        return inputs[term.index]
    return own(term.role, evaluate(term.left, inputs), evaluate(term.right, inputs))


def neutral_join(left, right):
    return Choice(2, Choice(0, left, right), Choice(1, left, right))


def view(player, value, count):
    """player = possible; count = excluded ambiguity; other indices = singleton."""
    if value & (1 << player):
        return player
    if value.bit_count() == 1:
        return value.bit_length() - 1
    return count


def view_own(player, owner, left, right, count):
    if owner != player and (left == owner or right == owner):
        return owner
    if left == right and left < count and left != player:
        return left
    if left == player or right == player:
        return player
    return count


def evaluate_view(term, inputs, player, count):
    if isinstance(term, Win):
        return term.role
    if isinstance(term, Var):
        return inputs[term.index]
    return view_own(player, term.role,
                    evaluate_view(term.left, inputs, player, count),
                    evaluate_view(term.right, inputs, player, count), count)


def perspective_tables(term, count, arity):
    """Canonical, compositional function tables in K factors of size K+1."""
    return tuple(tuple(evaluate_view(term, values, player, count)
                       for values in product(range(count + 1), repeat=arity))
                 for player in range(count))


def test_values(count):
    if count < 3:
        raise ValueError("The full nonempty powerset algebra requires K >= 3.")
    atoms = tuple(1 << i for i in range(count))
    pairs = (3, 5, 6) if count == 3 else (3, 12)
    return atoms + pairs


def equation_counterexample(left, right, count, arity):
    """A complete test at all arities, using the optimal fixed test domain."""
    for values in product(test_values(count), repeat=arity):
        if evaluate(left, values) != evaluate(right, values):
            return values
    return None


def status_form(term, statuses, count):
    """Canonical union provenance on a fixed singleton/ambiguous input cell.

    Status i means singleton {i}; status count means an arbitrary ambiguous
    value. The result (C,J) denotes C union the inputs indexed by J. If C is
    full, J is discarded. Only ambiguous input indices occur in J.
    """
    if isinstance(term, Win):
        return 1 << term.role, 0
    if isinstance(term, Var):
        status = statuses[term.index]
        return (0, 1 << term.index) if status == count else (1 << status, 0)
    first = status_form(term.left, statuses, count)
    second = status_form(term.right, statuses, count)
    atom = 1 << term.role
    if first == (atom, 0) or second == (atom, 0):
        return atom, 0
    extra, used = first[0] | second[0], first[1] | second[1]
    return extra, 0 if extra == (1 << count) - 1 else used


def realize_form(form, inputs):
    extra, used = form
    for j, value in enumerate(inputs):
        if used & (1 << j):
            extra |= value
    return extra


def status_tables(term, count, arity):
    return tuple(status_form(term, statuses, count)
                 for statuses in product(range(count + 1), repeat=arity))


def is_complete_domain(domain, count):
    """Exact characterization proved in the note; sufficiency is in Lean."""
    return (all(1 << i in domain for i in range(count)) and
            all(any(value.bit_count() > 1 and not value & (1 << i)
                    for value in domain) for i in range(count)))


def closure_congruences(count):
    """All congruences via intersection-closed families with the atom rule.

    Intended for K=3,4 experiments, not enumeration at large K.
    Returns class-maximum closure maps, represented on values 1..2^K-1.
    """
    full = (1 << count) - 1
    proper_ambiguous = tuple(v for v in range(1, full) if v.bit_count() > 1)
    result = set()
    for fixed_atoms in range(1 << count):
        optional = tuple(v for v in proper_ambiguous if not v & ~fixed_atoms)
        required = {full} | {1 << i for i in range(count) if fixed_atoms & (1 << i)}
        for selected in range(1 << len(optional)):
            closed = required | {v for j, v in enumerate(optional) if selected & (1 << j)}
            if any(a & b and a & b not in closed for a in closed for b in closed):
                continue
            classes = []
            for value in range(1, full + 1):
                maximum = full
                for c in closed:
                    if not value & ~c:
                        maximum &= c
                classes.append(maximum)
            result.add(tuple(classes))
    return result
