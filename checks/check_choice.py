"""Checks for the small owned-choice fragment. Only binary choice and atoms.

The generic union and single-use results are checked separately in Basic.lean.
The unary closure below is exhaustive at K=3; template synthesis is exhaustive
over the proposed unary normal forms at K=3 and K=4.
"""

from collections import deque
from dataclasses import dataclass
from itertools import permutations, product


def own(role, left, right):
    atom = 1 << role
    return atom if left == atom or right == atom else left | right


def neutral_join(left, right):
    return own(2, own(0, left, right), own(1, left, right))


def compose_profiles(role, left, right):
    return tuple(own(role, a, b) for a, b in zip(left, right))


def join_profiles(left, right):
    return tuple(neutral_join(a, b) for a, b in zip(left, right))


def ground_values(count):
    values = {1 << i for i in range(count)}
    while True:
        enlarged = values | {
            own(r, a, b) for r in range(count) for a in values for b in values
        }
        if enlarged == values:
            return values
        values = enlarged


def basic_laws():
    for count in range(3, 7):
        values = tuple(range(1, 1 << count))
        assert ground_values(count) == set(values)
        assert all(neutral_join(a, b) == a | b for a, b in product(values, repeat=2))
        assert all(
            own(r, a, b | c) == own(r, a, b) | own(r, a, c)
            for r in range(count) for a, b, c in product(values, repeat=3)
        )
    for r, s, t in permutations(range(4), 3):
        for a, b in product(range(1, 16), repeat=2):
            assert own(t, own(r, a, b), own(s, a, b)) == a | b
    # Contexts can distinguish ambiguity by possibility, but not by unique winner.
    assert own(0, 0b011, 0b100) == 0b111
    # Atomic input tests alone do not determine even a unary term function.
    identity = tuple(range(1, 8))
    gate = compose_profiles(0, identity, (2,) * 7)
    gate = compose_profiles(1, gate, (1,) * 7)
    gate = compose_profiles(2, identity, gate)
    assert all(gate[a - 1] == a for a in (1, 2, 4))
    assert gate[0b101 - 1] == 0b111
    # Unlike the guarantee algebra, owned operations are not mutually distributive.
    assert own(0, 3, own(1, 2, 4)) == 3
    assert own(1, own(0, 3, 2), own(0, 3, 4)) == 7
    print("Core: ground realization, neutral join, and distributivity over union passed for K=3..6.")


def unary_closure():
    values = tuple(range(1, 8))
    functions = {tuple(values)} | {(a,) * 7 for a in values}
    queue = deque(functions)
    while queue:
        first = queue.popleft()
        for second in list(functions):
            for role in range(3):
                combined = compose_profiles(role, first, second)
                if combined not in functions:
                    functions.add(combined)
                    queue.append(combined)
    assert len(functions) == 131
    return functions


def unary_templates(count):
    values = tuple(range(1, 1 << count))
    identity = values
    full = (1 << count) - 1
    gates = {}
    allowed = {}
    for winner in range(count):
        allowed[winner] = tuple(mask for mask in range(1 << count) if not mask & (1 << winner))
        for permit in allowed[winner]:
            profile = join_profiles(identity, (1 << winner,) * len(values))
            for role in range(count):
                if role != winner and not permit & (1 << role):
                    profile = compose_profiles(role, profile, identity)
            gates[winner, permit] = profile
    functions = set()
    parameters = []
    template_count = 0
    for extra in range(1 << count):
        winners = tuple(r for r in range(count) if extra & (1 << r))
        for permits in product(*(allowed[r] for r in winners)):
            function = identity
            for role, permit in zip(winners, permits):
                function = join_profiles(function, gates[role, permit])
            expected = []
            for value in values:
                if value.bit_count() >= 2:
                    expected.append(value | extra)
                else:
                    expected.append(value | sum(
                        1 << role for role, permit in zip(winners, permits) if permit & value
                    ))
            assert function == tuple(expected)
            rows = tuple(sum(
                1 << role for role, permit in zip(winners, permits) if permit & (1 << i)
            ) for i in range(count))
            parameters.append((extra, rows, function))
            functions.add(function)
            template_count += 1
    assert template_count == (1 + 2 ** (count - 1)) ** count
    assert len(functions) == template_count
    constants = {(a,) * len(values) for a in values}
    assert len(functions & constants) == 1  # Constant full set, counted in both families.
    functions |= constants
    predicted = (1 + 2 ** (count - 1)) ** count + 2**count - 2
    assert len(functions) == predicted
    small = tuple(i for i, value in enumerate(values) if value.bit_count() <= 2)
    assert len({tuple(f[i] for i in small) for f in functions}) == len(functions)
    if count == 3:
        for (outer_extra, outer_rows, outer), (inner_extra, inner_rows, inner) in product(
            parameters, repeat=2
        ):
            extra = outer_extra | inner_extra
            rows = tuple(
                outer_rows[i] if not inner_rows[i]
                else (inner_rows[i] | outer_extra) & ~(1 << i)
                for i in range(count)
            )
            expected = tuple(
                value | extra if value.bit_count() >= 2
                else value | rows[value.bit_length() - 1]
                for value in values
            )
            assert tuple(outer[inner[value - 1] - 1] for value in values) == expected
    print(f"Unary forms: K={count}, {len(functions)} functions constructed and separated by singleton/pair inputs.")
    return functions


@dataclass(frozen=True)
class Node:
    role: int
    key: str
    left: object
    right: object


def profile_result(tree, actions):
    """Backward induction criterion for a fixed full profile, keeping every subgame."""
    if isinstance(tree, int):
        return tree, True
    left, left_ok = profile_result(tree.left, actions)
    right, right_ok = profile_result(tree.right, actions)
    actual = right if actions[tree.key] else left
    best = max(left == tree.role, right == tree.role)
    return actual, left_ok and right_ok and (actual == tree.role) >= best


def uniform_copy_check():
    cases = profiles = 0
    for first_owner, second_owner in product(range(3), repeat=2):
        for a, b, c, d in product(range(3), repeat=4):
            first = Node(first_owner, "G", a, b)
            second = Node(second_owner, "H", c, d)
            game = Node(2, "root", Node(0, "left", first, second),
                        Node(1, "right", first, second))
            union = set()
            for first_action, second_action in product((0, 1), repeat=2):
                component_actions = {"G": first_action, "H": second_action}
                first_winner, first_ok = profile_result(first, component_actions)
                second_winner, second_ok = profile_result(second, component_actions)
                actual = set()
                for root, left, right in product((0, 1), repeat=3):
                    actions = dict(component_actions, root=root, left=left, right=right)
                    winner, valid = profile_result(game, actions)
                    if valid:
                        actual.add(winner)
                    profiles += 1
                expected = {first_winner, second_winner} if first_ok and second_ok else set()
                assert actual == expected
                union |= actual
            target = {r for r in range(3) if own(first_owner, 1 << a, 1 << b) & (1 << r)}
            target |= {r for r in range(3) if own(second_owner, 1 << c, 1 << d) & (1 << r)}
            assert union == target
            cases += 1
    assert cases == 729 and profiles == 23328
    print(f"Uniform copies: {cases} component pairs and {profiles} full profiles passed.")


def sure_observation_check(functions):
    ambiguous_inputs = (3, 5, 6, 7)
    for function in functions:
        observations = {
            tuple(function[value - 1] == 1 << r for r in range(3))
            for value in ambiguous_inputs
        }
        assert len(observations) == 1
    print("Observations: every unary context equates all ambiguous values under unique-winner tests.")


if __name__ == "__main__":
    basic_laws()
    exhaustive = unary_closure()
    synthesized = unary_templates(3)
    assert exhaustive == synthesized
    unary_templates(4)
    sure_observation_check(exhaustive)
    uniform_copy_check()
