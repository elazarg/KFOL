"""Finite instances of the paper's public and observation semantics.

This is an executable model check, not a proof-assistant formalization.
It compares full off-path policy tables with reduced endpoint plans, tests
complete traces and returns, and transports the same plans across role names.
"""

from dataclasses import dataclass
from itertools import permutations, product


@dataclass(frozen=True)
class Script:
    owners: tuple
    domains: tuple
    returns: tuple

    @property
    def roles(self):
        return len(self.returns)


@dataclass(frozen=True)
class Return:
    value: object


@dataclass(frozen=True)
class Send:
    value: object
    continuation: object


@dataclass(frozen=True)
class Receive:
    branches: dict


def reduce_policy(script, tables, role, history=()):
    """Reduce one role's full table, retaining every opposing-input branch."""
    position = len(history)
    if position == len(script.owners):
        return Return(script.returns[role](history))
    domain = tuple(script.domains[position](history))
    if script.owners[position] == role:
        value = tables[position][history]
        assert value in domain
        return Send(value, reduce_policy(script, tables, role, history + (value,)))
    return Receive({
        value: reduce_policy(script, tables, role, history + (value,))
        for value in domain
    })


def run_plans(script, plans):
    history = ()
    for position, owner in enumerate(script.owners):
        sender = plans[owner]
        assert isinstance(sender, Send)
        value = sender.value
        assert value in script.domains[position](history)
        next_plans = []
        for role, plan in enumerate(plans):
            if role == owner:
                next_plans.append(sender.continuation)
            else:
                assert isinstance(plan, Receive)
                assert set(plan.branches) == set(script.domains[position](history))
                next_plans.append(plan.branches[value])
        plans = tuple(next_plans)
        history += (value,)
    assert all(isinstance(plan, Return) for plan in plans)
    return history, tuple(plan.value for plan in plans)


def run_tables(script, tables):
    history = ()
    for position in range(len(script.owners)):
        value = tables[position][history]
        assert value in script.domains[position](history)
        history += (value,)
    return history, tuple(result(history) for result in script.returns)


def rename(script, role_permutation):
    inverse = tuple(role_permutation.index(i) for i in range(script.roles))
    return Script(
        tuple(role_permutation[i] for i in script.owners),
        script.domains,
        tuple(script.returns[inverse[i]] for i in range(script.roles)),
    )


def exhaustive_public_check():
    policy_tables = []
    for position in range(3):
        histories = tuple(product((0, 1), repeat=position))
        policy_tables.append(tuple(
            dict(zip(histories, values))
            for values in product((0, 1), repeat=len(histories))
        ))
    total = renamed = 0
    for owners in product(range(3), repeat=3):
        script = Script(
            owners,
            (lambda _: (0, 1),) * 3,
            (lambda h: h[0] == h[1], lambda h: h[1] == h[2], lambda h: h[0] ^ h[2]),
        )
        for tables in product(*policy_tables):
            plans = tuple(reduce_policy(script, tables, i) for i in range(3))
            expected = run_tables(script, tables)
            assert run_plans(script, plans) == expected
            for permutation in permutations(range(3)):
                inverse = tuple(permutation.index(i) for i in range(3))
                transported = tuple(plans[inverse[i]] for i in range(3))
                actual = run_plans(rename(script, permutation), transported)
                assert actual == (expected[0], tuple(expected[1][inverse[i]] for i in range(3)))
                renamed += 1
            total += 1
    assert total == 3456 and renamed == 20736
    print(f"Public core: {total} full profiles and {renamed} role transports passed.")


def dependent_check():
    script = Script(
        (0, 1, 2),
        (lambda _: (1, 2),
         lambda h: tuple(product((False, True), repeat=h[0])),
         lambda h: tuple(range(h[0]))),
        (lambda h: h[1][h[2]], lambda h: h[2], lambda h: h[1]),
    )
    cases = 0
    for n in (1, 2):
        for vector in product((False, True), repeat=n):
            for index in range(n):
                first = {(): n}
                second = {(m,): (vector if m == n else (True,) * m) for m in (1, 2)}
                third = {
                    (m, values): (index if (m, values) == (n, vector) else 0)
                    for m in (1, 2)
                    for values in product((False, True), repeat=m)
                }
                tables = (first, second, third)
                plans = tuple(reduce_policy(script, tables, i) for i in range(3))
                execution = run_plans(script, plans)
                assert execution == run_tables(script, tables)
                assert execution == ((n, vector, index), (vector[index], index, vector))
                cases += 1
    print(f"Dependent domains: {cases} vector/index executions passed.")


def reachable(worlds, observations, start):
    seen = {start}
    remaining = [start]
    while remaining:
        current = remaining.pop()
        for observe in observations:
            for candidate in worlds:
                if observe(current) == observe(candidate) and candidate not in seen:
                    seen.add(candidate)
                    remaining.append(candidate)
    return seen


def knowledge_check():
    worlds = tuple(product((0, 1), repeat=2))
    before = (lambda h: h[0], lambda h: h[1], lambda _: ())
    after = (lambda h: h[0], lambda h: (h[1], h[0]), lambda h: h[0])
    public = lambda h: h[0]
    for start in worlds:
        assert any(public(h) != public(start) for h in reachable(worlds, before, start))
        for observe in after:
            for left, right in product(worlds, repeat=2):
                assert observe(left) != observe(right) or public(left) == public(right)
        assert all(public(h) == public(start) for h in reachable(worlds, after, start))
    # Everyone can know at the actual world while common knowledge fails.
    worlds = (0, 1, 2)
    observations = (lambda h: 0 if h in (0, 1) else 1,
                    lambda h: 0 if h == 0 else 1)
    fact = lambda h: h in (0, 1)
    assert all(all(fact(h) for h in worlds if observe(h) == observe(0))
               for observe in observations)
    assert not all(fact(h) for h in reachable(worlds, observations, 0))
    print("Observations: public-readout criterion and mutual/common knowledge distinction passed.")


if __name__ == "__main__":
    exhaustive_public_check()
    dependent_check()
    knowledge_check()
    print("Finite checks passed; mathematical proofs are in the manuscript.")
