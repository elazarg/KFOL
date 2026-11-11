"""Atomic choice rules, transport, scalar SPE, and majority mechanisms."""

from functools import reduce
from itertools import product

from check_structure import full_profile_outcomes
from structure import own


def join(values):
    return reduce(int.__or__, values, 0)


def lift(rule, left, right):
    return join(rule[i][j] for i in range(len(rule)) if left & (1 << i)
                for j in range(len(rule)) if right & (1 << j))


def maximizing_rule(utility):
    return tuple(tuple((1 << i if utility[i] >= utility[j] else 0)
                       | (1 << j if utility[j] >= utility[i] else 0)
                       for j in range(len(utility))) for i in range(len(utility)))


def image(mapping, value):
    return join(1 << target for i, target in enumerate(mapping) if value & (1 << i))


def atomic_rule_checks():
    pairs = tuple((i, j) for i, j in product(range(3), repeat=2) if i != j)
    rules = transports = 0
    for selections in product(range(3), repeat=len(pairs)):
        rule = [[1 << i if i == j else 0 for j in range(3)] for i in range(3)]
        for (i, j), selection in zip(pairs, selections):
            rule[i][j] = (1 << i, 1 << j, (1 << i) | (1 << j))[selection]
        table = {(a, b): lift(rule, a, b) for a, b in product(range(1, 8), repeat=2)}
        assert all(table[a, a] == a for a in range(1, 8))
        assert all(table[a, b | c] == table[a, b] | table[a, c]
                   and table[a | b, c] == table[a, c] | table[b, c]
                   for a, b, c in product(range(1, 8), repeat=3))
        symmetric = all(rule[i][j] == rule[j][i] for i, j in pairs)
        assert symmetric == all(table[a, b] == table[b, a] for a, b in table)
        atomic_assoc = all(
            join(rule[v][k] for v in range(3) if rule[i][j] & (1 << v))
            == join(rule[i][v] for v in range(3) if rule[j][k] & (1 << v))
            for i, j, k in product(range(3), repeat=3))
        assert atomic_assoc == all(table[table[a, b], c] == table[a, table[b, c]]
                                   for a, b, c in product(range(1, 8), repeat=3))

        for mapping in product(range(2), repeat=3):
            # Choose the first observed atomic value on each coarse pair.
            # Other fine pairs may conflict, exercising necessity as well
            # as sufficiency of the atomic transport criterion.
            coarse = [[(1 << i) | (1 << j) for j in range(2)] for i in range(2)]
            seen = set()
            for i, j in product(range(3), repeat=2):
                key = mapping[i], mapping[j]
                if key not in seen:
                    coarse[key[0]][key[1]] = image(mapping, rule[i][j])
                    seen.add(key)
            compatible = all(image(mapping, rule[i][j]) == coarse[mapping[i]][mapping[j]]
                             for i, j in product(range(3), repeat=2))
            assert compatible == all(image(mapping, result)
                                     == lift(coarse, image(mapping, a), image(mapping, b))
                                     for (a, b), result in table.items())
            transports += 1
        rules += 1
    print(f"Atomic rules: all {rules} conservative rules on three outcomes; laws and {transports} transport tests passed.")


def utility_checks():
    utilities = tuple(product(range(3), repeat=3))
    for coarse in utilities:
        coarse_rule = maximizing_rule(coarse)
        for mapping in product(range(3), repeat=3):
            pulled_back = tuple(coarse[i] for i in mapping)
            fine_rule = maximizing_rule(pulled_back)
            assert all(image(mapping, lift(fine_rule, a, b))
                       == lift(coarse_rule, image(mapping, a), image(mapping, b))
                       for a, b in product(range(1, 8), repeat=2))

    def evaluate(tree):
        if isinstance(tree, int):
            return 1 << tree
        controller, left, right = tree
        return lift(maximizing_rule(utilities[controller]), evaluate(left), evaluate(right))

    def check(tree):
        predicted = evaluate(tree)
        actual = full_profile_outcomes(tree, lambda c, o: utilities[c][o])
        assert predicted == join(1 << o for o in actual)

    cases = 0
    for leaf in range(3):
        check(leaf)
        cases += 1
    for controller, a, b in product(range(27), range(3), range(3)):
        check((controller, a, b))
        cases += 1
    for first, second, a, b, c in product(range(27), range(27), range(3), range(3), range(3)):
        for tree in ((first, (second, a, b), c), (first, a, (second, b, c))):
            check(tree)
            cases += 1
    print(f"Scalar utilities: pullback transport passed; {cases} games checked against full-controller SPE deviations.")


def majority_rule(utilities):
    def pair(i, j):
        margin = sum((u[i] > u[j]) - (u[i] < u[j]) for u in utilities)
        return (1 << i if margin >= 0 else 0) | (1 << j if margin <= 0 else 0)
    return tuple(tuple(pair(i, j) for j in range(3)) for i in range(3))


def quota(sets, required):
    universe = join(sets)
    return join(1 << i for i in range(universe.bit_length())
                if sum(bool(value & (1 << i)) for value in sets) >= required)


def majority_checks():
    for utilities in product(tuple(product(range(2), repeat=3)), repeat=3):
        score = tuple(sum(u[i] for u in utilities) for i in range(3))
        assert majority_rule(utilities) == maximizing_rule(score)
        quota_one = tuple(int(s >= 1) for s in score)
        assert quota_one == tuple(int(any(u[i] for u in utilities)) for i in range(3))
        rules = tuple(maximizing_rule(u) for u in utilities)
        for required in range(1, 4):
            voted_rule = tuple(tuple(quota(tuple(rule[i][j] for rule in rules), required)
                                     for j in range(3)) for i in range(3))
            for a, b in product(range(1, 8), repeat=2):
                before = lift(voted_rule, a, b)
                after = quota(tuple(lift(rule, a, b) for rule in rules), required)
                assert not before & ~after
                if required == 1:
                    assert before == after
    for size in range(2, 6):
        # Diagonal payoffs give at most one approval to every outcome.
        assert all(int(sum(i == c for c in range(size)) >= size // 2 + 1) == 0
                   for i in range(size))
    favorites = (0, 0, 1)
    approvals = tuple(sum(f == i for f in favorites) for i in range(3))
    assert tuple(int(s >= 2) for s in approvals) == (1, 0, 0)
    before_common = ((1, 0, 1), (0, 2, 2), (1, 2, 4))
    assert lift(before_common, 3, 4) == 3
    assert quota((own(0, 3, 4), own(1, 3, 4)), 2) == 7
    for count in range(3, 7):
        for owner_mask in range(1, 1 << count):
            owners = tuple(r for r in range(count) if owner_mask & (1 << r))
            if len(owners) < 3:
                continue
            for a, b in product(range(1, 1 << count), repeat=2):
                proposed = tuple(own(r, a, b) for r in owners)
                for required in range(1, len(owners)):
                    assert quota(proposed, required) == a | b
    for a, b in product(range(1, 8), repeat=2):
        assert quota((own(0, a, b), own(0, a, b), own(1, a, b)), 2) == own(0, a, b)
    cycle = majority_rule(((2, 1, 0), (0, 2, 1), (1, 0, 2)))
    assert lift(cycle, lift(cycle, 1, 2), 4) == 4
    assert lift(cycle, 1, lift(cycle, 2, 4)) == 1

    cases = 0
    for size in (3, 5):
        for preferences in product(range(3), repeat=size):
            def payoff(voter, outcome):
                return int(preferences[voter] == outcome)

            equilibria = set()
            equilibrium_profiles = set()
            for ballots in product(range(2), repeat=size):
                outcome = int(sum(ballots) > size // 2)
                if all(payoff(voter, int(sum(ballots) + 1 - 2 * ballots[voter] > size // 2))
                       <= payoff(voter, outcome) for voter in range(size)):
                    equilibria.add(outcome)
                    equilibrium_profiles.add(ballots)
            assert equilibria == {0, 1}
            assert (0,) * size in equilibrium_profiles and (1,) * size in equilibrium_profiles
            cases += 1
    print(f"Majority: 512 binary-payoff profiles, aggregation/lifting, original-owner proposal collapse (K=3..6), a ranked cycle, and all {cases} three/five-voter preference profiles passed.")


if __name__ == "__main__":
    atomic_rule_checks()
    utility_checks()
    majority_checks()
