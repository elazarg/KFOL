"""Cross-checks for the new arbitrary-arity representation and optimal tests."""

from functools import lru_cache, reduce
from itertools import permutations, product
from random import Random

from structure import (Choice, Var, Win, closure_congruences, equation_counterexample,
                       evaluate, evaluate_view, is_complete_domain, neutral_join, own,
                       perspective_tables, realize_form, status_form, status_tables,
                       test_values, view, view_own)


def quotient_checks():
    for count in range(3, 7):
        values = range(1, 1 << count)
        for player in range(count):
            assert len({view(player, s, count) for s in values}) == count + 1
            assert all(view(player, own(owner, a, b), count) ==
                       view_own(player, owner, view(player, a, count),
                                view(player, b, count), count)
                       for owner in range(count) for a, b in product(values, repeat=2))
        assert len({tuple(view(p, s, count) for p in range(count)) for s in values}) == len(values)
    print("Perspectives: exact K+1-state quotients and faithful product passed for K=3..6.")


def random_term(rng, count, arity, depth):
    if depth == 0 or rng.randrange(4) == 0:
        return Var(rng.randrange(arity)) if rng.randrange(2) else Win(rng.randrange(count))
    return Choice(rng.randrange(count), random_term(rng, count, arity, depth - 1),
                  random_term(rng, count, arity, depth - 1))


def multivariable_checks():
    rng = Random(20261028)
    cases = 0
    for count, arity, samples in ((3, 2, 140), (4, 2, 100), (3, 3, 50)):
        terms = [Var(j) for j in range(arity)] + [Win(i) for i in range(count)]
        terms += [random_term(rng, count, arity, 5) for _ in range(samples)]
        # Guaranteed equations/non-equations exercise more than random collisions.
        terms += [neutral_join(Var(0), Var(1)), neutral_join(Var(1), Var(0))]
        interpretations = {}
        perspective_forms = {}
        provenance_forms = {}
        small_forms = {}
        for term in terms:
            table = []
            for inputs in product(range(1, 1 << count), repeat=arity):
                actual = evaluate(term, inputs)
                statuses = tuple(v.bit_length() - 1 if v.bit_count() == 1 else count for v in inputs)
                assert realize_form(status_form(term, statuses, count), inputs) == actual
                assert all(evaluate_view(term, tuple(view(p, s, count) for s in inputs), p, count)
                           == view(p, actual, count) for p in range(count))
                table.append(actual)
                cases += 1
            table = tuple(table)
            for form, dictionary in (
                (perspective_tables(term, count, arity), perspective_forms),
                (status_tables(term, count, arity), provenance_forms),
                (tuple(evaluate(term, inputs) for inputs in
                       product(test_values(count), repeat=arity)), small_forms)
            ):
                assert form not in dictionary or dictionary[form] == table
                dictionary[form] = table
            assert table not in interpretations or interpretations[table] == status_tables(term, count, arity)
            interpretations[table] = status_tables(term, count, arity)
    print(f"Arbitrary-arity representations: {cases} full valuations passed (binary/ternary terms).")


def domain_checks():
    from check_choice import unary_templates
    for count in (3, 4):
        functions = unary_templates(count)
        atoms = {1 << i for i in range(count)}
        extras = tuple(v for v in range(1, 1 << count) if v not in atoms)
        complete = []
        for mask in range(1 << len(extras)):
            domain = atoms | {v for j, v in enumerate(extras) if mask & (1 << j)}
            # Unary separation already characterizes the all-arity domains.
            observed = {tuple(f[v - 1] for v in sorted(domain)) for f in functions}
            separates = len(observed) == len(functions)
            assert separates == is_complete_domain(domain, count)
            if separates:
                complete.append(domain)
        minimum = min(map(len, complete))
        assert minimum == (6 if count == 3 else count + 2)
        assert is_complete_domain(set(test_values(count)), count)
        print(f"Optimal fixed tests: K={count}, all {1 << len(extras)} atom-containing domains checked; minimum={minimum}.")
    x = Var(0)
    d = Choice(2, x, Choice(1, Choice(0, x, Win(1)), Win(0)))
    assert equation_counterexample(d, x, 3, 1) is not None


def repetition_checks():
    from check_choice import unary_templates
    for count in (3, 4):
        functions = unary_templates(count)
        def lift(f):
            return tuple(reduce(int.__or__, (f[(1 << i) - 1] for i in range(count)
                         if s & (1 << i)), 0) for s in range(1, 1 << count))
        lifted = {lift(f) for f in functions}
        fixed = {f for f in functions if f == lift(f)}
        assert len(lifted) == 2 ** (count * (count - 1)) + 2**count - 2
        assert len(fixed) == (count + 1) ** count + 2**count - 2
        if count == 4:
            # Rows: only singleton a gains d; every ambiguous input gains d.
            f = tuple((s | 8) if s.bit_count() > 1 or s == 1 else s for s in range(1, 16))
            assert f in functions
            assert lift(f) not in functions
        print(f"Repetition: K={count}, {len(lifted)} uniform functions, {len(fixed)} ordinary functions preserved by uniform lifting.")
    x = Var(0)
    d = Choice(2, x, Choice(1, Choice(0, x, Win(1)), Win(0)))
    h = neutral_join(x, Win(2))
    # Uniform equality D(x)=x is destroyed by substituting H(x) for x.
    dh = Choice(2, h, Choice(1, Choice(0, h, Win(1)), Win(0)))
    assert all(evaluate(d, (1 << i,)) == 1 << i for i in range(3))
    assert evaluate(dh, (1,)) == 7 and evaluate(h, (1,)) == 5


def partitions(n):
    labels = [0] * n
    def visit(i, maximum):
        if i == n:
            yield tuple(labels)
            return
        for label in range(maximum + 2):
            labels[i] = label
            yield from visit(i + 1, max(label, maximum))
    yield from visit(1, 0)


def congruence_checks():
    derived = {}
    for count, expected in ((3, 18), (4, 626)):
        congruences = closure_congruences(count)
        assert len(congruences) == expected
        values = range(1, 1 << count)
        for classes in congruences:
            assert all(classes[own(r, a, b) - 1] ==
                       classes[own(r, classes[a - 1], classes[b - 1]) - 1]
                       for r in range(count) for a, b in product(values, repeat=2))
        def relation(classes):
            return sum(1 << n for n, (a, b) in enumerate(product(values, repeat=2))
                       if classes[a - 1] == classes[b - 1])
        relations = {relation(c): c for c in congruences}
        irreducible = set()
        for rel in relations:
            above = [other for other in relations if other != rel and not rel & ~other]
            if above:
                meet = above[0]
                for other in above[1:]:
                    meet &= other
                if meet != rel:
                    irreducible.add(rel)
        expected_irreducible = set()
        full = (1 << count) - 1
        for subset in range(1, full):
            classes = tuple(v if v.bit_count() == 1 and not v & ~subset
                            else subset if not v & ~subset else full for v in values)
            expected_irreducible.add(relation(classes))
            assert len(set(classes)) == (2 if subset.bit_count() == 1 else subset.bit_count() + 2)
        assert irreducible == expected_irreducible
        assert len(irreducible) == (1 << count) - 2
        symmetric = set()
        for rel, classes in relations.items():
            stable = True
            for perm in permutations(range(count)):
                image = {v: sum(1 << perm[i] for i in range(count) if v & (1 << i)) for v in values}
                if any(classes[image[a] - 1] != classes[image[b] - 1]
                       for a, b in product(values, repeat=2) if classes[a - 1] == classes[b - 1]):
                    stable = False
                    break
            if stable:
                symmetric.add(rel)
        expected_symmetric = {
            relation(tuple(v if v.bit_count() <= cutoff else full for v in values))
            for cutoff in range(count)
        }
        assert symmetric == expected_symmetric
        print(f"Irreducible quotients: K={count}, {len(irreducible)} kernels; symmetry leaves a {len(symmetric)}-element congruence chain.")
        derived[count] = congruences
    independent = set()
    for partition in partitions(7):
        valid = True
        for role in range(3):
            operation = {}
            for a, b in product(range(1, 8), repeat=2):
                key = partition[a - 1], partition[b - 1]
                output = partition[own(role, a, b) - 1]
                if key in operation and operation[key] != output:
                    valid = False
                    break
                operation[key] = output
            if not valid:
                break
        if valid:
            independent.add(tuple(reduce(int.__or__,
                (v for v in range(1, 8) if partition[v - 1] == partition[a - 1]), 0)
                for a in range(1, 8)))
    assert independent == derived[3]
    print("Congruences: 18 at K=3 (independent exhaustive partitions); 626 at K=4 (closure-family construction).")


def restricted_view_checks():
    cases = 0
    for count in range(3, 6):
        values = tuple(range(1, 1 << count))
        for player in range(count):
            for owner_mask in range(1 << count):
                owners = tuple(r for r in range(count) if owner_mask & (1 << r))
                translations = tuple((r, c) for r in owners for c in values)
                # Compute the contextual congruence independently by refining
                # membership until every unary translation respects the partition.
                classes = {v: bool(v & (1 << player)) for v in values}
                while True:
                    signatures = {}
                    refined = {}
                    for v in values:
                        key = (classes[v], tuple(classes[own(r, v, c)]
                                                 for r, c in translations))
                        refined[v] = signatures.setdefault(key, len(signatures))
                    if len(set(refined.values())) == len(set(classes.values())):
                        classes = refined
                        break
                    classes = refined

                def expected(v):
                    if v & (1 << player):
                        return player
                    if v.bit_count() == 1 and v.bit_length() - 1 in owners:
                        return v.bit_length() - 1
                    return count

                assert all((classes[a] == classes[b]) == (expected(a) == expected(b))
                           for a, b in product(values, repeat=2))
                assert len(set(classes.values())) == len(set(owners) - {player}) + 2
                if owners:
                    units = {classes[e] for e in values
                             if all(classes[own(r, e, v)] == classes[v]
                                    for r in owners for v in values)}
                    negative = next(v for v in values if expected(v) == count)
                    assert units == ({classes[negative]} if len(owners) == 1 else set())
                cases += 1
    print(f"Restricted views: {cases} observer/owner partitions independently refined; exact unit criterion passed (K=3..5).")


def bottom_extension_checks():
    def zero_choice(r, a, b):
        return own(r, a, b) if a and b else 0

    def derived_join(operation, a, b):
        return operation(2, operation(0, a, b), operation(1, a, b))

    for count in range(3, 6):
        values = range(1 << count)
        for a, b in product(values, repeat=2):
            assert derived_join(own, a, b) == a | b
            assert derived_join(zero_choice, a, b) == (a | b if a and b else 0)
        for r in range(count):
            for a in values:
                assert own(r, 0, a) == a
                assert zero_choice(r, 0, a) == 0
                assert own(r, a, a) == zero_choice(r, a, a) == a
            for a, b, c in product(values, repeat=3):
                assert own(r, own(r, a, b), c) == own(r, a, own(r, b, c))
                assert zero_choice(r, zero_choice(r, a, b), c) == zero_choice(r, a, zero_choice(r, b, c))
                assert zero_choice(r, a, b | c) == zero_choice(r, a, b) | zero_choice(r, a, c)
            other = 1 << ((r + 1) % count)
            atom = 1 << r
            assert own(r, other, 0 | atom) == atom
            assert own(r, other, 0) | own(r, other, atom) == other | atom
    print("Bottom extensions: unit and annihilator laws, derived unions and the distributivity obstruction passed (K=3..5).")


def full_profile_outcomes(tree, payoff, subgame_perfect=True):
    nodes = []

    def index(t):
        if isinstance(t, int):
            return t
        owner, left, right = t
        position = len(nodes)
        nodes.append(None)
        node = (owner, position, index(left), index(right))
        nodes[position] = node
        return node

    root = index(tree)
    profiles = tuple(product((0, 1), repeat=len(nodes)))
    controllers = {node[0] for node in nodes}
    subgames = nodes if subgame_perfect else nodes[:1]

    def outcome(t, profile):
        while not isinstance(t, int):
            _, position, left, right = t
            t = right if profile[position] else left
        return t

    result = set()
    for profile in profiles:
        # Enumerate whole-controller deviations at the root or every subgame.
        # Neither backward induction nor an algebraic recurrence is used.
        perfect = True
        for subgame in subgames:
            actual = outcome(subgame, profile)
            for controller in controllers:
                for deviation in profiles:
                    if all(deviation[j] == profile[j] or node[0] == controller
                           for j, node in enumerate(nodes)):
                        if payoff(controller, outcome(subgame, deviation)) > payoff(controller, actual):
                            perfect = False
                            break
                if not perfect:
                    break
            if not perfect:
                break
        if perfect:
            result.add(outcome(root, profile))
    return frozenset(result)


def unrepeated_ownership_checks():
    def structural_values(tree):
        if isinstance(tree, int):
            return (1 << tree,) * 3
        owner, left, right = tree
        left_leaves, left_pruned, left_actual = structural_values(left)
        right_leaves, right_pruned, right_actual = structural_values(right)
        atom = 1 << owner
        pruned = atom if atom in (left_leaves, right_leaves) else left_pruned | right_pruned
        return left_leaves | right_leaves, pruned, own(owner, left_actual, right_actual)

    def check(tree):
        leaves, pruned, actual = structural_values(tree)
        assert pruned == actual and actual & ~leaves == 0
        payoff = lambda controller, winner: int(controller == winner)
        spe = full_profile_outcomes(tree, payoff)
        nash = full_profile_outcomes(tree, payoff, subgame_perfect=False)
        assert spe == nash
        assert reduce(int.__or__, (1 << winner for winner in spe), 0) == pruned
        return pruned

    @lru_cache(None)
    def games(nodes, ancestors=()):
        if nodes == 0:
            return tuple(range(3))
        return tuple((owner, left, right)
                     for owner in range(3) if owner not in ancestors
                     for left_size in range(nodes)
                     for left in games(left_size, ancestors + (owner,))
                     for right in games(nodes - 1 - left_size, ancestors + (owner,)))

    cases = 0
    for nodes in range(4):
        for tree in games(nodes):
            check(tree)
            cases += 1
    print(f"Unrepeated ownership: structural pruning and Nash/SPE winner equality passed on all {cases} three-role games with at most three choices.")

    @lru_cache(None)
    def shapes(nodes):
        if nodes == 0:
            return (None,)
        return tuple((left, right) for left_size in range(nodes)
                     for left in shapes(left_size)
                     for right in shapes(nodes - 1 - left_size))

    def label(shape, owners, winners):
        if shape is None:
            return next(winners)
        owner = next(owners)
        return (owner, label(shape[0], owners, winners), label(shape[1], owners, winners))

    matched = 0
    for nodes in range(5):
        for shape in shapes(nodes):
            for owners in permutations(range(nodes + 1), nodes):
                winners = iter(range(nodes + 1))
                tree = label(shape, iter(owners), winners)
                assert next(winners, None) is None
                pruned = check(tree)
                if nodes:
                    owner, left, right = tree
                    immediate = any(isinstance(child, int) and child == owner
                                    for child in (left, right))
                    assert (pruned.bit_count() == 1) == immediate
                matched += 1
    print(f"Injective matching: all {matched} binary trees/matchings through four choices passed; singleton winners are exactly immediate root matches.")


def winning_family_checks():
    def family(tree):
        if isinstance(tree, int):
            return frozenset({tree})
        owner, left, right = tree
        first, second = family(left), family(right)
        winners = frozenset(w for w in first | second if w & (1 << owner))
        if all(w & (1 << owner) for w in first) or all(w & (1 << owner) for w in second):
            return winners
        return first | second

    def full_profile_family(tree):
        return full_profile_outcomes(tree, lambda player, winners: (winners >> player) & 1)

    cases = 0
    for leaf in range(8):
        assert family(leaf) == full_profile_family(leaf)
        cases += 1
    for owner, a, b in product(range(3), range(8), range(8)):
        tree = (owner, a, b)
        assert family(tree) == full_profile_family(tree)
        cases += 1
    for r, s, a, b, c in product(range(3), range(3), range(8), range(8), range(8)):
        for tree in ((r, (s, a, b), c), (r, a, (s, b, c))):
            assert family(tree) == full_profile_family(tree)
            cases += 1
    draw_or_a, certain_a = (1, 0, 1), 1
    assert family(draw_or_a) == frozenset({0, 1})
    assert reduce(int.__or__, family(draw_or_a), 0) == certain_a
    assert family((0, draw_or_a, 2)) == frozenset({0, 1, 2})
    assert family((0, certain_a, 2)) == frozenset({1})
    print(f"Winning-set families: {cases} games with arbitrary terminal coalitions checked against full-profile SPE deviations; draw obstruction passed.")


def collective_choice(goal, left, right):
    union = left | right
    return union & goal if not left & ~goal or not right & ~goal else union


def collective_checks():
    for count in range(3, 6):
        values = range(1, 1 << count)
        for goal in range(1 << count):
            for a in values:
                assert collective_choice(goal, a, a) == a
            for a, b in product(values, repeat=2):
                result = collective_choice(goal, a, b)
                assert result == collective_choice(goal, b, a) and result
                # Independent pointwise optimality of the two fixed outcomes.
                expected = 0
                for i in range(count):
                    if not a & (1 << i):
                        continue
                    for j in range(count):
                        if b & (1 << j):
                            first, second = (goal >> i) & 1, (goal >> j) & 1
                            if first >= second:
                                expected |= 1 << i
                            if second >= first:
                                expected |= 1 << j
                assert result == expected
                delegates = reduce(int.__or__, (own(r, a, b) for r in range(count)
                                                if goal & (1 << r)), 0)
                if goal.bit_count() >= 2:
                    assert delegates == a | b
                if goal.bit_count() == 1:
                    assert result == delegates
                if goal in (0, (1 << count) - 1):
                    assert result == a | b
            for a, b, c in product(values, repeat=3):
                assert collective_choice(goal, collective_choice(goal, a, b), c) == collective_choice(goal, a, collective_choice(goal, b, c))
                assert collective_choice(goal, a, b | c) == collective_choice(goal, a, b) | collective_choice(goal, a, c)
            if 2 <= goal.bit_count() < count:
                member = goal & -goal
                outsider = next(1 << i for i in range(count) if not goal & (1 << i))
                other = member | outsider
                assert goal.bit_count() >= 2 and other.bit_count() == 2
                assert collective_choice(goal, goal, other) == goal != goal | other

    assert own(0, 1, 2) & own(1, 1, 2) == 0
    assert collective_choice(3, 3, 4) == 3 < (own(0, 3, 4) & own(1, 3, 4))
    assert collective_choice(3, 1, collective_choice(4, 2, 4)) == 1
    assert collective_choice(4, collective_choice(3, 1, 2), collective_choice(3, 1, 4)) == 3
    print("Collective choice: pointwise optimality, semilattice and union laws, delegation and nondefinability witnesses passed (K=3..5).")

    cases = 0
    for count in range(3, 6):
        values = range(1, 1 << count)
        for partition in partitions(count):
            teams = max(partition) + 1
            if teams < 3:
                continue
            blocks = tuple(sum(1 << i for i in range(count) if partition[i] == j)
                           for j in range(teams))

            def quotient(value):
                return sum(1 << j for j, block in enumerate(blocks) if value & block)

            def embed(value):
                return reduce(int.__or__, (block for j, block in enumerate(blocks)
                                          if value & (1 << j)), 0)

            def observer(player, value):
                own_team = partition[player]
                if value & (1 << player):
                    return own_team
                for j, block in enumerate(blocks):
                    if j != own_team and not value & ~block:
                        return j
                return teams

            coarse_values = range(1, 1 << teams)
            assert all(quotient(embed(v)) == v for v in coarse_values)
            assert all(len({observer(i, v) for v in values}) == teams + 1
                       for i in range(count))
            for r, goal in enumerate(blocks):
                assert all(embed(own(r, a, b)) == collective_choice(goal, embed(a), embed(b))
                           for a, b in product(coarse_values, repeat=2))
                for a, b in product(values, repeat=2):
                    result = collective_choice(goal, a, b)
                    assert quotient(result) == own(r, quotient(a), quotient(b))
                    for i in range(count):
                        assert observer(i, result) == view_own(partition[i], r,
                            observer(i, a), observer(i, b), teams)
                    joined = collective_choice(blocks[2], collective_choice(blocks[0], a, b), collective_choice(blocks[1], a, b))
                    assert joined == a | b
            cases += 1
    print(f"Team refinement: split maps and every observer homomorphism checked on {cases} partitions with at least three teams (K=3..5).")

    def evaluate_collective(tree):
        if isinstance(tree, int):
            return 1 << tree
        goal, left, right = tree
        return collective_choice(goal, evaluate_collective(left), evaluate_collective(right))

    def check_game(tree):
        value = evaluate_collective(tree)
        predicted = frozenset(i for i in range(3) if value & (1 << i))
        actual = full_profile_outcomes(tree, lambda goal, winner: (goal >> winner) & 1)
        assert actual == predicted

    games = 0
    for leaf in range(3):
        check_game(leaf)
        games += 1
    for goal, a, b in product(range(8), range(3), range(3)):
        check_game((goal, a, b))
        games += 1
    for first, second, a, b, c in product(range(8), range(8), range(3), range(3), range(3)):
        for tree in ((first, (second, a, b), c), (first, a, (second, b, c))):
            check_game(tree)
            games += 1
    print(f"Collective SPE: {games} games with arbitrary overlapping controller goals checked against full-profile deviations.")


if __name__ == "__main__":
    quotient_checks()
    multivariable_checks()
    domain_checks()
    repetition_checks()
    congruence_checks()
    restricted_view_checks()
    bottom_extension_checks()
    unrepeated_ownership_checks()
    winning_family_checks()
    collective_checks()
