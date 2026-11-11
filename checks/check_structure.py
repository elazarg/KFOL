"""Cross-checks for the new arbitrary-arity representation and optimal tests."""

from functools import reduce
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

        def outcome(t, profile):
            while not isinstance(t, int):
                _, position, left, right = t
                t = right if profile[position] else left
            return t

        result = set()
        for profile in profiles:
            # Check whole-player deviations in every subgame, without using
            # either backward induction or the proposed family recurrence.
            perfect = True
            for subgame in nodes:
                actual = outcome(subgame, profile)
                for player in range(3):
                    if actual & (1 << player):
                        continue
                    for deviation in profiles:
                        if all(deviation[j] == profile[j] or node[0] == player
                               for j, node in enumerate(nodes)):
                            if outcome(subgame, deviation) & (1 << player):
                                perfect = False
                                break
                    if not perfect:
                        break
                if not perfect:
                    break
            if perfect:
                result.add(outcome(root, profile))
        return frozenset(result)

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


if __name__ == "__main__":
    quotient_checks()
    multivariable_checks()
    domain_checks()
    repetition_checks()
    congruence_checks()
    restricted_view_checks()
    bottom_extension_checks()
    winning_family_checks()
