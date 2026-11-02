"""Native soundness and boundary checks for the atomic basis and its lifts.

The SI classification used for completeness is external (Knoebel--Romanowska,
Corollary 3.8). Here we check its two/three-element templates independently,
all displayed equations, the core abbreviations, and the D_K obstruction.
"""

from itertools import product

from core_atomic_basis import (atomic_basis, expand_core, lifting_basis,
                               variables)
from core_basis import (MIXED_JOIN, MIXED_OPERATIONS, marker_join,
                        marker_own, mixed_absorption)
from probe_core_basis import exhaustion_holds


def operation_tables(carrier, join, choice, owners):
    join_table = {(x, y): join(x, y) for x, y in product(carrier, repeat=2)}
    choices = [{(x, y): choice(i, x, y) for x, y in product(carrier, repeat=2)}
               for i in range(owners)]
    resets = {}
    for x, y in product(carrier, repeat=2):
        value = join_table[x, y]
        for table in choices:
            value = table[y, value]
        resets[x, y] = value
    return join_table, choices, resets


def truth_tables(equations, carrier, tables):
    """Evaluate shared subterms as vectors; do not assume any of the laws."""
    join, choices, resets = tables
    groups = {}
    for equation in equations:
        _, left, right = equation
        arity = 1 + max(variables(left) | variables(right))
        groups.setdefault(arity, []).append(equation)
    for arity, group in groups.items():
        assignments = tuple(product(carrier, repeat=arity))
        cache = {}

        def evaluate(term):
            if term not in cache:
                if term.op == 'var':
                    result = tuple(row[term.args[0]] for row in assignments)
                else:
                    if term.op == 'owned':
                        owner, left, right = term.args
                        operation = choices[owner]
                    else:
                        left, right = term.args
                        operation = join if term.op == 'union' else resets
                    result = tuple(operation[a, b]
                                   for a, b in zip(evaluate(left), evaluate(right)))
                cache[term] = result
            return cache[term]

        for name, left, right in group:
            yield name, evaluate(left), evaluate(right)


def assert_laws(equations, carrier, tables):
    comparisons = 0
    for name, left, right in truth_tables(equations, carrier, tables):
        assert left == right, name
        comparisons += len(left)
    return comparisons


def check_templates():
    survivors = templates = 0
    for owners in range(3, 7):
        basis = atomic_basis(owners)
        passing = []
        for pattern in product((False, True), repeat=owners):
            def choice(i, x, y):
                if 2 in (x, y):  # Common absorber in the three-state extension.
                    return 2
                return min(x, y) if pattern[i] else max(x, y)

            for size in (2, 3):
                if size == 3 and not any(pattern):
                    continue  # Not a three-element SI template.
                carrier = tuple(range(size))
                tables = operation_tables(carrier, max, choice, owners)
                holds = all(left == right for _, left, right in
                            truth_tables(basis, carrier, tables))
                assert holds == (size == 2 and sum(pattern) == 1)
                templates += 1
                if holds:
                    passing.append(pattern)
        assert len(passing) == owners
        survivors += len(passing)
    return templates, survivors


def check():
    comparisons = 0
    for owners in range(3, 7):
        basis, lifts = atomic_basis(owners), lifting_basis(owners)
        assert len(basis) == (3 * owners**2 + 7 * owners + 8) // 2
        assert len(lifts) == (3 * owners**2 + 11 * owners + 20) // 2
        assert max(len(variables(s) | variables(t)) for _, s, t in basis) == 3
        assert max(len(variables(s) | variables(t)) for _, s, t in lifts) == 4
        join = lambda x, y: marker_join(owners, x, y)
        choice = lambda i, x, y: marker_own(owners, i, x, y)
        atomic = tuple(range(owners + 1))
        comparisons += assert_laws(basis, atomic,
                                   operation_tables(atomic, join, choice, owners))

        # All observer quotients: their product separates the core generator.
        for omitted in range(owners):
            observer = tuple(x for x in range(owners + 2) if x != omitted)
            tables = operation_tables(observer, join, choice, owners)
            comparisons += assert_laws(lifts, observer, tables)
            for x, y in product(observer, repeat=2):
                assert choice(2, choice(0, x, y), choice(1, x, y)) == join(x, y)

        # These same laws hold in D_K, which still fails owner exhaustion.
        marker = tuple(range(owners + 2))
        tables = operation_tables(marker, join, choice, owners)
        comparisons += assert_laws(lifts, marker, tables)
        witness = tuple(range(owners)) + (owners + 1,)
        cover = owners
        for i in range(owners):
            cover = join(cover, choice(i, witness[-1], witness[i]))
        assert cover == owners and join(witness[-1], cover) == owners + 1

    # Independent native winner-set interpretation, with both abbreviations
    # expanded all the way to owned choices in the equations being checked.
    owners = 3
    carrier = tuple(range(1, 1 << owners))
    def choice(i, x, y):
        return 1 << i if 1 << i in (x, y) else x | y
    tables = operation_tables(carrier, lambda x, y: x | y, choice, owners)
    expanded = [(name, expand_core(left, owners), expand_core(right, owners))
                for name, left, right in lifting_basis(owners)]
    comparisons += assert_laws(expanded, carrier, tables)

    # Exhaustion does not complete the lifting theory: the earlier mixed
    # countermodel also satisfies all forty lifts and still fails absorption.
    carrier = tuple(range(6))
    tables = operation_tables(carrier, lambda x, y: MIXED_JOIN[x][y],
                              lambda i, x, y: MIXED_OPERATIONS[i][x][y], 3)
    comparisons += assert_laws(lifting_basis(3), carrier, tables)
    assert exhaustion_holds(MIXED_JOIN, MIXED_OPERATIONS)
    mixed = [('mixed_absorption', *mixed_absorption(0, 2))]
    assert any(left != right for _, left, right in truth_tables(mixed, carrier, tables))

    templates, survivors = check_templates()
    print(f'Atomic basis and uniform lifts: {comparisons} equation evaluations; '
          f'{templates} SI templates leave exactly {survivors} owner quotients '
          'at K=3..6. K=3 core expansions sound; D_K satisfies the lifts '
          'but fails exhaustion; the six-state mixed countermodel passes '
          'lifts and exhaustion. Arbitrary-algebra completeness written.')


if __name__ == '__main__':
    check()
