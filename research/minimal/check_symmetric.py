"""Finite cross-checks for the primary signature with internal role switching."""

from itertools import combinations, permutations, product
from random import Random

from structure import Choice, Var, Win, test_values
from symmetric import (Rename, ambiguity_action, constant, evaluate, pair_separator,
                       partial_permutations_three, provenance, realize, regular,
                       small_values, unary_closure_three, unary_template_three)


def unary_classification():
    forms = set()
    by_rank = {r: 0 for r in range(4)}
    partials = list(partial_permutations_three())
    for partial in partials:
        extra = 7 ^ sum(1 << j for j in partial.values())
        allowed_rows = []
        for i in range(3):
            allowed = extra | ((1 << partial[i]) if i in partial else 0)
            mandatory = (1 << partial[i]) if i in partial else 0
            allowed_rows.append([row for row in range(1, 8)
                                 if not row & ~allowed and row & mandatory == mandatory])
        for rows in product(*allowed_rows):
            expected = tuple(rows[s.bit_length() - 1] if s.bit_count() == 1
                             else ambiguity_action(partial, s) for s in range(1, 8))
            term = unary_template_three(partial, rows)
            actual = tuple(evaluate(term, (s,)) for s in range(1, 8))
            assert actual == expected, (partial, rows, actual, expected)
            assert expected not in forms
            forms.add(expected)
            by_rank[len(partial)] += 1
    assert by_rank == {0: 343, 1: 324, 2: 72, 3: 6}
    assert len(forms) == 745
    for value in range(1, 8):
        term = constant(3, value)
        actual = tuple(evaluate(term, (s,)) for s in range(1, 8))
        assert actual == (value,) * 7
        forms.add(actual)
    assert len(forms) == 751
    exhaustive = unary_closure_three()
    assert forms == exhaustive
    for outer, inner in product(partials, repeat=2):
        composed = {i: outer[j] for i, j in inner.items() if j in outer}
        assert all(ambiguity_action(outer, ambiguity_action(inner, s)) ==
                   ambiguity_action(composed, s) for s in (3, 5, 6, 7))
    print("Symmetric unary clone K=3: 751 functions; every normal form synthesized by an actual term; independent closure agrees.")
    print(f"Top-preserving part: 745 functions, rank fibers {by_rank}; quotient is the 34-element symmetric inverse monoid.")


def necessity_witnesses():
    for count in range(3, 7):
        for a, b in combinations(range(count), 2):
            pair = (1 << a) | (1 << b)
            first, second = pair_separator(count, pair)
            differences = [s for s in range(1, 1 << count)
                           if evaluate(first, (s,)) != evaluate(second, (s,))]
            assert differences == [pair]
        for i in range(count):
            full = (1 << count) - 1
            k = (i + 1) % count
            rows = tuple(full & ~(1 << j) & (~(1 << k) if j == i else full) for j in range(count))
            separator = regular(count, full, rows)
            differences = [s for s in range(1, 1 << count) if evaluate(separator, (s,)) != full]
            assert differences == [1 << i]
    first, second = pair_separator(4, 5)
    assert all(evaluate(first, (s,)) == evaluate(second, (s,)) for s in test_values(4))
    assert evaluate(first, (5,)) != evaluate(second, (5,))
    print("Sharp symmetric tests: singleton and pair separators verified for K=3..6; the bare K+2 domain fails with role switching.")


def random_term(rng, count, arity, depth):
    if depth == 0 or rng.randrange(5) == 0:
        return Var(rng.randrange(arity)) if rng.randrange(2) else Win(rng.randrange(count))
    if rng.randrange(3) == 0:
        permutation = list(range(count))
        rng.shuffle(permutation)
        return Rename(tuple(permutation), random_term(rng, count, arity, depth - 1))
    return Choice(rng.randrange(count), random_term(rng, count, arity, depth - 1),
                  random_term(rng, count, arity, depth - 1))


def pair_sufficiency_checks():
    rng = Random(20261029)
    cases = 0
    for count, arity, samples in ((3, 2, 100), (4, 2, 80), (3, 3, 50)):
        tables = {}
        for _ in range(samples):
            term = random_term(rng, count, arity, 5)
            table = []
            for inputs in product(range(1, 1 << count), repeat=arity):
                actual = evaluate(term, inputs)
                statuses = tuple(s.bit_length() - 1 if s.bit_count() == 1 else count for s in inputs)
                form = provenance(term, statuses, count)
                assert realize(form, inputs) == actual
                table.append(actual)
                cases += 1
            small = tuple(evaluate(term, inputs) for inputs in product(small_values(count), repeat=arity))
            table = tuple(table)
            assert small not in tables or tables[small] == table
            tables[small] = table
    print(f"Symmetric all-arity provenance/pair tests: {cases} full binary/ternary valuations passed.")


if __name__ == "__main__":
    unary_classification()
    necessity_witnesses()
    pair_sufficiency_checks()
