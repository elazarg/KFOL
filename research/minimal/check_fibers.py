"""Finite cross-checks of the common-source and two-permutation theorems."""

from itertools import product
from math import prod

from ambiguity import all_rows, witnesses
from fibers import (atomic_closure, atomic_map_term, cycles, cycle_patterns,
                    cycle_size, reset_relative, two_permutation_term, two_valued_term)
from structure import Var
from symmetric import evaluate, move


def check_cycle(permutation):
    count = len(permutation)
    components = cycles(permutation)
    patterns = list(product(*(sorted(cycle_patterns(len(c))) for c in components)))
    proposed = set()
    for pattern in patterns:
        rows = [0] * count
        for c, bits in zip(components, pattern):
            for i, bit in zip(c, bits):
                rows[i] = (1 << i if bit == 0 else 1 << permutation[i] if bit == 1
                           else (1 << i) | (1 << permutation[i]))
        proposed.add(tuple(rows))
        term = two_permutation_term(permutation, pattern)
        for value in range(1, 1 << count):
            expected = rows[value.bit_length() - 1] if value.bit_count() == 1 else value | move(permutation, value)
            assert evaluate(term, (value,)) == expected
    assert len(proposed) == prod(cycle_size(len(c)) for c in components)
    assert proposed == atomic_closure(permutation)
    print(f"Cycle lengths {tuple(map(len, components))}: exact fiber {len(proposed)}; "
          "independent closure and actual term synthesis agree")


def check_star_free_four():
    total = 0
    actions = 0
    for rows in all_rows(4):
        if 15 in rows:
            continue
        ps = witnesses(rows)
        p = ps[0]
        # Choose the other orientation of each nontrivial support component.
        q = []
        for i, image in enumerate(p):
            alternate = [k for k, row in enumerate(rows) if row & (1 << i) and k != image]
            q.append(alternate[0] if alternate else image)
        assert sorted(q) == list(range(4))
        inverse = {image: i for i, image in enumerate(p)}
        normalized = tuple(inverse[q[i]] for i in range(4))
        total += prod(cycle_size(len(c)) for c in cycles(normalized))
        actions += 1
    assert (actions, total) == (282, 6378)
    print("K=4: all 282 ambiguity actions without constant coordinates; 6378 unary functions above them")


def check_atomic_clone():
    count = 3
    inputs = tuple(product(range(count), repeat=2))
    triples = tuple(product(range(count), repeat=3))
    repeated = [t for t in triples if len(set(t)) < 3]
    # Precompute all 3-row Boolean-box tests for preservation of iota_3.
    tests = [tuple(a[i] * count + b[i] for i in range(3))
             for a, b in product(repeated, repeat=2)]
    accepted = 0
    for table in product(range(count), repeat=len(inputs)):
        preserves = all(len({table[i] for i in test}) < 3 for test in tests)
        unary = any(all(table[j] == table[k] for j, a in enumerate(inputs)
                        for k, b in enumerate(inputs) if a[col] == b[col]) for col in range(2))
        expected = len(set(table)) <= 2 or unary
        assert preserves == expected
        if not expected:
            continue
        if len(set(table)) <= 2:
            outputs = sorted(set(table))
            if len(outputs) == 1:
                mapping = [outputs[0]] * count
                term = atomic_map_term(mapping, Var(0))
            else:
                term = two_valued_term(count, 2, table, *outputs)
        else:
            col = next(col for col in range(2) if all(
                table[j] == table[k] for j, a in enumerate(inputs)
                for k, b in enumerate(inputs) if a[col] == b[col]))
            mapping = [next(table[j] for j, a in enumerate(inputs) if a[col] == label)
                       for label in range(count)]
            term = atomic_map_term(mapping, Var(col))
        assert tuple(evaluate(term, tuple(1 << i for i in value)) for value in inputs) == tuple(1 << x for x in table)
        accepted += 1
    assert accepted == 1545
    print("K=3 binary deterministic fragment: all 19683 tables tested; exactly 1545 in S_2, all synthesized")


def check_reset():
    for count in range(3, 7):
        term = reset_relative(Var(0), Var(1), count)
        for a, b in product(range(1, 1 << count), repeat=2):
            assert evaluate(term, (a, b)) == (b if b.bit_count() == 1 else a | b)
    print("Relative reset law checked on every pair at K=3..6")


if __name__ == "__main__":
    check_reset()
    # Every cycle type at K=4, plus longer and disconnected examples.
    for permutation in ((0, 1, 2, 3), (1, 0, 2, 3), (1, 0, 3, 2),
                        (1, 2, 0, 3), (1, 2, 3, 0), (1, 2, 3, 4, 0),
                        (1, 2, 3, 4, 5, 0), (1, 2, 0, 4, 5, 3)):
        check_cycle(permutation)
    check_star_free_four()
    check_atomic_clone()
