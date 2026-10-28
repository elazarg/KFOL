"""Independent finite checks of the general-K results; not formal proofs."""

from itertools import product
from random import Random

from ambiguity import all_rows, apply, canonical, compose, factorpower, matching, synthesize, witnesses
from structure import own
from symmetric import evaluate


def check_actions(count):
    full = (1 << count) - 1
    ambiguous = [s for s in range(1, full + 1) if s.bit_count() >= 2]
    proposed = all_rows(count)
    relations = factorpower(count)
    independent = {canonical(c, r) for r in relations for c in range(full + 1)}
    assert proposed == independent
    # Canonical forms are semantically unique, independently of their criterion.
    tables = {tuple(apply(rows, s) for s in ambiguous) for rows in proposed}
    assert len(tables) == len(proposed)
    ordered = sorted(proposed)
    rng = Random(count)
    pairs = product(ordered, repeat=2) if count == 3 else (
        (rng.choice(ordered), rng.choice(ordered)) for _ in range(10000))
    for outer, inner in pairs:
        result = compose(outer, inner)
        assert result in proposed
        for s in ambiguous:
            assert apply(result, s) == apply(outer, apply(inner, s))
    sample = ordered if count == 3 else rng.sample(ordered, 100)
    for rows in sample:
        term = synthesize(rows)
        for s in ambiguous:
            assert evaluate(term, (s,)) == apply(rows, s)
    print(f"K={count}: {len(relations)} factorpower relations; "
          f"{len(proposed)} canonical ambiguity actions; independent enumerations agree")


def check_boolean_reduction():
    # Every monotone circuit on these two values has exactly Boolean semantics.
    for count in range(3, 7):
        full = (1 << count) - 1
        for a in range(count):
            b = (a + 1) % count
            val = lambda bit: 1 << a if bit else full
            for x in range(1, full + 1):
                assert own(a, x, full) == val(x == 1 << a)
            for x, y in product((False, True), repeat=2):
                assert own(a, val(x), val(y)) == val(x or y)
                assert own(b, val(x), val(y)) == val(x and y)
    # Check the dual-rail witness equivalence for every CNF with up to
    # three clauses on two propositional variables, including empty clauses.
    literals = tuple(product(range(2), (False, True)))
    clauses = [tuple(literals[i] for i in range(4) if mask & (1 << i))
               for mask in range(16)]
    checked = 0
    for size in range(4):
        for cnf in product(clauses, repeat=size):
            sat = any(all(any(bits[i] == sign for i, sign in clause) for clause in cnf)
                      for bits in product((False, True), repeat=2))
            failed = False
            for rails in product((False, True), repeat=4):
                a = (all(rails[2*i] or rails[2*i+1] for i in range(2)) and
                     all(any(rails[2*i + int(not sign)] for i, sign in clause)
                         for clause in cnf))
                b = any(rails[2*i] and rails[2*i+1] for i in range(2))
                failed |= (a or b) != b
            assert sat == failed
            checked += 1
    print(f"Boolean gates K=3..6; dual-rail reduction checked on {checked} CNFs")


if __name__ == "__main__":
    check_actions(3)
    check_actions(4)
    # Hall existence alone misses an unsupported prescribed edge.
    bad = (1, 3, 15, 15)
    assert matching(bad) is not None and witnesses(bad) is None
    check_boolean_reduction()
