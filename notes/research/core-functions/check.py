#!/usr/bin/env python3
"""Independently verify a ternary obstruction; no search solver is required.

This exploratory certificate is separate from the production Lean artifact.
Run: python3 notes/research/core-functions/check.py
"""

import itertools
import json
from functools import reduce
from pathlib import Path


def own(r, a, b):
    return 1 << r if 1 << r in (a, b) else a | b


def main():
    data = json.loads(Path(__file__).with_name("certificate.json").read_text())
    assert (data["roles"], data["arity"]) == (3, 3)
    domain = range(1, 8)
    valuations = list(itertools.product(domain, repeat=3))
    table = tuple(x for row in data["table"] for x in row)
    assert len(table) == 343 and all(x in domain for x in table)
    function = dict(zip(valuations, table))

    # A finite closed relation is enough; it need not be the whole generated
    # subalgebra. Every term preserves it by structural induction.
    rows = data["rows"]
    relation = {tuple(row) for row in data["relation"]}
    assert len(rows) == 6 and all(len(row) == 3 for row in rows)
    assert len(relation) == 45 and all(len(row) == 6 for row in relation)
    assert all(tuple(row[j] for row in rows) in relation for j in range(3))
    assert all(tuple(own(r, a, b) for a, b in zip(left, right)) in relation
               for r in range(3) for left in relation for right in relation)
    output = tuple(function[tuple(row)] for row in rows)
    assert output not in relation

    assert all(function[(x, x, x)] == x for x in domain)
    assert all(not out & ~reduce(int.__or__, v) for v, out in function.items())
    assert all(any(x & ~y for x, y in zip(v, w)) or not function[v] & ~function[w]
               for v in valuations for w in valuations)
    ambiguous = (3, 5, 6, 7)
    assert all(function[v] == reduce(int.__or__, v)
               for v in itertools.product(ambiguous, repeat=3))

    # On a status cell, every output is a fixed constant union together with
    # a fixed selection of its ambiguous inputs.
    for status in itertools.product((1, 2, 4, 0), repeat=3):
        vs = list(itertools.product(*(ambiguous if s == 0 else (s,) for s in status)))
        assert any(all(function[v] == constant | reduce(int.__or__,
                       (a for j, a in enumerate(v) if selected & (1 << j)), 0)
                       for v in vs)
                   for constant in range(8) for selected in range(8)
                   if all(not selected & (1 << j) or status[j] == 0 for j in range(3)))

    # Every finite disjoint-region common-source test, including one region.
    masks = {region: set() for region in domain}
    for v, out in function.items():
        for region in domain:
            if not out & ~region:
                masks[region].add(sum(1 << j for j, x in enumerate(v) if not x & ~region))
    for count in (1, 2, 3):
        for regions in itertools.combinations(domain, count):
            if any(a & b for a, b in itertools.combinations(regions, 2)):
                continue
            assert all(reduce(int.__and__, selection, 7)
                       for selection in itertools.product(*(masks[r] for r in regions)))

    # The independently proved unary-polynomial normal forms: constants, or
    # increment U on ambiguous inputs and {i} union B_i on atom i, with
    # B_i contained in U minus {i}.
    polynomials = {(c,) * 7 for c in domain}
    for increment in range(8):
        choices = [[b for b in range(8) if not b & ~(increment & ~(1 << i))]
                   for i in range(3)]
        for atomic in itertools.product(*choices):
            polynomials.add(tuple((x | atomic[x.bit_length() - 1])
                                  if x.bit_count() == 1 else x | increment for x in domain))
    assert len(polynomials) == 131
    identity = tuple(domain)
    for left, middle, right in itertools.product(polynomials, repeat=3):
        result = tuple(table[(a - 1) * 49 + (b - 1) * 7 + c - 1]
                       for a, b, c in zip(left, middle, right))
        assert result in polynomials
        assert result != identity or left == middle == right == identity
    print("Verified: nonterm obstruction on a closed 45-row relation; idempotence,")
    print("monotonicity, support, cell provenance, common source, and all 131^3")
    print("unary-polynomial substitutions, including strict identity reflection.")


if __name__ == "__main__":
    main()
