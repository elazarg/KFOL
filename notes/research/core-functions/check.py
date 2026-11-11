#!/usr/bin/env python3
"""Independently verify two ternary obstructions; no solver is required.

This exploratory certificate is separate from the production Lean artifact.
Run: python3 notes/research/core-functions/check.py
"""

import argparse
import itertools
import subprocess
import tempfile
from collections import Counter
from functools import reduce
from pathlib import Path


def own(r, a, b):
    return 1 << r if 1 << r in (a, b) else a | b


def cut_maxima(columns, target):
    """Independent regression implementation of maximum-value cut propagation."""
    states = list(itertools.product(*(sorted({1, 2, 4, 7, u}) for u in target)))
    maxima = {}
    rules = []
    for bound in states:
        below = [v for v in columns if all(not x & ~b for x, b in zip(v, bound))]
        maxima[bound] = tuple(reduce(int.__or__, (v[i] for v in below))
                              for i in range(len(bound))) if below else None
        for r in range(3):
            choices = [[(b, b)] + ([(1 << r, 7), (7, 1 << r)] if b & (1 << r) else [])
                       for b in bound]
            for cut in itertools.product(*choices):
                rules.append((bound, tuple(v[0] for v in cut), tuple(v[1] for v in cut), r))
    while True:
        changed = False
        for bound, left, right, r in rules:
            if maxima[left] is None or maxima[right] is None:
                continue
            value = tuple(own(r, a, b) for a, b in zip(maxima[left], maxima[right]))
            old = maxima[bound]
            value = tuple(a | b for a, b in zip(old, value)) if old is not None else value
            if value != old:
                maxima[bound] = value
                changed = True
        if not changed:
            return maxima[target]


def four_patches(valuation):
    x, y, z = valuation
    h = own(1, x, y)
    t = own(0, y, z)
    return (own(2, h, own(0, h, t)),
            z | own(0, h, own(2, x, z)),
            x | own(2, h, t),
            own(2, h, own(0, y, own(2, z, own(0, x, y)))))


def load_problem(name):
    assert name in ("pairwise", "threewise")
    if name == "threewise":
        # Independent tags normalize formal unions in all 64 status cells.
        # Equality is preserved by interpreting each passive tag as any
        # nonempty set other than the three distinguished atoms.
        for status in itertools.product(range(4), repeat=3):
            symbolic = tuple(1 << s if s < 3 else 1 << (3 + i)
                             for i, s in enumerate(status))
            assert max(Counter(four_patches(symbolic)).values()) >= 3
    values, agreements = [], set()
    for x, y, z in itertools.product(range(1, 8), repeat=3):
        if name == "pairwise":
            h = own(1, x, z)
            p = y | h
            q = own(0, h, own(2, y, z))
            r = own(2, own(0, x, y), h)
            assert len({p, q, r}) <= 2
            values.append(p if p == q else r)
        else:
            candidates = four_patches((x, y, z))
            common, count = Counter(candidates).most_common(1)[0]
            assert count >= 3
            assert common == (candidates[0] if candidates[0] == candidates[1]
                              else candidates[2])
            values.append(common)
            agreements.add(sum(1 << i for i, value in enumerate(candidates)
                               if value == common))
    if name == "threewise":
        assert all(a & b & c for a, b, c in itertools.product(agreements, repeat=3))
    return {"roles": 3, "arity": 3, "persistence": name == "threewise",
            "rows": [[5, 2, 1], [3, 1, 6], [1, 2, 4], [2, 4, 1]] if name == "threewise"
                    else [[3, 2, 2], [2, 6, 3], [1, 2, 4]],
            "table": [values[i:i + 7] for i in range(0, len(values), 7)]}


def check(filename):
    data = load_problem(filename)
    assert (data["roles"], data["arity"]) == (3, 3)
    domain = range(1, 8)
    valuations = list(itertools.product(domain, repeat=3))
    table = tuple(x for row in data["table"] for x in row)
    assert len(table) == 343 and all(x in domain for x in table)
    function = dict(zip(valuations, table))

    # Sourcewise reconstruction is necessary, but does not characterize the
    # clone image: both independently excluded operations satisfy it.
    for valuation in valuations:
        for k in range(3):
            bit = 1 << k
            supplied = False
            for j in range(3):
                if not valuation[j] & bit:
                    continue
                probe = tuple(bit if i == j else
                              value if value in (1, 2, 4) and value != bit else 7 ^ bit
                              for i, value in enumerate(valuation))
                supplied |= bool(function[probe] & bit)
            assert bool(function[valuation] & bit) == supplied

    rows = data["rows"]
    assert rows and all(len(row) == 3 for row in rows)
    output = tuple(function[tuple(row)] for row in rows)
    columns = [tuple(row[j] for row in rows) for j in range(3)]
    if data["persistence"]:
        # These four values violate Core.four_valuation_persistence, whose
        # symbolic Lean proof replaces the finite relation certificate.
        assert output == (7, 3, 6, 3)
        assert output[0] & 4 and not output[1] & 4 and not output[2] & 1 and not output[3] & 4
        expected_maximum = (3, 3, 6, 3)
    else:
        assert rows == [[3, 2, 2], [2, 6, 3], [1, 2, 4]]
        assert output == (2, 6, 5)
        expected_maximum = (2, 2, 5)
    assert cut_maxima(columns, output) == expected_maximum

    persistence = True
    for a, b, c in itertools.permutations((1, 2, 4)):
        for tags in itertools.product(range(3), repeat=3):
            first = tuple((a | b, b, b)[j] for j in tags)
            second = tuple((b, b | c, a | b)[j] for j in tags)
            third = tuple((a, b, c)[j] for j in tags)
            if function[first] == b and function[second] == b | c:
                persistence &= bool(function[third] & b)
    assert persistence == data["persistence"]
    if persistence:
        # Three-point interpolation already implies this preservation.
        # Keep an independent direct regression of the first law's relation.
        generated = {(3, 2, 1), (2, 6, 2), (2, 3, 4)}
        while True:
            expanded = generated | {
                tuple(own(r, a, b) for a, b in zip(left, right))
                for r in range(3) for left in generated for right in generated}
            if expanded == generated:
                break
            generated = expanded
        assert len(generated) == 34
        for order in itertools.permutations(range(3)):
            relation = {tuple(sum(((x >> i) & 1) << order[i] for i in range(3))
                              for x in row) for row in generated}
            assert all(tuple(function[tuple(col[i] for col in columns)] for i in range(3))
                       in relation for columns in itertools.product(relation, repeat=3))

    assert all(function[(x, x, x)] == x for x in domain)
    assert all(not out & ~reduce(int.__or__, v) for v, out in function.items())
    assert all(any(x & ~y for x, y in zip(v, w)) or not function[v] & ~function[w]
               for v in valuations for w in valuations)
    ambiguous = (3, 5, 6, 7)
    assert all(function[v] == reduce(int.__or__, v)
               for v in itertools.product(ambiguous, repeat=3))

    # Check the actual all-arity singleton-profile conditions, not merely
    # their restrictions to pure atomic valuations.
    profiles = [[function[tuple(1 << r if coalition & (1 << j) else 7
                                for j in range(3))] == 1 << r
                 for coalition in range(8)] for r in range(3)]
    for r in range(3):
        assert profiles[r][7]
        assert all(not profiles[r][a] or profiles[r][b]
                   for a in range(8) for b in range(8) if not a & ~b)
        assert all((out == 1 << r) == profiles[r][sum(1 << j for j, x in enumerate(v)
                                                    if x == 1 << r)]
                   for v, out in function.items())
    assert all(a & b & c or not (profiles[0][a] and profiles[1][b] and profiles[2][c])
               for a, b, c in itertools.product(range(8), repeat=3))

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
    print(f"{filename}: nonterm obstruction verified; persistence={persistence}.")
    if data["persistence"]:
        print("Verified four core patches and all 64 formal status cells for uniform coherence.")
        print("Any three valuations have a common patch; four-valuation persistence fails.")
    print("Verified idempotence, monotonicity, profiles, support, cell provenance,")
    print("common source and all 131^3 polynomial substitutions with identity reflection.")


def check_full_unary():
    """Optional exhaustive substitution check; requires a C++20 compiler."""
    root = Path(__file__).resolve().parent
    data = "2\n" + "\n".join(
        " ".join(map(str, sum(load_problem(name)["table"], [])))
        for name in ("pairwise", "threewise")) + "\n"
    with tempfile.TemporaryDirectory(prefix="kfol-full-unary-") as temporary:
        binary = Path(temporary) / "full-unary"
        subprocess.run(["g++", "-O3", "-std=c++20", str(root / "full_unary.cpp"),
                        "-o", str(binary)], check=True)
        subprocess.run([str(binary)], input=data, text=True, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-unary", action="store_true",
                        help="also exhaust binary invariants and all 751^3 unary substitutions")
    args = parser.parse_args()
    check("pairwise")
    check("threewise")
    if args.full_unary:
        check_full_unary()
