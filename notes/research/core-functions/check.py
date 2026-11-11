#!/usr/bin/env python3
"""Independently verify two ternary obstructions; no solver is required.

This exploratory certificate is separate from the production Lean artifact.
Run: python3 notes/research/core-functions/check.py
"""

import argparse
import itertools
import subprocess
import tempfile
import json
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


def evaluate_patches(data, valuation):
    evaluated = []
    for node in data["nodes"]:
        if node[0] == "var":
            value = valuation[node[1]]
        elif node[0] == "choice":
            value = own(node[1], evaluated[node[2]], evaluated[node[3]])
        else:
            value = evaluated[node[1]] | evaluated[node[2]]
        evaluated.append(value)
    return [evaluated[root] for root in data["patches"]]


def load_problem(name):
    if name != "pairwise":
        data = json.loads(Path(__file__).with_name(name).read_text())
        assert (data["roles"], data["arity"]) == (3, 3)
        nodes, patches = data["nodes"], data["patches"]
        assert len(patches) == 4 and len(set(patches)) == 4
        assert all(0 <= root < len(nodes) for root in patches)
        for i, node in enumerate(nodes):
            if node[0] == "var":
                assert len(node) == 2 and 0 <= node[1] < 3
            elif node[0] == "choice":
                assert len(node) == 4 and 0 <= node[1] < 3
                assert all(0 <= child < i for child in node[2:])
            else:
                assert node[0] == "union" and len(node) == 3
                assert all(0 <= child < i for child in node[1:])
        # Normalize the terms as formal unions on each status cell. Bits
        # 0..2 are a,b,c; each passive input has its own independent tag.
        # Such an input may be any nonempty set other than these three atoms.
        # No union containing a passive input can become one of these atoms,
        # so this normalization commutes with arbitrary interpretations of
        # the tags. Formal equality therefore proves universal equality.
        for status in itertools.product(range(4), repeat=3):
            symbolic = tuple(1 << s if s < 3 else 1 << (3 + i)
                             for i, s in enumerate(status))
            assert max(Counter(evaluate_patches(data, symbolic)).values()) >= 3
        values, agreements = [], set()
        for valuation in itertools.product(range(1, 8), repeat=3):
            candidates = evaluate_patches(data, valuation)
            common, count = Counter(candidates).most_common(1)[0]
            assert count >= 3
            # This expression selects the common value without enumerating
            # the carrier; three of the four candidates agree.
            assert common == (candidates[0] if candidates[0] == candidates[1]
                              else candidates[2])
            values.append(common)
            agreements.add(sum(1 << i for i, value in enumerate(candidates)
                               if value == common))
        # Any three evaluations have one common candidate term. Checking
        # their agreement masks suffices, including repeated evaluations.
        assert all(a & b & c for a, b, c in itertools.product(agreements, repeat=3))
        data["table"] = [values[i:i + 7] for i in range(0, len(values), 7)]
        return data
    values = []
    for x, y, z in itertools.product(range(1, 8), repeat=3):
        h = own(1, x, z)
        p = y | h
        q = own(0, h, own(2, y, z))
        r = own(2, own(0, x, y), h)
        assert len({p, q, r}) <= 2
        values.append(p if p == q else r)
    return {"roles": 3, "arity": 3, "persistence": False,
            "rows": [[3, 2, 2], [2, 6, 3], [1, 2, 4]],
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
    if "relation" in data:
        # Closure, rather than exhaustiveness, suffices for the obstruction.
        relation = {tuple(row) for row in data["relation"]}
        assert len(relation) == len(data["relation"]) == 148
        assert all(len(row) == len(rows) and all(value in domain for value in row)
                   for row in relation)
        assert all(tuple(row[j] for row in rows) in relation for j in range(3))
        assert all(tuple(own(r, a, b) for a, b in zip(left, right)) in relation
                   for r in range(3) for left in relation for right in relation)
        # At any additional owner the embedded relation's values cannot
        # absorb, so its operation is union. This also checks that closure.
        assert all(tuple(a | b for a, b in zip(left, right)) in relation
                   for left in relation for right in relation)
        assert output == tuple(data["target"]) and output not in relation
        bounded = [v for v in relation if all(not a & ~b for a, b in zip(v, output))]
        expected_maximum = tuple(data["bounded_maximum"])
        assert expected_maximum == tuple(reduce(int.__or__, (v[i] for v in bounded), 0)
                                         for i in range(len(rows)))
    else:
        # These entries contradict Core.three_valuation_persistence in Lean.
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
    if "patches" in data:
        print("Verified four core patches and all 64 formal status cells for uniform coherence.")
        print("Any three valuations have a common patch; the obstruction is union-closed.")
    print("Verified idempotence, monotonicity, profiles, support, cell provenance,")
    print("common source and all 131^3 polynomial substitutions with identity reflection.")


def check_full_unary():
    """Optional exhaustive substitution check; requires a C++20 compiler."""
    root = Path(__file__).resolve().parent
    data = "2\n" + "\n".join(
        " ".join(map(str, sum(load_problem(name)["table"], [])))
        for name in ("pairwise", "threewise.json")) + "\n"
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
    check("threewise.json")
    if args.full_unary:
        check_full_unary()
