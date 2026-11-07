#!/usr/bin/env python3
"""Audit the exact rigid-upper-clone criterion on stored and native models.

The written theorem is uniform. Here old-table R/P/C conditions are compared
with an independent new-table Gamma audit. ACI, Birkhoff and ordered M are
checked even on clones that fail Gamma. Exhaustion uses exact attainable
arm sums, covering all parameter tuples without an arity cutoff.
"""

from collections import Counter
from itertools import permutations, product
import json

from check_core_owned_reset import test_models


def clone(tables, e):
    n = len(tables[0])
    result = []
    for h in tables:
        row = [n if h[e][c] == e else h[e][c] for c in range(n)] + [n]
        result.append([old[:] + [row[c]] for c, old in enumerate(h)] + [row])
    return result


def conditions(add, choices, e):
    n = len(add)
    ideal = [x for x in range(n) if add[e][x] == e]
    reflection = all(
        add[e][f[e][x]] != e or x in ideal
        for f in choices for x in range(n)
    )
    prime = all(
        add[f[e][x]][f[e][y]] != e or e in (f[e][x], f[e][y])
        for f in choices for x, y in product(ideal, repeat=2)
    )
    cover = all(
        sum(f[e][x] != e for f in choices) <= 1 for x in ideal
    )
    unused = any(all(f[e][x] == e for x in ideal) for f in choices)
    return reflection and prime and cover, unused


def exhaustion(add, choices):
    """All attainable joins of one arm per owner, for every source."""
    entries = 0
    for a in range(len(add)):
        sums = set(choices[0][a])
        for f in choices[1:]:
            sums = {add[x][y] for x in sums for y in f[a]}
        entries += len(sums)
        if any(add[a][value] != value for value in sums):
            return False, entries
    return True, entries


def independent_gamma(tables, triples, counts):
    """ACI and Birkhoff are audited separately, so only two laws remain."""
    add, *choices = tables
    u = len(add) - 1
    for f in choices:
        for x, y, z in triples:
            counts["distribution_entries"] += 1
            if f[x][add[y][z]] != add[f[x][y]][f[x][z]]:
                return False
    for f, g in permutations(choices, 2):
        for x in range(len(add)):
            counts["coverage_entries"] += 1
            if add[f[u][x]][g[u][x]] != add[u][x]:
                return False
    return True


def check():
    counts = Counter()
    for add, choices in test_models():
        counts["models"] += 1
        n, old, carrier = len(add), range(len(add)), range(len(add) + 1)
        u = n
        triples = (
            [(u, y, z) for y, z in product(carrier, repeat=2)]
            + [(x, u, z) for x in old for z in carrier]
            + [(x, y, u) for x, y in product(old, repeat=2)]
        )
        assert len(triples) == (n + 1) ** 3 - n ** 3
        old_E, entries = exhaustion(add, choices)
        counts["old_exhaustion_sums"] += entries
        for e in old:
            tables = clone([add, *choices], e)
            counts["clones"] += 1
            for h in tables:
                for x in carrier:
                    assert h[x][x] == x and h[x][u] == h[u][x]
                for x, y, z in triples:
                    assert h[h[x][y]][z] == h[x][h[y][z]]
                    counts["associativity_entries"] += 1
            for f, g in permutations(tables[1:], 2):
                for x in carrier:
                    assert f[u][g[u][x]] == g[u][f[u][x]]
                    assert f[x][g[x][u]] == g[x][f[x][u]]
                    counts["Birkhoff_entries"] += 2
                for x, y, z in triples:
                    yz = f[y][z]
                    assert f[x][g[y][yz]] == f[x][g[y][f[x][yz]]]
                    counts["mixed_absorption_entries"] += 1
            expected, unused = conditions(add, choices, e)
            actual = independent_gamma(tables, triples, counts)
            assert actual == expected
            if actual:
                counts["Gamma_clones"] += 1
                if old_E:
                    actual_E, entries = exhaustion(tables[0], tables[1:])
                    assert actual_E == unused
                    counts["exhaustion_comparisons"] += 1
                    counts["clone_exhaustion_sums"] += entries
    print("PASS", json.dumps(dict(counts), sort_keys=True))


if __name__ == "__main__":
    check()
