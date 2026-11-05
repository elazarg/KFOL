#!/usr/bin/env python3
"""Certify all three-owner candidate models with <=4 join generators.

Standard library only. No stored model/certificate input and no solver.
The only external mathematical dependencies are the committed completeness
result through eight elements, the one-owner theorem, and
V(D_3) intersect Mod(E) = V(core). Models with a least join element are
already covered by the principal-filter theorem and are omitted here.

Candidate laws checked: four semilattices; choice-over-join distribution;
all pair coverage/Birkhoff/mixed-absorption laws; all ordered distinct-
three-owner union definitions; and owner exhaustion E.

The support representation enumerates all join orders with exactly four
join-irreducibles. Orders with fewer have <=7 elements. For each order,
distribution determines choices from the six unordered generator products.
Each product is between every common lower bound and the generators' join.
Full generator-row join equations ensure the extension is well defined.

Positive certificates are checked immediately: jointly separating native
homomorphisms, or jointly separating onto quotients of size <=8. The latter
may combine several principal congruences. A failure is reported as UNKNOWN;
this script never interprets failure to find a cover as a countermodel.
"""
from collections import Counter, deque
from functools import reduce
from itertools import combinations, combinations_with_replacement, permutations, product
from time import monotonic


def join_shapes():
    """All no-bottom four-irreducible orders, up to generator relabeling."""
    relabelings = list(permutations(range(4)))
    seen = set()
    for selection in range(1 << 14):
        closed = {0, 15} | {s for s in range(1, 15) if selection >> (s - 1) & 1}
        if any(a & b not in closed for a, b in combinations(closed, 2)):
            continue
        masks = sorted(closed - {0})
        if any(all(a & b == a for b in masks) for a in masks):
            continue
        def closure(s):
            return reduce(int.__and__, (c for c in closed if s & c == s))
        generators = [closure(1 << i) for i in range(4)]
        if len(set(generators)) != 4:
            continue
        irreducibles = []
        for a in masks:
            lower = [b for b in masks if b != a and b & a == b]
            if not lower or closure(reduce(int.__or__, lower)) != a:
                irreducibles.append(a)
        if set(irreducibles) != set(generators):
            continue
        canonical = min(tuple(sorted(sum(1 << p[i] for i in range(4) if s >> i & 1)
                                     for s in closed)) for p in relabelings)
        if canonical in seen:
            continue
        seen.add(canonical)
        index = {s: i for i, s in enumerate(masks)}
        join = [[index[closure(a | b)] for b in masks] for a in masks]
        yield masks, join, [index[g] for g in generators]


def choice_tables(masks, join, generators):
    """Exhaust all bilinear semilattice choices; audit their full tables."""
    n = len(join)
    states = range(n)
    supports = [[i for i in range(4) if s >> i & 1] for s in masks]
    pairs = list(combinations(range(4), 2))
    options = []
    for i, j in pairs:
        a, b = generators[i], generators[j]
        lower = [z for z in states if join[z][a] == a and join[z][b] == b]
        upper = join[a][b]
        options.append([z for z in states if join[z][upper] == upper
                        and all(join[w][z] == z for w in lower)])
    choices, raw = [], 0
    for values in product(*options):
        raw += 1
        atomic = [[generators[i] if i == j else None for j in range(4)]
                  for i in range(4)]
        for (i, j), value in zip(pairs, values):
            atomic[i][j] = atomic[j][i] = value
        rows = [[reduce(lambda a, b: join[a][b], (atomic[i][j] for j in support))
                 for support in supports] for i in range(4)]
        # Comparable generators require this consistency test explicitly.
        if any(rows[i][generators[j]] != atomic[i][j]
               for i, j in product(range(4), repeat=2)):
            continue
        if any(row[join[a][b]] != join[row[a]][row[b]]
               for row in rows for a, b in product(states, repeat=2)):
            continue
        table = [[reduce(lambda a, b: join[a][b], (rows[i][y] for i in support))
                  for y in states] for support in supports]
        if any(table[a][table[b][c]] != table[table[a][b]][c]
               for a, b, c in product(states, repeat=3)):
            continue
        assert all(table[a][a] == a for a in states)
        assert all(table[a][b] == table[b][a] for a, b in product(states, repeat=2))
        assert all(table[a][join[b][c]] == join[table[a][b]][table[a][c]]
                   for a, b, c in product(states, repeat=3))
        choices.append(table)
    assert len({tuple(map(tuple, f)) for f in choices}) == len(choices)
    return choices, supports, raw


def compatible(f, g, join):
    states = range(len(join))
    if any(join[f[a][b]][g[a][b]] != join[a][b]
           or f[a][g[a][b]] != g[a][f[a][b]]
           for a, b in product(states, repeat=2)):
        return False
    return all(m[x][p[y][m[y][z]]] == m[x][p[y][m[x][m[y][z]]]]
               for m, p in ((f, g), (g, f))
               for x, y, z in product(states, repeat=3))


def exhausted(choices, join):
    for c in range(len(join)):
        sums = set(choices[0][c])
        for f in choices[1:]:
            sums = {join[a][b] for a in sums for b in f[c]}
        if any(join[c][a] != a for a in sums):
            return False
    return True


def native_join(a, b):
    return a if a == b else max(3, a, b)


def native_choice(owner, a, b):
    return owner if owner in (a, b) else native_join(a, b)


def native_join_maps(join, supports):
    states = range(len(join))
    for valuation in product(range(5), repeat=4):
        mapping = [reduce(native_join, (valuation[i] for i in s)) for s in supports]
        if all(mapping[join[a][b]] == native_join(mapping[a], mapping[b])
               for a, b in product(states, repeat=2)):
            yield mapping


def congruence(tables, edges):
    n = len(tables[0])
    parents, queue = list(range(n)), deque(edges)
    def root(x):
        while parents[x] != x:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x
    while queue:
        a, b = map(root, queue.popleft())
        if a == b:
            continue
        parents[b] = a
        for table in tables:
            queue.extend((table[a][z], table[b][z]) for z in range(n))
    roots = [root(a) for a in range(n)]
    labels = {x: i for i, x in enumerate(dict.fromkeys(roots))}
    return [labels[x] for x in roots]


def audit_quotient(tables, mapping):
    n = len(mapping)
    size = max(mapping) + 1
    assert set(mapping) == set(range(size)) and size <= 8
    representatives = [mapping.index(i) for i in range(size)]
    for table in tables:
        quotient = [[mapping[table[a][b]] for b in representatives] for a in representatives]
        assert all(mapping[table[a][b]] == quotient[mapping[a]][mapping[b]]
                   for a, b in product(range(n), repeat=2))


def certify(choices, join, generators, join_maps):
    if sum(f != join for f in choices) <= 1:
        return 'one_owner', 0
    n = len(join)
    pairs = list(combinations(range(n), 2))
    residual = set(pairs)
    for mapping in join_maps:
        if any(mapping[f[a][b]] != native_choice(i, mapping[a], mapping[b])
               for i, f in enumerate(choices)
               for a, b in combinations_with_replacement(generators, 2)):
            continue
        # Full-table validation of each actual native map used.
        assert all(mapping[f[a][b]] == native_choice(i, mapping[a], mapping[b])
                   for i, f in enumerate(choices)
                   for a, b in product(range(n), repeat=2))
        residual = {(a, b) for a, b in residual if mapping[a] == mapping[b]}
        if not residual:
            return 'native_embedding', 0
    tables = choices + [join]
    residual = set(pairs)
    for pair in pairs:
        mapping = congruence(tables, [pair])
        if max(mapping) >= 8:
            continue
        audit_quotient(tables, mapping)
        residual = {(a, b) for a, b in residual if mapping[a] == mapping[b]}
        if not residual:
            return 'small_quotients', 0
    completions = 0
    for protected in sorted(residual):
        if protected not in residual:
            continue
        mapping = list(range(n))
        for pair in pairs:
            if mapping[pair[0]] == mapping[pair[1]]:
                continue
            edges = [(a, b) for a, b in pairs if mapping[a] == mapping[b]]
            trial = congruence(tables, edges + [pair])
            if trial[protected[0]] != trial[protected[1]]:
                mapping = trial
        if max(mapping) >= 8:
            continue
        audit_quotient(tables, mapping)
        completions += 1
        residual = {(a, b) for a, b in residual if mapping[a] == mapping[b]}
    return ('small_quotients' if not residual else 'UNKNOWN'), completions


def main():
    start = monotonic()
    total = Counter()
    for masks, join, generators in join_shapes():
        total['shapes'] += 1
        n = len(join)
        if n <= 8:
            total['small_shapes'] += 1
            continue
        total['large_shapes'] += 1
        choices, supports, raw = choice_tables(masks, join, generators)
        total['raw_products'] += raw
        total['choice_tables'] += len(choices)
        adjacency = [set() for _ in choices]
        for i, f in enumerate(choices):
            for j in range(i, len(choices)):
                if compatible(f, choices[j], join):
                    adjacency[i].add(j)
                    adjacency[j].add(i)
        join_maps = list(native_join_maps(join, supports))
        local = Counter()
        for i in range(len(choices)):
            for j in sorted(q for q in adjacency[i] if q >= i):
                for k in sorted(q for q in adjacency[i] & adjacency[j] if q >= j):
                    selected = [choices[q] for q in (i, j, k)]
                    if any(h[f[a][b]][g[a][b]] != join[a][b]
                           for f, g, h in permutations(selected)
                           for a, b in product(range(n), repeat=2)):
                        continue
                    local['ambient'] += 1
                    if not exhausted(selected, join):
                        local['E_failing'] += 1
                        continue
                    local['candidate'] += 1
                    status, completions = certify(selected, join, generators, join_maps)
                    local[status] += 1
                    local['nonprincipal_completions'] += completions
                    if status == 'UNKNOWN':
                        print('UNKNOWN', masks, (i, j, k), flush=True)
        total.update(local)
        print('AUDITED', masks, dict(local), flush=True)
    print('TOTAL', dict(total), 'seconds', round(monotonic() - start, 2), flush=True)
    assert total['shapes'] == 117 and total['small_shapes'] == 70
    assert total['large_shapes'] == 47 and total['choice_tables'] == 2105
    assert total['ambient'] == 10332 and total['candidate'] == 10111
    assert total['native_embedding'] == 2553 and total['one_owner'] == 2105
    assert total['small_quotients'] == 5453 and total['nonprincipal_completions'] == 5
    assert total['UNKNOWN'] == 0
    print('PASS: every three-owner candidate with <=4 join generators is core.')


if __name__ == '__main__':
    main()
