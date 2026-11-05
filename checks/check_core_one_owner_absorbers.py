"""Check the one-owner multiplier normal forms and absorber constructions.

Run from the repository root.  No solver, search certificate, or /tmp module is
loaded.  The sole repository helper is the published unitization table.
"""
from itertools import product
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path.cwd() / 'checks'))
from core_two_owner_unitization import unitize


def hom(source, target, mapping):
    assert len(mapping) == len(source[0])
    entries = 0
    for op, image in zip(source, target):
        for x, y in product(range(len(mapping)), repeat=2):
            assert mapping[op[x][y]] == image[mapping[x]][mapping[y]]
            entries += 1
    return entries


def iso(source, target, mapping):
    assert len(source[0]) == len(target[0]) == len(set(mapping))
    return hom(source, target, mapping)


def opposite(join, meet, F):
    """Adjoin a g-absorber with f(a,d)=F(d); tables are +,f,g."""
    n = len(join)
    image = sorted(set(F))
    endpoint = n
    barred = {e: n + 1 + i for i, e in enumerate(image)}
    elements = [('old', d) for d in range(n)] + [('new', None)]
    elements += [('bar', e) for e in image]
    index = {t: i for i, t in enumerate(elements)}

    def operation(h, left, right):
        tag, d = left
        kind, e = right
        if tag == 'old' and kind == 'old':
            return ('old', (meet if h == 1 else join)[d][e])
        if tag == 'old':
            return operation(h, right, left)
        if tag == 'new':
            if kind == 'new':
                return ('new', None)
            if h == 2:
                return ('new', None)
            if kind == 'bar':
                return ('bar', e)
            return ('bar', F[e]) if h == 0 else ('old', F[e])
        if kind == 'new':
            return operation(h, right, left)
        if kind == 'bar':
            return ('bar', join[d][e])
        if h != 1:
            return ('bar', join[d][F[e]])
        return ('old', join[F[e]][meet[F[e]][d]])

    tables = [[[index[operation(h, x, y)] for y in elements]
               for x in elements] for h in range(3)]
    return tables, endpoint, barred


def both(join, meet, F, G):
    """Literal formal two-absorber tag construction; no laws presumed."""
    n = len(join)
    Fi, Gi = sorted(set(F)), sorted(set(G))
    Hi = sorted({F[G[x]] for x in range(n)})
    tags = [(0, x) for x in range(n)]
    tags += [(1, x) for x in Gi] + [(2, x) for x in Fi]
    tags += [(3, x) for x in Hi] + [(1, None), (2, None), (3, None)]
    index = {t: i for i, t in enumerate(tags)}

    def normalize(k, d):
        if d is not None:
            if k & 1:
                d = G[d]
            if k & 2:
                d = F[d]
        return k, d

    def collect(parts):
        k, value = 0, None
        for l, d in parts:
            k |= l
            if d is not None:
                value = d if value is None else join[value][d]
        return normalize(k, value)

    def constants(h, k, l):
        if k == l:
            return k
        if h == 1:
            return 1 if 1 in (k, l) else 3
        return 2 if 2 in (k, l) else 3

    def mixed(h, k, d):
        if h == 1:
            if k == 1:
                return 1, None
            return (0, F[d]) if k == 2 else (1, F[G[d]])
        if k == 2:
            return 2, None
        return (0, G[d]) if k == 1 else (2, F[G[d]])

    def operation(h, left, right):
        if h == 0:
            return collect([left, right])
        k, d = left
        l, e = right
        parts = []
        if k and l:
            parts.append((constants(h, k, l), None))
        if k and e is not None:
            parts.append(mixed(h, k, e))
        if l and d is not None:
            parts.append(mixed(h, l, d))
        if d is not None and e is not None:
            parts.append((0, (meet if h == 1 else join)[d][e]))
        return collect(parts)

    tables = [[[index[operation(h, t, u)] for u in tags]
               for t in tags] for h in range(3)]
    return tables, tags, index


def marked_forms(arity):
    monomials = [(s, mark) for s in range(1, 1 << arity) for mark in (0, 1)]

    def close(family):
        family = set(family)
        while True:
            extended = family | {(s, 0) for s, e in family}
            extended |= {(s | t, e | d) for s, e in family for t, d in family}
            if extended == family:
                return frozenset(family)
            family = extended

    forms = sorted({close(monomials[i] for i in range(len(monomials))
                          if mask >> i & 1)
                    for mask in range(1, 1 << len(monomials))},
                   key=lambda family: tuple(sorted(family)))
    index = {p: i for i, p in enumerate(forms)}
    join = [[index[close(p | q)] for q in forms] for p in forms]
    meet = [[index[close((s | t, e | d) for s, e in p for t, d in q)]
             for q in forms] for p in forms]
    F = [index[close((s, 1) for s, e in p)] for p in forms]
    return forms, join, meet, F


def expanded_laws(join, meet, F, G):
    n = len(join)
    for op in (join, meet):
        for x in range(n):
            assert op[x][x] == x
        for x, y in product(range(n), repeat=2):
            assert op[x][y] == op[y][x]
        for x, y, z in product(range(n), repeat=3):
            assert op[x][op[y][z]] == op[op[x][y]][z]
    for x, y, z in product(range(n), repeat=3):
        assert meet[x][join[y][z]] == join[meet[x][y]][meet[x][z]]
    for x in range(n):
        assert F[F[x]] == F[x] and G[G[x]] == G[x]
        assert F[G[x]] == G[F[x]]
        assert join[x][F[x]] == F[x] and join[x][G[x]] == G[x]
    for x, y in product(range(n), repeat=2):
        assert F[join[x][y]] == join[F[x]][F[y]]
        assert G[join[x][y]] == join[G[x]][y]
        assert F[meet[x][y]] == meet[F[x]][y]
        assert G[meet[x][y]] == meet[G[x]][y]


def evaluate_family(family, values, join, meet, F):
    results = []
    for support, mark in family:
        members = [values[i] for i in range(len(values)) if support >> i & 1]
        value = members[0]
        for x in members[1:]:
            value = meet[value][x]
        results.append(F[value] if mark else value)
    value = results[0]
    for x in results[1:]:
        value = join[value][x]
    return value


def pair_expansion(join, meet):
    """The explicit free multiplier pairs, independently of marked DNF."""
    n = len(join)
    zero = n
    add = [row + [x] for x, row in enumerate(join)] + [list(range(n + 1))]
    mul = [row + [zero] for row in meet] + [[zero] * (n + 1)]
    pairs = [(c, d) for c in range(n) for d in range(n + 1)
             if add[c][d] == c and mul[c][d] == d]
    index = {p: i for i, p in enumerate(pairs)}
    plus = [[index[add[c][e], mul[add[c][e]][add[d][k]]]
             for e, k in pairs] for c, d in pairs]
    times = [[index[mul[c][e], add[mul[c][k]][mul[d][e]]]
              for e, k in pairs] for c, d in pairs]
    F = [index[c, c] for c, d in pairs]
    return plus, times, F, pairs


def main():
    j3 = [[max(x, y) for y in range(3)] for x in range(3)]
    f3 = [[0 if 0 in (x, y) else max(x, y) for y in range(3)] for x in range(3)]
    j2 = [[max(x, y) for y in range(2)] for x in range(2)]
    f2 = [[min(x, y) for y in range(2)] for x in range(2)]
    models = [(j3, f3, [0, 1, 2], [0, 1, 2]),
              (j3, f3, [0, 2, 2], [0, 1, 2]),
              (j2, j2, [0, 1], [1, 1])]
    for model in models:
        expanded_laws(*model)

    # The six-state opposite extension embeds in 3_m x U_f({beta,p}).
    six, endpoint, barred = opposite(j3, f3, [0, 2, 2])
    unit_lattice = unitize([j2, f2, j2], unit_owner=0)
    first = [0, 1, 2, 2, 2, 2]
    second = [0, 1, 1, 4, 2, 3]
    six_entries = hom(six, [j3, f3, j3], first)
    six_entries += hom(six, unit_lattice, second)
    assert len(set(zip(first, second))) == 6

    # The four-state active extension over SL2 embeds in native D2 x SL2.
    opposite_four, ep4, bars4 = opposite(j2, j2, [1, 1])
    active_four = [opposite_four[0], opposite_four[2], opposite_four[1]]
    native_join = [[x if x == y else max(2, x, y) for y in range(4)] for x in range(4)]
    native_f = [[0 if 0 in (x, y) else native_join[x][y] for y in range(4)] for x in range(4)]
    native_g = [[1 if 1 in (x, y) else native_join[x][y] for y in range(4)] for x in range(4)]
    obs1, obs2 = [1, 1, 0, 2], [0, 1, 1, 1]
    four_entries = hom(active_four, [native_join, native_f, native_g], obs1)
    four_entries += hom(active_four, [j2, j2, j2], obs2)
    assert len(set(zip(obs1, obs2))) == 4

    # Formal double extensions are exactly the claimed unitizations.
    extensions, tags_list, unit_sizes = [], [], []
    unit_entries = 0
    for case, (join, meet, F, G) in enumerate(models):
        target, tags, index = both(join, meet, F, G)
        extensions.append(target)
        tags_list.append(tags)
        if case < 2:
            inner, endpoint, bars = opposite(join, meet, F)
            outer = unitize(inner, unit_owner=1)
            n = len(inner[0])
            inverse_bar = {v: e for e, v in bars.items()}
            def inside(v):
                if v < len(join): return 0, v
                if v == endpoint: return 2, None
                return 2, inverse_bar[v]
            mapping = []
            for v in range(len(outer[0])):
                if v == 2 * n: t = (1, None)
                elif v < n: t = inside(v)
                else:
                    k, d = inside(v - n)
                    t = (1, d) if k == 0 else ((3, None) if d is None else (3, d))
                mapping.append(index[t])
        else:
            inner, endpoint, bars = opposite(join, meet, G)
            inner = [inner[0], inner[2], inner[1]]
            outer = unitize(inner, unit_owner=0)
            n = len(inner[0])
            inverse_bar = {v: e for e, v in bars.items()}
            def inside(v):
                if v < len(join): return 0, v
                if v == endpoint: return 1, None
                return 1, inverse_bar[v]
            mapping = []
            for v in range(len(outer[0])):
                if v == 2 * n: t = (2, None)
                elif v < n: t = inside(v)
                else:
                    k, d = inside(v - n)
                    t = (2, d) if k == 0 else ((3, None) if d is None else (3, d))
                mapping.append(index[t])
        unit_entries += iso(outer, target, mapping)
        unit_sizes.append(len(target[0]))
    assert unit_sizes == [15, 13, 9]

    # Exact two-variable marked-DNF and outer-G normal forms.
    forms, pj, pf, pF = marked_forms(2)
    assert len(forms) == 17
    states = [(p, e) for p in range(17) for e in (0, 1)]
    state_index = {v: i for i, v in enumerate(states)}
    join = [[state_index[pj[p][q], e | d] for q, d in states] for p, e in states]
    meet = [[state_index[pf[p][q], e | d] for q, d in states] for p, e in states]
    F = [state_index[pF[p], e] for p, e in states]
    G = [state_index[p, 1] for p, e in states]
    expanded_laws(join, meet, F, G)
    one_owner = [i for i, p in enumerate(forms) if all(mark == 0 for _, mark in p)]
    assert len(one_owner) == 6
    pair_forms = set(one_owner) | {pF[i] for i in one_owner}
    pair_forms |= {pj[c][pF[d]] for c in one_owner for d in one_owner}
    assert len(pair_forms) == 17

    # Compare the pair formulas with the independently built marked-DNF
    # algebra, including every operation entry and the multiplier.
    coefficient_index = {p: i for i, p in enumerate(one_owner)}
    cj = [[coefficient_index[pj[p][q]] for q in one_owner] for p in one_owner]
    cf = [[coefficient_index[pf[p][q]] for q in one_owner] for p in one_owner]
    qj, qf, qF, pairs = pair_expansion(cj, cf)
    pair_map = [one_owner[c] if d == 6 else pj[one_owner[c]][pF[one_owner[d]]]
                for c, d in pairs]
    pair_entries = iso([qj, qf], [pj, pf], pair_map)
    assert all(pair_map[qF[x]] == pF[pair_map[x]] for x in range(len(pairs)))
    assert len(pairs) == 17
    assert sum(d != 6 for c, d in pairs) == 11

    # Sharpness uses actual chain coefficient tables, not a numerical bound
    # imposed on the construction. Include an all-join case and the small
    # dissemilattice that has no separating maps into the single 3_m.
    chain_pair_counts = []
    for m in range(1, 6):
        chain_join = [[max(x, y) for y in range(m)] for x in range(m)]
        chain_meet = [[min(x, y) for y in range(m)] for x in range(m)]
        rj, rf, rF, rp = pair_expansion(chain_join, chain_meet)
        expanded_laws(rj, rf, rF, list(range(len(rp))))
        assert len(rp) == m + m * (m + 1) // 2
        chain_pair_counts.append(len(rp))
    for cj, cf in [(j3, j3), (j3, [[0, 0, 2], [0, 1, 2], [2, 2, 2]])]:
        rj, rf, rF, rp = pair_expansion(cj, cf)
        expanded_laws(rj, rf, rF, list(range(len(rp))))

    seventy_two, tags, index = both(join, meet, F, G)
    assert len(seventy_two[0]) == 72
    evaluations, lifted = [], []
    lift_entries = 0
    for case, model in enumerate(models):
        mj, mf, mF, mG = model
        target_tags = {t: i for i, t in enumerate(tags_list[case])}
        for values in product(range(len(mj)), repeat=2):
            mapping = []
            for p, outer in states:
                value = evaluate_family(forms[p], values, mj, mf, mF)
                mapping.append(mG[value] if outer else value)
            for x, y in product(range(34), repeat=2):
                assert mapping[join[x][y]] == mj[mapping[x]][mapping[y]]
                assert mapping[meet[x][y]] == mf[mapping[x]][mapping[y]]
            for x in range(34):
                assert mapping[F[x]] == mF[mapping[x]]
                assert mapping[G[x]] == mG[mapping[x]]
            evaluations.append(mapping)
            tag_map = [target_tags[k, None if d is None else mapping[d]] for k, d in tags]
            lift_entries += hom(seventy_two, extensions[case], tag_map)
            lifted.append(tag_map)
    assert len({tuple(m[x] for m in evaluations) for x in range(34)}) == 34
    assert len({tuple(m[x] for m in lifted) for x in range(72)}) == 72
    pindex = {p: i for i, p in enumerate(forms)}
    x = index[0, state_index[pindex[frozenset({(1, 0)})], 0]]
    y = index[0, state_index[pindex[frozenset({(2, 0)})], 0]]
    a, b = index[1, None], index[2, None]
    reached = {x, y, a, b}
    while True:
        new = reached | {op[u][v] for op in seventy_two for u, v in product(reached, repeat=2)}
        if new == reached: break
        reached = new
    assert len(reached) == 72
    assert all(seventy_two[1][a][v] == a and seventy_two[2][b][v] == b for v in range(72))
    print(json.dumps({'finite_expanded_generators': [3, 3, 2],
                      'six_state_embedding_entries': six_entries,
                      'four_state_embedding_entries': four_entries,
                      'unitization_sizes': unit_sizes,
                      'unitization_isomorphism_entries': unit_entries,
                      'one_owner_binary_coefficients': 6,
                      'marked_DNF_forms': 17,
                      'pair_DNF_isomorphism_entries': pair_entries,
                      'sharp_chain_pair_sizes': chain_pair_counts,
                      'outer_G_forms': 34,
                      'image_sizes_F_G_FG': [len(set(F)), len(set(G)), len({F[G[v]] for v in range(34)})],
                      'universal_binary_one_owner_extension': 72,
                      'separating_expanded_observers': len(evaluations),
                      'lifted_embedding_entries': lift_entries}, indent=2))


if __name__ == '__main__':
    main()
