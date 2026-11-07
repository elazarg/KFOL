#!/usr/bin/env python3
"""A reproducible finite countermodel for the strengthened core candidate.

Standard library only. Six native coordinate valuations generate a192-state
core coefficient algebra. Its rigid upper clone has193 states and fails a
native-valid five-variable coverage equation. A final exact quotient has115
states. No solver, native-equality merges, external data, or search artifact.

All old-input law instances hold in the literal native subpower. New-input
instances are exhausted. OC/HOC use the proved retained-input theorem for
a split common-support extension; the reduction is stated in check_overlap.
All Star arities follow from the written rigid-clone support-lifting lemma,
not from an arity cutoff. Unused owners are interpreted as join (K>=4).
"""
from itertools import product, permutations
import json
import time

# At each coordinate: the four ordinary generators a,b,c,d. Native owner
# atoms are0,1,2; the neutral and upper markers are3,4. e is constantly3.
ROWS = ((4,0,1,2), (0,4,2,1), (1,2,4,3),
        (2,1,3,4), (0,2,1,1), (0,1,2,2))


def scalar(h, x, y, k=3):
    if h < k and h in (x, y):
        return h
    return x if x == y else max(k, x, y)


def vector(h, x, y):
    return tuple(scalar(h, a, b) for a, b in zip(x, y))


def coefficient_algebra():
    generators = [(3,) * len(ROWS)]
    generators += [tuple(row[i] for row in ROWS) for i in range(4)]
    states, terms, index = [], [], {}

    def add(value, term):
        if value not in index:
            index[value] = len(states)
            states.append(value)
            terms.append(term)

    for i, value in enumerate(generators):
        add(value, ('generator', i))
    position = 0
    while position < len(states):
        for other in range(position + 1):
            for h in range(4):
                add(vector(h, states[position], states[other]),
                    ('operation', h, position, other))
        position += 1
    assert len(states) == 192
    for i, term in enumerate(terms):
        if term[0] == 'generator':
            assert states[i] == generators[term[1]]
        else:
            _, h, left, right = term
            assert left < i and right < i
            assert states[i] == vector(h, states[left], states[right])
    # Every ordered source product is independently looked up in the carrier.
    tables = [[[index[vector(h, x, y)] for y in states] for x in states]
              for h in range(4)]
    return states, tables


def upper_clone(base):
    n, e = len(base[0]), 0
    result = []
    for h in base:
        result.append([row[:] + [n if h[e][c] == e else h[e][c]]
                       for c, row in enumerate(h)] +
                      [[n if h[e][c] == e else h[e][c]
                        for c in range(n)] + [n]])
    return result


def check_upper_clone_criterion(base):
    """Old-table R/P/C, independent of the new-point law audit below."""
    e, join = 0, base[-1]
    ideal = [x for x in range(len(join)) if join[e][x] == e]
    assert len(ideal) == 10
    counts = dict(reflection=0, primeness=0, coverage=0)
    for f in base:
        for x in range(len(join)):
            assert join[e][f[e][x]] != e or x in ideal
            counts['reflection'] += 1
        for x, y in product(ideal, repeat=2):
            assert join[f[e][x]][f[e][y]] != e or e in (f[e][x], f[e][y])
            counts['primeness'] += 1
    for i in range(len(base)):
        for j in range(i):
            for x in ideal:
                assert e in (base[i][e][x], base[j][e][x])
                counts['coverage'] += 1
    assert all(join[e][x] == e for x in ideal)
    return counts


def check_retraction_and_generation(tables, base):
    n, e = len(base[0]), 0
    q = list(range(n)) + [e]
    entries = 0
    for h, old in zip(tables, base):
        for x, y in product(range(n + 1), repeat=2):
            assert q[h[x][y]] == old[q[x]][q[y]]
            entries += 1
        assert h[e][n] == n
    seen = {n, 1, 2, 3, 4}
    while True:
        values = {h[x][y] for h in tables for x, y in product(seen, repeat=2)}
        if values <= seen:
            break
        seen |= values
    assert seen == set(range(n + 1))
    return entries


def check_new_laws(tables):
    """All Gamma/M instances involving the sole new value.

    Four owners: choices0,1,2 are active, choice3 is join. Designated join
    is the same table. E follows directly because its owner3 arm c+x
    dominates c. More unused owners give no additional nontrivial cases.
    """
    n = len(tables[0])
    u, carrier = n - 1, range(n)
    choices = tables[:3] + [tables[-1]]
    join = tables[-1]
    triples = [(x,y,z) for x,y,z in product(carrier, repeat=3)
               if u in (x,y,z)]
    count = 0
    for h in tables:
        for x in carrier:
            assert h[x][x] == x and h[x][u] == h[u][x]
            count += 2
        for x,y,z in triples:
            assert h[h[x][y]][z] == h[x][h[y][z]]
            count += 1
    for h in choices:
        for x,y,z in triples:
            assert h[x][join[y][z]] == join[h[x][y]][h[x][z]]
            count += 1
    for i,j in permutations(range(4), 2):
        h,k = choices[i], choices[j]
        for x in carrier:
            assert join[h[x][u]][k[x][u]] == join[x][u]
            assert h[x][k[x][u]] == k[x][h[x][u]]
            assert h[u][k[u][x]] == k[u][h[u][x]]
            count += 3
        for x,y,z in triples:
            a = h[y][z]
            assert h[x][k[y][a]] == h[x][k[y][h[x][a]]]
            count += 1
    for i,j,k in permutations(range(4), 3):
        h,l,m = choices[i], choices[j], choices[k]
        for x in carrier:
            assert m[h[x][u]][l[x][u]] == join[x][u]
            count += 1
    return count


def check_overlap(tables, heterogeneous=False):
    """Exact all-valuations reduction, not a restricted-arity sample.

    The checked retraction commonly supports every input. Retained-input
    linearization reduces any failed identity to a valuation with only
    one input outside the old base. If the sole epsilon is padding z/w,
    monotonicity cannot break a true lower bound. Otherwise swap x,y
    (and their paddings/inner owners), so x=epsilon and y is old. Failure
    requires f(epsilon,y)=epsilon and RHS=old e: any old RHS>e dominates
    epsilon. Cases involving an outer join or an inner join are Gamma
    consequences; the uniform routine nevertheless checks join cases.
    """
    old_size = len(tables[0]) - 1
    u, e, join = old_size, 0, tables[-1]
    patterns = (permutations(range(3), 3) if heterogeneous else
                ((i,j,j) for i,j in permutations(range(4), 2)))
    count = 0
    for i,j,k in patterns:
        f,g,h = tables[i], tables[j], tables[k]
        for y in range(old_size):
            if f[u][y] != u:
                continue
            for z in range(old_size):
                left_arm = f[u][g[y][z]]
                if left_arm == u:
                    continue
                for w in range(old_size):
                    right_arm = f[y][h[u][w]]
                    rhs = join[left_arm][right_arm]
                    assert rhs != e
                    assert rhs == u or join[e][rhs] == rhs
                    count += 1
    return count


def coverage_value(tables, values):
    f,g,h,join = tables
    p,a,b,c,d = values
    arms = [f[p][f[a][b]], g[p][g[a][c]], g[p][g[b][d]],
            h[p][h[a][d]], h[p][h[b][c]]]
    rhs = arms[0]
    for value in arms[1:]:
        rhs = join[rhs][value]
    return arms, rhs


def check_native_coverage():
    # The written proof is uniform in K. These are independent finite checks.
    entries = 0
    for k in (3,4,5):
        tables = [[[scalar(h,x,y,k) for y in range(k+2)]
                   for x in range(k+2)] for h in (0,1,2,k)]
        join = tables[-1]
        for values in product(range(k+2), repeat=5):
            _,rhs = coverage_value(tables, values)
            assert join[values[0]][rhs] == rhs
            entries += 1
    edges = ((0,(0,1)), (1,(0,2)), (1,(1,3)),
             (2,(0,3)), (2,(1,2)))
    for colors in product((-1,0,1,2), repeat=4):
        assert not all(any(colors[v] == i for v in edge) for i,edge in edges)
    return entries


def check_atomic_fibers(states, tables):
    atomic = [tuple(min(v,3) for v in s) for s in states]
    atomic.append((3,) * len(ROWS))
    carrier = sorted(set(atomic))
    assert len(carrier) == 59
    entries = common_entries = 0
    for hi,h in enumerate(tables):
        for x,y in product(range(len(atomic)), repeat=2):
            assert atomic[h[x][y]] == vector(hi, atomic[x], atomic[y])
            entries += 1
            if atomic[x] == atomic[y]:
                assert h[x][y] == tables[-1][x][y]
                common_entries += 1
    assert atomic.count(atomic[-1]) == 17
    return entries, common_entries


def separating_quotient(tables):
    """Coarsest congruence refining the zero ideal down(e).

    This is also the largest congruence avoiding e~epsilon: if a<=e and
    b is outside down(e), then epsilon<=e+b; a congruence merging a,b
    merges e with e+b and hence with epsilon. The fixed point below is
    the largest congruence refining that cut, by translation refinement.
    Consequently the115-state quotient is subdirectly irreducible.
    """
    n, e = len(tables[0]), 0
    u, join = n-1, tables[-1]
    colors = [int(join[e][x] != e) for x in range(n)]
    assert colors[e] != colors[u]
    for b in range(n):
        if colors[b]:
            assert join[u][join[e][b]] == join[e][b]
    rounds = 0
    while True:
        signatures = [(colors[x], tuple(colors[h[x][c]]
                       for h in tables for c in range(n))) for x in range(n)]
        ids, refined = {}, []
        for sig in signatures:
            if sig not in ids:
                ids[sig] = len(ids)
            refined.append(ids[sig])
        rounds += 1
        stable = all((colors[x] == colors[y]) == (refined[x] == refined[y])
                     for x,y in product(range(n), repeat=2))
        colors = refined
        if stable:
            break
    size = len(set(colors))
    assert size == 115 and colors[e] != colors[u]
    quotient = [[[None] * size for _ in range(size)] for _ in tables]
    entries = 0
    for i,h in enumerate(tables):
        for x,y in product(range(n), repeat=2):
            a,b,c = colors[x],colors[y],colors[h[x][y]]
            assert quotient[i][a][b] is None or quotient[i][a][b] == c
            quotient[i][a][b] = c
            entries += 1
    values = [colors[x] for x in (u,1,2,3,4)]
    _, rhs = coverage_value(quotient, values)
    assert rhs == colors[e]
    assert quotient[-1][values[0]][rhs] != rhs
    return size, rounds, entries


def main():
    start = time.monotonic()
    states, base = coefficient_algebra()
    criterion = check_upper_clone_criterion(base)
    tables = upper_clone(base)
    retraction = check_retraction_and_generation(tables, base)
    laws = check_new_laws(tables)
    uniform = check_overlap(tables)
    heterogeneous = check_overlap(tables, heterogeneous=True)
    native = check_native_coverage()
    u = len(states)
    arms,rhs = coverage_value(tables, (u,1,2,3,4))
    assert rhs == 0 and all(value != 0 for value in arms)
    assert all(tables[-1][0][value] == 0 for value in arms)
    assert tables[-1][u][rhs] == u != rhs
    atomic, common = check_atomic_fibers(states, tables)
    size, rounds, quotient_entries = separating_quotient(tables)
    print(json.dumps({'status':'PASS', 'seconds':time.monotonic()-start,
        'coefficient_size':len(states), 'clone_size':len(tables[0]),
        'source_product_entries':4*len(states)**2,
        'upper_clone_criterion_entries':criterion,
        'retraction_entries':retraction, 'new_Gamma_M_entries':laws,
        'OC2_critical_entries':uniform, 'mixed_HOC2_critical_entries':heterogeneous,
        'native_coverage_entries':native, 'coverage_arms':arms,
        'source_value':u, 'coverage_rhs':rhs, 'generated_by':5,
        'atomic_quotient_size':59, 'atomic_hom_entries':atomic,
        'common_fiber_entries':common, 'quotient_size':size,
        'quotient_refinement_rounds':rounds,
        'quotient_hom_entries':quotient_entries,
        'scope':'K>=4; unused owners are join. All Star_n and HOC_n follow by the written lifting/grouping proofs, not a finite arity sample.'}, indent=2))


if __name__ == '__main__':
    main()

