import itertools, random
from fm import coal_masks, choice, closure, is_monotone, is_selfdual

maj = lambda a,b,c: (a&b)|(b&c)|(a&c)

# (b) median distributive law  m(m(a,b,c),d,e) = m(a, m(b,d,e), m(c,d,e))  on {0,1}
ok = all(maj(maj(a,b,c),d,e) == maj(a, maj(b,d,e), maj(c,d,e)) for a,b,c,d,e in itertools.product((0,1),repeat=5))
print("(b) median distributive law holds on {0,1}:", ok)

# (a) value theorem: random game trees, brute-force coalition forcing vs compositional median value
def rand_tree(K, depth, branch=3, onehot=True):
    if depth == 0 or random.random() < 0.2:
        if onehot: return ('leaf', frozenset([random.randrange(K)]))
        return ('leaf', frozenset(j for j in range(K) if random.random() < 0.5))
    i = random.randrange(K)
    return ('node', i, [rand_tree(K, depth-1, branch, onehot) for _ in range(random.randint(1, branch))])

def forces(t, C):  # can coalition C force "some member of C wins" (perfect info, minimax)
    if t[0] == 'leaf': return bool(t[1] & C)
    _, i, ch = t
    vals = [forces(c, C) for c in ch]
    return any(vals) if i in C else all(vals)

def value(t, K):
    N, full, xs = coal_masks(K)
    if t[0] == 'leaf':
        m = 0
        for j in t[1]: m |= xs[j]
        return m
    _, i, ch = t
    v = value(ch[0], K)
    for c in ch[1:]:
        v = choice(xs[i], v, value(c, K), full)
    return v

random.seed(1)
bad = 0
for K in (2,3,4,5):
    for onehot in (True, False):
        for _ in range(400):
            t = rand_tree(K, 6, 3, onehot)
            v = value(t, K)
            for Cm in range(1 << K):
                C = frozenset(j for j in range(K) if Cm >> j & 1)
                if forces(t, C) != bool(v >> Cm & 1): bad += 1
print("(a) value theorem mismatches over random trees (K=2..5, one-hot & general):", bad)

# (c) S_K-equivariant n-ary operations on outcomes K^n -> K
def count_equivariant(K, n):
    perms = list(itertools.permutations(range(K)))
    # orbit representatives: brute force over all functions is too big; instead build via orbits
    pts = list(itertools.product(range(K), repeat=n))
    idx = {p:i for i,p in enumerate(pts)}
    seen = [False]*len(pts); orbits = []
    for p in pts:
        if seen[idx[p]]: continue
        orb = set(tuple(pi[x] for x in p) for pi in perms)
        for q in orb: seen[idx[q]] = True
        orbits.append(p)
    # value at representative p must be fixed by stabilizer of p; equivariance then determines orbit
    total = 1
    for p in orbits:
        stab = [pi for pi in perms if tuple(pi[x] for x in p) == p]
        fixed = [v for v in range(K) if all(pi[v] == v for pi in stab)]
        total *= len(fixed)
    return total
for K in range(2, 7):
    print(f"(c) K={K}: #equivariant binary ops K^2->K = {count_equivariant(K,2)},  ternary = {count_equivariant(K,3)}")

# (d) general-sum values: leaves are arbitrary winner sets (OR of x_j over the set, incl. empty set)
for K in (2,3,4):
    N, full, xs = coal_masks(K)
    leaves = []
    for S in range(1 << K):
        m = 0
        for j in range(K):
            if S >> j & 1: m |= xs[j]
        leaves.append(m)
    Sset = closure(leaves, K)
    allmono0 = [f for f in range(1 << N) if is_monotone(f, K) and not (f & 1)]
    print(f"(d) K={K} general-sum: |closure|={len(Sset)}, #monotone f with f(empty)=0: {len(allmono0)}, equal sets: {Sset==set(allmono0)}")
