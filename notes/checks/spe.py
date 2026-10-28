import itertools, random
# outcomes: frozenset of winners (general-sum) ; one-hot = singletons.
def W(i, S): return frozenset(o for o in S if i in o)
def L(i, S): return frozenset(o for o in S if i not in o)
def chooseS(i, kids):
    U = frozenset().union(*kids)
    res = set(W(i, U))
    if all(L(i, k) for k in kids): res |= L(i, U)
    return frozenset(res)
def spe_comp(t):
    if t[0] == 'leaf': return frozenset([t[1]])
    _, i, ch = t
    return chooseS(i, [spe_comp(c) for c in ch])

# brute force: enumerate pure strategy profiles (a choice at every internal node), keep subgame-perfect ones
def nodes(t, acc):
    if t[0] == 'node':
        acc.append(t)
        for c in t[2]: nodes(c, acc)
    return acc
def play(t, prof):
    while t[0] == 'node': t = t[2][prof[id(t)]]
    return t[1]
def spe_brute(t):
    ns = nodes(t, [])
    outs = set()
    for choice in itertools.product(*[range(len(n[2])) for n in ns]):
        prof = {id(n): c for n, c in zip(ns, choice)}
        ok = True
        for n in ns:  # one-shot deviation principle at every node (finite perfect info)
            i = n[1]
            cur = i in play(n, prof)
            for alt in range(len(n[2])):
                if (i in play(n[2][alt], prof)) and not cur: ok = False; break
            if not ok: break
        if ok: outs.add(play(t, prof))
    return frozenset(outs)

def rand_tree(K, d, onehot):
    if d == 0 or random.random() < 0.25:
        return ('leaf', frozenset([random.randrange(K)]) if onehot else frozenset(j for j in range(K) if random.random() < .5))
    return ('node', random.randrange(K), [rand_tree(K, d-1, onehot) for _ in range(random.randint(1, 3))])

random.seed(7); bad = 0; n = 0
for K in (2, 3, 4):
    for onehot in (True, False):
        for _ in range(300):
            t = rand_tree(K, 4, onehot)
            if len(nodes(t, [])) > 11: continue
            n += 1
            if spe_comp(t) != spe_brute(t): bad += 1
print(f"SPE compositional formula vs brute-force subgame-perfect profiles: {bad} mismatches / {n} trees")

# value sets reachable (one-hot), algebraic laws
for K in (2, 3, 4):
    leaves = [frozenset([frozenset([j])]) for j in range(K)]
    S = set(leaves); fr = set(leaves)
    while fr:
        new = set()
        for i in range(K):
            for a in fr:
                for b in list(S):
                    c = chooseS(i, [a, b])
                    if c not in S: new.add(c)
        S |= new; fr = new
    print(f"K={K} one-hot: #SPE values = {len(S)} (nonempty subsets of K: {2**K-1})")
    Sl = list(S)
    assoc = all(chooseS(i,[a,chooseS(i,[b,c])]) == chooseS(i,[chooseS(i,[a,b]),c]) for i in range(K) for a in Sl for b in Sl for c in Sl)
    dist_fail = [(i,j,a,b,c) for i in range(K) for j in range(K) if i!=j for a in Sl for b in Sl for c in Sl
                 if chooseS(j,[chooseS(i,[a,b]),c]) != chooseS(i,[chooseS(j,[a,c]),chooseS(j,[b,c])])]
    print(f"   (+)_i associative: {assoc};  distributivity (a+_i b)+_j c = (a+_j c)+_i(b+_j c) failures: {len(dist_fail)}")
    if dist_fail:
        i,j,a,b,c = dist_fail[0]
        fmt = lambda s: '{'+','.join(str(min(o)) for o in sorted(s, key=min))+'}'
        print(f"   e.g. i={i}, j={j}, a={fmt(a)}, b={fmt(b)}, c={fmt(c)}: LHS={fmt(chooseS(j,[chooseS(i,[a,b]),c]))} RHS={fmt(chooseS(i,[chooseS(j,[a,c]),chooseS(j,[b,c])]))}")
