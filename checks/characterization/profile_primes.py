"""Prime guards of the greatest-profile candidate with Phi_a = Phi_b = transversals of a hypergraph H,
unanimity elsewhere (K=3, owners a=0,b=1,c=2).  Checks: the prime guards at observer c are the minimal sets
(e\\j)x{a} u (e'\\j)x{b}; at observer a the minimal (e\\j)x{b}; and the candidate has an empty output
exactly when H has two disjoint transversals."""
import itertools, random, sys
def run(n,rng):
    V=range(n)
    edges=[]
    for _ in range(rng.randint(1,4)):
        e=frozenset(rng.sample(range(n),rng.randint(2,min(3,n))))
        if e not in edges: edges.append(e)
    trans=lambda E: all(E & e for e in edges)
    def c(k,j,p):   # p: dict i->status in {'n',0,1,2}\{k}
        for r in range(3):
            if r==k: continue
            E=frozenset(i for i in p if p[i]==r)
            if r in (0,1):
                if trans(E): return 0
            # unanimity for owner 2 never holds without j
        return 1
    for k in range(3):
        others=[r for r in range(3) if r!=k]
        for j in V:
            rest=[i for i in V if i!=j]
            lits=[(i,r) for i in rest for r in others]
            pats=[dict(zip(rest,st)) for st in itertools.product(['n']+others,repeat=len(rest))]
            def suff(G): return all(c(k,j,p) for p in pats if all(p[i]!=r for (i,r) in G))
            primes=set()
            for m in range(len(lits)+1):
                for G in itertools.combinations(lits,m):
                    G=frozenset(G)
                    if any(P<=G for P in primes): continue
                    if suff(G): primes.add(G)
            cand=set()
            if k==2:
                for e in edges:
                    for e2 in edges:
                        cand.add(frozenset({(i,0) for i in e-{j}}|{(i,1) for i in e2-{j}}))
            else:
                o=1-k
                for e in edges: cand.add(frozenset((i,o) for i in e-{j}))
            mins={G for G in cand if not any(H<G for H in cand)}
            assert primes==mins,(edges,k,j,primes,mins)
    # disjoint transversals <=> empty output somewhere (use atoms only)
    subsets=[frozenset(s) for m in range(n+1) for s in itertools.combinations(V,m)]
    disjoint=any(trans(A) and trans(B) and not (A&B) for A in subsets for B in subsets)
    empty=False
    for S in itertools.product(range(3),repeat=n):
        out=set()
        for j in V:
            k=S[j]
            if c(k,j,{i:S[i] for i in V if i!=j}): out.add(k)
        if not out: empty=True
    assert empty==disjoint,(edges,empty,disjoint)
    return disjoint
rng=random.Random(5); res=[run(rng.choice([3,4]),rng) for _ in range(150)]
print('instances',len(res),'two-colorable',sum(res),'all prime lists and emptiness checks agree')
