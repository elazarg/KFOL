import itertools
def W(i,S): return frozenset(o for o in S if i in o)
def L(i,S): return frozenset(o for o in S if i not in o)
def ch(i, kids):
    U = frozenset().union(*kids); r = set(W(i,U))
    if all(L(i,k) for k in kids): r |= L(i,U)
    return frozenset(r)
def clos(K, leaves):
    S=set(leaves); fr=set(leaves)
    while fr:
        new=set()
        for i in range(K):
            for a in fr:
                for b in list(S):
                    c=ch(i,[a,b])
                    if c not in S: new.add(c)
        S|=new; fr=new
    return S
fmt = lambda s: '{' + ','.join(''.join(map(str,sorted(o))) or '-' for o in sorted(s, key=lambda o:(len(o),sorted(o)))) + '}'
K=2
outs=[frozenset(c) for r in range(K+1) for c in itertools.combinations(range(K), r)]
S=clos(K,[frozenset([o]) for o in outs]); Sl=list(S)
df=[(i,j,a,b,c) for i in range(K) for j in range(K) if i!=j for a in Sl for b in Sl for c in Sl if ch(j,[ch(i,[a,b]),c])!=ch(i,[ch(j,[a,c]),ch(j,[b,c])])]
print(f"K=2 general-sum: #SPE values={len(S)}: {sorted(fmt(s) for s in S)}; distributivity failures={len(df)}")
if df:
    i,j,a,b,c=min(df,key=lambda t:sum(len(x) for x in t[2:]))
    print(f"  smallest: i={i} j={j} a={fmt(a)} b={fmt(b)} c={fmt(c)} LHS={fmt(ch(j,[ch(i,[a,b]),c]))} RHS={fmt(ch(i,[ch(j,[a,c]),ch(j,[b,c])]))}")
# smallest one-hot K=3 counterexample, values restricted to dictator leaves and depth-1 values
K=3
dic=[frozenset([frozenset([j])]) for j in range(K)]
S=clos(K,dic); Sl=sorted(S,key=len)
df=[(i,j,a,b,c) for i in range(K) for j in range(K) if i!=j for a in Sl for b in Sl for c in Sl if ch(j,[ch(i,[a,b]),c])!=ch(i,[ch(j,[a,c]),ch(j,[b,c])])]
i,j,a,b,c=min(df,key=lambda t:sum(len(x) for x in t[2:]))
print(f"K=3 one-hot smallest: i={i} j={j} a={fmt(a)} b={fmt(b)} c={fmt(c)} LHS={fmt(ch(j,[ch(i,[a,b]),c]))} RHS={fmt(ch(i,[ch(j,[a,c]),ch(j,[b,c])]))}")
