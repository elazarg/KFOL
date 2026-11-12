#!/usr/bin/env python3
"""Independent standard-library checks for the canonical-D research package."""
from itertools import product, combinations
import ast, argparse

B,C,P,N=0,1,2,3
RI=(0,3,1,2); RS=(0,3,2,1)
def inf(x,y): return x if RI[x] <= RI[y] else y
def sup(x,y): return x if RS[x] >= RS[y] else y

def parse(s): return ast.parse(s,mode='eval').body

def evaluate(t,v):
    if isinstance(t,ast.Name): return v[ord(t.id)-97]
    x,y=evaluate(t.left,v),evaluate(t.right,v)
    return inf(x,y) if isinstance(t.op,ast.BitAnd) else sup(x,y)

def truth(s,n):
    t=parse(s)
    return sum(evaluate(t,[(i>>j)&1 for j in range(n)])<<i for i in range(1<<n))

def dual(f,n): return sum((1-(f>>((1<<n)-1-i)&1))<<i for i in range(1<<n))

def minterms(f,n):
    return [s for s in range(1<<n) if f>>s&1 and all(not(f>>(s^(1<<j))&1) for j in range(n) if s>>j&1)]

def cube_vertices(q):
    lo=sum((x==1)<<j for j,x in enumerate(q)); free=sum((x is None)<<j for j,x in enumerate(q))
    return [s for s in range(1<<len(q)) if s&~free==lo]

def essential(f,q,j):
    return any((f>>s&1)!=(f>>(s|1<<j)&1) for s in cube_vertices(q) if not(s>>j&1))

def extension(f,v):
    q=tuple(None if x>=2 else x for x in v); vs=cube_vertices(q); values={f>>s&1 for s in vs}
    if len(values)==1: return values.pop()
    return P if any(x==P and essential(f,q,j) for j,x in enumerate(v)) else N

def constraints(n,f):
    out=[]
    for q in product((0,1,None),repeat=n):
        vs=cube_vertices(q)
        if len({f>>s&1 for s in vs})<2: continue
        for j,x in enumerate(q):
            if x is None and not essential(f,q,j): out.append((q,j))
    return out

def dual_constraints(rows):
    return [(tuple(None if x is None else 1-x for x in q),j) for q,j in rows]

def reachability(f,n,rows):
    nodes=[s for s in range(1<<n) if f>>s&1]
    a=[0]*(1<<n)
    for s in nodes:
        a[s]=1<<s
        for j in range(n): a[s] |= 1<<(s|1<<j)
    for q,j in rows:
        assert q[j] is None
        assert len({f>>s&1 for s in cube_vertices(q)})==2
        assert not essential(f,q,j)
        for s in cube_vertices(q):
            if f>>s&1 and s>>j&1: a[s] |= 1<<(s^(1<<j))
    for k in nodes:
        for s in nodes:
            if a[s]>>k&1: a[s] |= a[k]
    return a

def vertex(s): return sum(1<<(ord(x)-97) for x in s)

# P4 base obstruction: four ordinary Boolean cofactor independence obligations.
p4=truth('(a&b)|(a&c)|(b&d)',4)
p4rows=[((None,1,None,0),2),((1,None,0,None),3),((None,None,1,0),1),((None,None,0,1),0)]
r=reachability(p4,4,p4rows)
assert r[vertex('ac')]==p4
p4dual=dual(p4,4)
assert p4dual==truth('(a&b)|(a&d)|(b&c)',4)
print('P4: four-cofactor OR obstruction and dual permutation verified.')

# Self-dual weighted-majority obstruction.
w=truth('(a&b)|(a&c)|(a&d&e)|(b&c&d)|(b&c&e)',5)
assert w==3941132456 and dual(w,5)==w
for s in range(32): assert (w>>s&1)==(sum(x for j,x in enumerate((3,2,2,1,1)) if s>>j&1)>=5)
wr=[((1,None,None,None,0),3),((None,1,None,0,0),2),((None,None,1,0,0),1),((0,1,None,None,1),3),((None,None,0,1,1),1)]
assert reachability(w,5,wr)[vertex('bcd')]==w
print('Weighted majority: threshold (3,2,2,1,1;5), self-duality, and five-cofactor obstruction verified.')

# Six-variable hereditary-SCC counterexample.
F=truth('(c&d)|(a&f)|(a&c&e)|(a&d&e)|(c&e&f)|(b&d&e&f)',6)
H=truth('(c&d)|(a&f)|(a&d&e)|(c&e&f)|(b&d&e&f)',6)
K=truth('a&c&(e|(d&f))',6)
assert F==18373273242067595264 and H==18373273242057109504
rows=[((0,None,None,None,None,0),4),((1,None,None,None,None,None),1),
      ((None,0,None,1,1,None),5),((None,0,None,None,1,1),3),
      ((None,None,0,0,None,None),4),((None,None,0,None,0,None),3),
      ((None,None,1,None,None,None),1),((None,None,None,0,0,None),2)]
rF=reachability(F,6,rows); rH=reachability(H,6,rows)
assert rF[vertex('bdef')]==H and rH[vertex('bdef')]==H
assert F^H == (1<<vertex('ace'))|(1<<vertex('abce'))
assert rF[vertex('abce')]>>vertex('ace')&1
assert rF[vertex('ace')]>>vertex('abce')&1
Fd,Hd=dual(F,6),dual(H,6)
rdF=reachability(Fd,6,dual_constraints(rows)); rdH=reachability(Hd,6,dual_constraints(rows))
assert rdF[vertex('cef')]==Fd
assert rdH[vertex('df')]==Hd
assert Hd == Fd | truth('d&f',6)
print('Six variables: complete eight-cofactor two-function descent certificate verified.')

# Verify the full root safe cover against EVERY partial Boolean cube.
full=constraints(6,F)
for g in (H,K):
    for q,j in full: assert not essential(g,q,j)
assert H|K==F and H!=F and K!=F
print('Six variables: H and K are strict safe OR children covering F on all cubes.')

# Explicit pure term witnesses for all twelve one-variable cofactors.
witnesses=[
 (0,0,'((((f&b)&(e&d))|c)&((f&e)|d))'),
 (0,1,'(((d|c)&e)|((d&c)|f))'),
 (1,0,'(((((d|c)&e)|f)&a)|(((f&e)|d)&c))'),
 (1,1,'((((d|c)&e)&(f|a))|((f&a)|(d&c)))'),
 (2,0,'((((f&b)&(e&d))|a)&((e&d)|f))'),
 (2,1,'(((e|a)&f)|((e&a)|d))'),
 (3,0,'(((f&a)|(e&c))&(f|a))'),
 (3,1,'(((((e&b)&f)|a)&(f|e))|c)'),
 (4,0,'((f&a)|(d&c))'),
 (4,1,'((((d&b)&f)|(c|a))&((f|d)|(c&a)))'),
 (5,0,'(((e&a)|(d&c))&(d|c))'),
 (5,1,'(((((d&b)&e)|c)&(e|d))|a)'),
]
for j,b,s in witnesses:
    t=parse(s); free=[k for k in range(6) if k!=j]
    for vv in product(range(4),repeat=5):
        v=[b]*6
        for k,x in zip(free,vv): v[k]=x
        assert evaluate(t,v)==extension(F,v),(j,b,v,s)
print('Six variables: all twelve cofactor terms verified on all 1024 inputs each.')

# Cotree construction and independent full-table validation for graph functions.
def components(V,E,complement=False):
    rem=set(V); out=[]
    while rem:
        todo=[rem.pop()]; C=set(todo)
        while todo:
            a=todo.pop(); new={b for b in rem if ((tuple(sorted((a,b))) in E)!=complement)}
            C.update(new);todo.extend(new);rem.difference_update(new)
        out.append(C)
    return out

def fold(op,ts):
    ts=list(ts)
    if not ts:return None
    t=ts[0]
    for u in ts[1:]:t=(op,t,u)
    return t

def coterm(V,E):
    if len(V)==1:return None
    cs=components(V,E)
    if len(cs)>1:return fold('or',(t for C in cs if (t:=coterm(C,E)) is not None))
    cs=components(V,E,True)
    if len(cs)==1:raise ValueError('induced P4')
    ts=[t for C in cs if (t:=coterm(C,E)) is not None]
    us=[fold('or',sorted(C)) for C in cs]
    ts.extend(('and',s,t) for s,t in combinations(us,2))
    return fold('or',ts)

def tree_eval(t,v):
    if isinstance(t,int):return v[t]
    op,s,u=t
    return (inf if op=='and' else sup)(tree_eval(s,v),tree_eval(u,v))

args=argparse.ArgumentParser();args.add_argument('--exhaustive-cographs',action='store_true');a=args.parse_args()
for n in range(2,6 if a.exhaustive_cographs else 5):
    pairs=list(combinations(range(n),2));count=0
    for bits in range(1,1<<len(pairs)):
        E={e for i,e in enumerate(pairs) if bits>>i&1}
        try:t=coterm(set(range(n)),E)
        except ValueError:continue
        count+=1; f=sum(any((s>>i&1)and(s>>j&1) for i,j in E)<<s for s in range(1<<n))
        for v in product(range(4),repeat=n):assert tree_eval(t,v)==extension(f,v)
    assert count=={2:1,3:7,4:51,5:471}[n]
    print(f'Cographs n={n}: {count} nonempty-edge graphs, complete 4^{n} tables verified.')
print('All checks passed. No external files or non-standard packages used.')
