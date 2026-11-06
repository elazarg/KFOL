#!/usr/bin/env python3
"""Independent, fixed certificate for failure of complementary deletion SD.
Standard library only; no generated-search files or scratch imports.
"""
from itertools import product
import json

def join(a,b): return a if a==b else max(2,a,b)
def f(a,b): return 0 if 0 in (a,b) else join(a,b)
def g(a,b): return 1 if 1 in (a,b) else join(a,b)
native=(f,g,join)
S=((0,0),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,2),(3,3))
Q=(0,1,2,3,4,5,6,7,5)
lookup=dict(zip(S,Q))
tables=[[[None]*8 for _ in range(8)] for _ in native]
cover_checks=0
for k,h in enumerate(native):
    for a,b in product(S,repeat=2):
        value=tuple(h(x,y) for x,y in zip(a,b))
        assert value in lookup
        old=tables[k][lookup[a]][lookup[b]]
        assert old is None or old==lookup[value]
        tables[k][lookup[a]][lookup[b]]=lookup[value]
        cover_checks+=1
assert all(x is not None for h in tables for row in h for x in row)
F,G,J=tables
gens=((3,0),(0,3),(1,2))
generated=set(gens)
while True:
    new={tuple(h(x,y) for x,y in zip(a,b))
         for h in native for a,b in product(generated,repeat=2)}
    if new<=generated: break
    generated|=new
assert generated==set(S)
carrier=range(8)
laws=0
for h in tables:
    for x in carrier:
        assert h[x][x]==x
        laws+=1
    for x,y in product(carrier,repeat=2):
        assert h[x][y]==h[y][x]
        laws+=1
    for x,y,z in product(carrier,repeat=3):
        assert h[h[x][y]][z]==h[x][h[y][z]]
        assert h[x][J[y][z]]==J[h[x][y]][h[x][z]]
        laws+=2
for i,h in enumerate(tables):
    for k,l in enumerate(tables):
        if i==k: continue
        for x,y in product(carrier,repeat=2):
            assert J[h[x][y]][l[x][y]]==J[x][y]
            assert h[x][l[x][y]]==l[x][h[x][y]]
            laws+=2
        for x,y,z in product(carrier,repeat=3):
            a=h[y][z]
            assert h[x][l[y][a]]==h[x][l[y][h[x][a]]]
            laws+=1

p,x,y=map(lookup.__getitem__,gens)
c=F[p][x]
old=J[c][G[G[p][y]][x]]
new=J[c][G[p][y]]
assert (p,x,y,c,old,new,J[p][new])==(6,1,2,0,5,4,7)
assert J[p][old]==old
assert J[p][new]!=new

top=5
rho=[J[a][F[a][G[a][top]]] for a in carrier]
assert rho==[0,1,3,3,5,5,6,5]
common_checks=0
for a,b in product(carrier,repeat=2):
    for h in tables:
        assert rho[h[a][b]]==h[rho[a]][rho[b]]
        if rho[a]==rho[b]:
            assert h[a][b]==J[a][b]
            common_checks+=1
assert all(F[a][G[a][b]]==a for a,b in product(set(rho),repeat=2))

psi=tuple(int(a not in (0,2,4)) for a in carrier)
assert all(psi[J[a][b]]==(psi[a]|psi[b]) for a,b in product(carrier,repeat=2))
assert psi[p]==1 and psi[new]==0
assert all(J[J[p][new]][J[a][new]]==J[a][new] for a in carrier if psi[a])
types={}
for a in carrier:
    if psi[a]: continue
    killed=[i for i,h in enumerate((F,G)) if not psi[h[a][p]]]
    assert len(killed)<=1
    types[a]=killed[0] if killed else 2
assert types=={0:0,2:1,4:2}

# A generator valuation may still separate the target while failing to
# respect positive equalities of the quotient. All actual zero terms
# retain their unique owned/neutral value under this valuation.
pairs={(p,3),(x,0),(y,1)}
while True:
    newpairs={(h[a][b],nh[c][d])
              for h,nh in zip(tables,[[[op(a,b) for b in range(4)]
                                      for a in range(4)] for op in native])
              for (a,c),(b,d) in product(pairs,repeat=2)}
    if newpairs<=pairs:break
    pairs|=newpairs
assert all(v==types[a] for a,v in pairs if not psi[a])
assert (p,3) in pairs and (4,2) in pairs and (5,2) in pairs

print(json.dumps({'status':'PASS','source_size':len(S),'quotient_size':8,
    'source_generators':gens,'cover_entries':cover_checks,
    'Gamma_M_instances':laws,'common_fiber_entries':common_checks,
    'atomic_retraction':rho,'valuation':[p,x,y],
    'premise_rhs':old,'conclusion_rhs':new,'conclusion_join':J[p][new],
    'zero_ideal':[0,2,4],'target_native_pair_closure':len(pairs)},indent=2))
