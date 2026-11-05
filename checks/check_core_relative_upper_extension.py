#!/usr/bin/env python3
"""Independent exact finite check of the bounded deflation and guarded lift.
The universal theorem is proved separately; this checks the native
D_K semantic classification and many exact contextual instances of exhaustion.
"""
from itertools import product
from functools import reduce
from random import Random
from hashlib import sha256
import json
from pathlib import Path

class D:
 def __init__(self,k):
  self.k=k;self.n=k;self.p=k+1;self.A=tuple(range(k+2))
  self.j=[[a if a==b else self.p if self.p in (a,b) else self.n for b in self.A] for a in self.A]
  self.f=[[[i if i in (a,b) else self.j[a][b] for b in self.A] for a in self.A] for i in range(k)]
 def join(self,seq):return reduce(lambda a,b:self.j[a][b],seq)

rng=Random(481231);digest=sha256();counts={};cache={}
for k,mmax in [(3,5),(4,4),(5,3)]:
 A=D(k)
 for m in range(1,mmax+1):
  tuples=list(product(range(m),repeat=k));count=0
  for ys in product(A.A,repeat=m):
   d=A.join(ys)
   for x in A.A:
    initial=A.j[x][d];z=initial
    for inds in tuples:
     previous=z
     z=A.j[d][A.join([A.f[i][previous][ys[inds[i]]] for i in range(k)])]
     assert A.j[d][z]==z and A.j[z][previous]==previous
    ownfolds=[reduce(lambda a,b,i=i:A.f[i][a][b],ys) for i in range(k)]
    direct=A.j[d][A.join([A.f[i][x][ownfolds[i]] for i in range(k)])]
    assert direct==z,(k,m,x,ys,direct,z)
    predicted=d if A.p in ys or all(i in ys for i in range(k)) else initial
    assert z==predicted,(k,m,x,ys,z,predicted)
    if z!=d:assert any(i not in (z,)+ys for i in range(k))
    digest.update(bytes((k,m,x,*ys,z)))
    if k==3 and m<=4:cache[(m,x,ys)]=z
    count+=1
  counts[f'D{k}_coefficients{m}']=count

# Expression tuples: ('v',i), ('+',s,t), (owner,s,t).
def V(i):return ('v',i)
def add(s,t):return ('+',s,t)
def choice(i,s,t):return (i,s,t)
def ev(A,t,values):
 if t[0]=='v':return values[t[1]]
 a=ev(A,t[1],values);b=ev(A,t[2],values)
 return A.j[a][b] if t[0]=='+' else A.f[t[0]][a][b]
def summands(ts):return reduce(add,ts)
A=D(3);identity_checks=0;baseline_required=0
for m in (3,4):
 # Seed E with c=x; for m=4 also seed E with c=y4 (x dummy).
 seed=[]
 for cv in ([0] if m==3 else [0,4]):
  c=V(cv);N=summands([choice(i,c,V(i+1)) for i in range(3)])
  seed.append((add(c,N),N))
 identities=list(seed)
 for _ in range(30):
  s,t=rng.choice(identities);coef=V(rng.randrange(m+1));op=rng.choice(['+',0,1,2])
  build=add if op=='+' else lambda a,b,op=op:choice(op,a,b)
  identities.append((build(s,coef),build(t,coef)))
 for ys in product(A.A,repeat=m):
  d=A.join(ys)
  for x in A.A:
   z=cache[(m,x,ys)]
   for s,t in identities:
    baseline=A.j[ev(A,s,(d,)+ys)][ev(A,t,(d,)+ys)]
    raw_left=ev(A,s,(z,)+ys);raw_right=ev(A,t,(z,)+ys)
    baseline_required += raw_left != raw_right
    left=A.j[baseline][raw_left]
    right=A.j[baseline][raw_right]
    assert left==right,(m,x,ys,s,t,z,left,right)
    digest.update(bytes((m,x,*ys,z,baseline,left)))
    identity_checks+=1
assert baseline_required > 0
# The stronger pointwise upper-substitution reconstruction is false.
data=json.loads((Path(__file__).parent/'data'/'core-owned-unit-observer-countermodel.json').read_text())
join,first=data['join'],data['operations'][0]
valuation=[1,6,8];upper=reduce(lambda a,b:join[a][b],valuation)
def ternary(values):return join[first[values[0]][values[1]]][values[2]]
cofactors=[]
for i in range(3):
 changed=valuation[:];changed[i]=upper;cofactors.append(ternary(changed))
assert upper==7 and ternary(valuation)==9 and cofactors==[7,7,7]
assert join[9][7]==7 and 9!=7
result={'status':'all assertions passed','normalizer_counts':counts,'normalizer_total':sum(counts.values()),'direct_formula_comparisons':sum(counts.values()),'guarded_identity_evaluations':identity_checks,'baseline_required_evaluations':baseline_required,'pointwise_reconstruction_counterexample':{'original':9,'cofactors':cofactors},'certificate_sha256':digest.hexdigest(),'scope':'Every native D_K assignment in listed coefficient arities; exact bounded-deflation sequence; 31 or32 contextual exhaustion identities per tested arity. Does not turn a finite check into a proof of relative equality.'}
print(json.dumps(result,indent=2))
