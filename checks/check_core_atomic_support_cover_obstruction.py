"""Verify the six-state core obstruction to atomic supported covers.

Checks the native cover, support section, candidate laws, reset units,
and an independently reconstructed index presentation. Standard library only.
"""
from itertools import product,permutations,combinations,combinations_with_replacement
from pathlib import Path
import json
D=json.loads((Path(__file__).parent / 'data' / 'core_atomic_support_cover_obstruction.json').read_text())
ops=D['operations'];f,g,J=ops;n=len(J);R=range(n);q=D['flat_tags'];checks=0
assert n==6 and D['names']==['u','v','w','a','A','b']
for h in ops:
 for x in R:assert h[x][x]==x;checks+=1
 for x,y in product(R,repeat=2):assert h[x][y]==h[y][x];checks+=1
 for x,y,z in product(R,repeat=3):
  assert h[h[x][y]][z]==h[x][h[y][z]];checks+=1
  assert h[x][J[y][z]]==J[h[x][y]][h[x][z]];checks+=1
for i,j in combinations(range(3),2):
 for x,y in product(R,repeat=2):assert J[ops[i][x][y]][ops[j][x][y]]==J[x][y];checks+=1
for i,j in permutations(range(3),2):
 for x,y in product(R,repeat=2):assert ops[i][x][ops[j][x][y]]==ops[j][x][ops[i][x][y]];checks+=1
 for x,y,z in product(R,repeat=3):
  assert ops[i][x][ops[j][y][ops[i][y][z]]]==ops[i][x][ops[j][y][ops[i][x][ops[i][y][z]]]];checks+=1
for i,j,k in permutations(range(3)):
 for x,y in product(R,repeat=2):assert ops[k][ops[i][x][y]][ops[j][x][y]]==J[x][y];checks+=1
for c,x,y,z in product(R,repeat=4):
 s=J[J[f[c][x]][g[c][y]]][J[c][z]]
 assert J[c][s]==s;checks+=1

def bj(a,b):return a if a==b else-1
for x,y in product(R,repeat=2):
 assert q[J[x][y]]==bj(q[x],q[y])
 for i,h in enumerate(ops):
  target=i if i in(q[x],q[y])else bj(q[x],q[y])
  assert q[h[x][y]]==target
  if q[x]==q[y]:assert h[x][y]==J[x][y]
assert set(q)=={-1,0,1}
C=D['coefficient_indices'];assert C==list(range(5))
for x,y in product(C,repeat=2):
 assert all(h[x][y]in C for h in ops)
 assert g[x][y]==J[x][y]
assert f[3][0]!=J[3][0]
assert all(f[4][x]==4 and g[5][x]==5 for x in R)
assert set(C)|{5}==set(R)
# Unique possible common-support section values are the fiber minima.
minima={tag:next(x for x in R if q[x]==tag and all(J[x][y]==y for y in R if q[y]==tag))for tag in set(q)}
assert minima=={-1:0,0:3,1:5}
assert J[minima[0]][minima[1]]!=minima[-1]

# Reconstruct the exact expanded-semiltattice presentation, independently
# from the saved proof, then replay every Horn addition and saturation.
k=2;nr=1<<k;rules=set()
def mon(x,s=0):return nr*x+s
def relation(left,right):
 for r in range(nr):
  a=frozenset(mon(x,s|r)for x,s in left);b=frozenset(mon(x,s|r)for x,s in right)
  for U,V in((a,b),(b,a)):
   if V-U:rules.add((tuple(sorted(U)),tuple(sorted(V-U))))
for x in R:
 for r in range(nr):
  for i in range(k):
   if not r>>i&1:rules.add(((mon(x,r),),(mon(x,r|1<<i),)))
 if q[x]>=0:relation([(x,0)],[(x,1<<q[x])])
for x,y in combinations_with_replacement(R,2):relation([(J[x][y],0)],[(x,0),(y,0)])
for i in range(k):
 for x in R:
  if q[x]!=i:continue
  for y in R:relation([(ops[i][x][y],0)],[(x,0),(y,1<<i)])
rules=sorted(rules);P=D['index_proof']
assert [[list(a),list(b)]for a,b in rules]==P['rules']
additions=0
for x,(target,events)in enumerate(zip(P['closures'],P['derivations'])):
 S={mon(x)}
 for ri,added in events:
  premise,result=rules[ri]
  assert set(premise)<=S
  assert set(added)==set(result)-S
  S.update(added);additions+=len(added)
 assert S==set(target)
 assert all(not set(a)<=S or set(b)<=S for a,b in rules)
assert P['closures'][0]==P['closures'][1]
# Table facts used in the short obstruction proof.
assert J[4][0]==J[4][5]==2 and J[5][0]==1
assert f[3][0]==f[3][5]==3 and g[5][4]==5
assert J[3][4]==4 and J[3][0]==0
print(f'PASS: {checks} candidate-law instances; flat common fibers; explicit five-state one-owner coefficient subalgebra; named global absorbers.')
print(f'PASS: {len(rules)} exact Horn rules, {additions} replayed monomial additions; distinct ordinary elements u,v have equal universal indices.')
# Reset units and the support obstruction to onto maps from whole supported extensions.
def reset(c,x):
 value=J[c][x]
 for h in ops:value=h[x][value]
 return value
units=[c for c in R if all(reset(c,x)==x for x in R)]
supports={c:[x for x in R if J[c][x]==x and all(h[c][x]==x for h in ops)]for c in units}
assert units==[0,3] and supports=={0:[0,1,2],3:[3,4]}
assert all(J[x][h[0][x]]==h[0][x]for h in ops for x in R)
assert 5 not in {x for values in supports.values()for x in values}
print('PASS: reset units exactly {u,a}; u is neutral; common supports are u->{u,v,w}, a->{a,A}; b has none.')
assert [reset(2,x)for x in R]==[2,2,2,4,4,5]
assert f[3][0]!=J[3][0] and g[5][0]!=J[5][0] and f[3][5]!=J[3][5]
# A direct native HS cover: remove one section coefficient, then quotient.
cover=D['native_cover'];source=list(map(tuple,cover['source']));image=cover['map'];mapping=dict(zip(source,image))
assert len(mapping)==7 and set(image)==set(R)
def native_join(x,y):return x if x==y else max(2,x,y)
def native_op(i,x,y):return i if i<2 and i in(x,y)else native_join(x,y)
def coordinate_op(i,x,y):return tuple(native_op(i,a,b)for a,b in zip(x,y))
entries=0
for x,y in product(source,repeat=2):
 for i in range(3):
  z=coordinate_op(i,x,y);assert z in mapping
  assert mapping[z]==ops[i][mapping[x]][mapping[y]];entries+=1
whole=set(source)|{tuple(cover['omitted_section_point'])};section=set(map(tuple,cover['section']))
assert len(whole)==8 and len(section)==3
retract=lambda x:tuple(2 if a==3 else a for a in x)
assert {retract(x)for x in whole}==section
for x,y in product(whole,repeat=2):
 for i in range(3):
  z=coordinate_op(i,x,y);assert z in whole
  assert retract(z)==coordinate_op(i,retract(x),retract(y))
for x in whole:
 assert retract(x)in whole and retract(retract(x))==retract(x)
 assert all(coordinate_op(i,retract(x),x)==x for i in range(3))
print(f'PASS: reset at w has exact flat fibers; all three possible tag mergers fail common-join compatibility.')
print(f'PASS: {entries}-entry onto native cover from seven states in D2^2; adding the omitted section point gives an eight-state atomic common-support extension.')
