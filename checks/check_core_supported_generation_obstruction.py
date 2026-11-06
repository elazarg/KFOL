#!/usr/bin/env python3
"""A genuine-core, neutral-unit, SI counterexample to generation by the
unit-supported region and the global absorbers. Standard library only.
"""
import itertools,json,collections
from pathlib import Path
D=json.loads((Path(__file__).parent/'data'/'core_supported_generation_obstruction.json').read_text())
J,f,g=D['tables'];R=range(6);H=[J,f,g];choices=[f,g,J];law_checks=0
for h in H:
 for x in R:assert h[x][x]==x;law_checks+=1
 for x,y in itertools.product(R,repeat=2):assert h[x][y]==h[y][x];law_checks+=1
 for x,y,z in itertools.product(R,repeat=3):assert h[x][h[y][z]]==h[h[x][y]][z];law_checks+=1
for h in choices:
 for x,y,z in itertools.product(R,repeat=3):assert h[x][J[y][z]]==J[h[x][y]][h[x][z]];law_checks+=1
for h,k in itertools.combinations(choices,2):
 for x,y in itertools.product(R,repeat=2):
  assert J[h[x][y]][k[x][y]]==J[x][y];assert h[x][k[x][y]]==k[x][h[x][y]];law_checks+=2
for h,k in itertools.permutations(choices,2):
 for x,y,z in itertools.product(R,repeat=3):assert h[x][k[y][h[y][z]]]==h[x][k[y][h[x][h[y][z]]]];law_checks+=1
for h,k,l in itertools.permutations(choices,3):
 for x,y in itertools.product(R,repeat=2):assert l[h[x][y]][k[x][y]]==J[x][y];law_checks+=1
for c,x,y,z in itertools.product(R,repeat=4):
 n=J[J[f[c][x]][g[c][y]]][J[c][z]];assert J[c][n]==n;law_checks+=1
assert f!=J and g!=J
# Native cover: an11-element subalgebra of D2^3 onto this6-element model.
NJ=[[x if x==y else max(2,x,y)for y in range(4)]for x in range(4)]
NH=[NJ]+[[[i if i in(x,y)else NJ[x][y]for y in range(4)]for x in range(4)]for i in range(2)]
source=list(map(tuple,D['native_source']));image=D['onto_map'];mapping=dict(zip(source,image))
assert len(source)==len(mapping)==len(image)==11 and set(image)==set(R)
cover_checks=0
for h,native in zip(H,NH):
 for x,y in itertools.product(source,repeat=2):
  z=tuple(native[a][b]for a,b in zip(x,y));assert z in mapping
  assert mapping[z]==h[mapping[x]][mapping[y]];cover_checks+=1
# D2 is a proper-owner observer in the3-owner core signature, hence this
# checked HS(D2^3) certificate proves genuine core membership.
reset=[[g[x][f[x][J[c][x]]]for x in R]for c in R]
assert all(J[x][reset[c][x]]==reset[c][x]for c,x in itertools.product(R,repeat=2))
units=[c for c in R if all(reset[c][x]==x for x in R)]
neutral=[c for c in units if all(J[x][h[c][x]]==h[c][x]for h in[f,g]for x in R)]
supports={x:[c for c in units if all(h[c][x]==x for h in H)]for x in R}
supported=[x for x in R if supports[x]]
absorbers=[]
for h in[f,g]:
 a=0
 for x in R:a=h[a][x]
 assert all(h[a][x]==a for x in R);absorbers.append(a)
generated=set(supported+absorbers)
while True:
 new=generated|{h[x][y]for h in H for x in generated for y in generated}
 if new==generated:break
 generated=new
assert units==[0,1,2]and neutral==[2]
assert supported==[0,1,2,5]and absorbers==[5,0]
assert generated=={0,1,2,5}and set(R)-generated=={3,4}
# Exhaust all15 principal nonzero congruences to certify SI as well.
pairs=set(itertools.combinations(R,2));intersection=pairs.copy()
for x,y in pairs:
 parent=list(R);queue=collections.deque([(x,y)])
 def root(a):
  while parent[a]!=a:a=parent[a]
  return a
 while queue:
  a,b=queue.popleft();a,b=root(a),root(b)
  if a==b:continue
  parent[b]=a
  for h in H:
   for z in R:queue.append((h[a][z],h[b][z]))
 intersection&={(a,b)for a,b in pairs if root(a)==root(b)}
assert intersection=={(1,2)}
print(json.dumps(dict(status='PASS',states=6,units=units,neutral_units=neutral,
                     common_supports=supports,supported=supported,
                     global_absorbers=absorbers,generated=sorted(generated),
                     missing=sorted(set(R)-generated),monolith=sorted(intersection),
                     candidate_law_checks=law_checks,native_cover_states=11,
                     native_cover_entries=cover_checks),sort_keys=True))
