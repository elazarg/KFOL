"""Replay exact native-base supported extensions and their core embeddings.

Only the recorded ground proofs are replayed; no search or solver is used.
Term support and fiber linearization invoke the proved supported-extension
lemmas. Every other merge is a displayed presentation/Sigma equation or ACI
congruence. The full closed tables are checked separately.
"""
import json,itertools,collections,time
from pathlib import Path

def full_laws(join,choices):
 states=range(len(join))
 for op in[join]+choices:
  if any(op[x][x]!=x for x in states):return 'idempotence'
  if any(op[x][y]!=op[y][x]for x,y in itertools.product(states,repeat=2)):return 'commutativity'
  if any(op[x][op[y][z]]!=op[op[x][y]][z]for x,y,z in itertools.product(states,repeat=3)):return 'associativity'
 for f in choices:
  if any(f[x][join[y][z]]!=join[f[x][y]][f[x][z]]for x,y,z in itertools.product(states,repeat=3)):return 'distribution'
 for f,g in itertools.combinations(choices,2):
  if any(join[f[x][y]][g[x][y]]!=join[x][y]or f[x][g[x][y]]!=g[x][f[x][y]]for x,y in itertools.product(states,repeat=2)):return 'coverage/Birkhoff'
 for f,g,h in itertools.permutations(choices,3):
  if any(h[f[x][y]][g[x][y]]!=join[x][y]for x,y in itertools.product(states,repeat=2)):return 'union-definition'
 for f,g in itertools.permutations(choices,2):
  if any(f[x][g[y][f[y][z]]]!=f[x][g[y][f[x][f[y][z]]]]for x,y,z in itertools.product(states,repeat=3)):return 'mixed'
 for c in states:
  values=set(choices[0][c])
  for f in choices[1:]:values={join[a][b]for a in values for b in f[c]}
  if any(join[c][z]!=z for z in values):return 'exhaustion'
 return None

def replay(D):
 assert D['status']=='FREE PRESENTATION COMPLETE'
 nodes=D['nodes_dag'];events=D['merges_proof'];T=D['table'];c=D['base_support']
 J=[[a if a==b else max(2,a,b)for b in range(4)]for a in range(4)];C=[[[i if i in(a,b)else J[a][b]for b in range(4)]for a in range(4)]for i in range(2)]+[J]
 parent=[];uses=[];base=[];keys=[];index=collections.defaultdict(set);counts=collections.Counter()
 def root(x):
  while parent[x]!=x:x=parent[x]
  return x
 def key(h,a,b):
  a,b=root(a),root(b);return(h,min(a,b),max(a,b))
 def declare(v):
  parent.append(v);uses.append(set());keys.append(None)
  if v<5:assert nodes[v]is None;base.append(v if v<4 else c);return
  h,a,b=nodes[v];assert a<v and b<v;base.append(C[h][base[a]][base[b]]);k=key(h,a,b);keys[v]=k;index[k].add(v);uses[root(a)].add(v);uses[root(b)].add(v)
 def op(h,a,b):
  k=key(h,a,b);_,a,b=k
  if a==b:return a
  assert k in index and index[k],('MISSING OPERATION',k)
  images={root(v)for v in index[k]};assert len(images)==1,('PENDING CONGRUENCE BEFORE AXIOM',k,images)
  return next(iter(images))
 def union(a,b):
  assert root(a)==a and root(b)==b and a<b
  affected=list(uses[b]);parent[b]=a;uses[a].update(uses[b]);uses[b].clear()
  for v in affected:
   old=keys[v];index[old].remove(v)
   if not index[old]:del index[old]
   h,x,y=nodes[v];new=key(h,x,y);keys[v]=new;index[new].add(v)
 def equation(reason):
  name,values=reason
  if name=='coefficient-table':h,a,b=values;return op(h,a,b),C[h][a][b]
  if name=='generator-support':h,=values;return op(h,c,4),4
  if name=='term-support':h,x=values;return op(h,base[x],x),x
  if name=='fiber-linearization':h,x,y=values;return op(h,x,y),op(2,op(h,base[x],y),op(h,base[y],x))
  if name=='coverage':x,y=values;return op(2,op(0,x,y),op(1,x,y)),op(2,x,y)
  if name=='Birkhoff':x,y=values;return op(0,x,op(1,x,y)),op(1,x,op(0,x,y))
  if name=='associativity':h,x,y,z=values;return op(h,x,op(h,y,z)),op(h,op(h,x,y),z)
  if name=='distribution':h,x,y,z=values;return op(h,x,op(2,y,z)),op(2,op(h,x,y),op(h,x,z))
  if name=='mixed':f,h,x,y,z=values;v=op(f,y,z);return op(f,x,op(h,y,v)),op(f,x,op(h,y,op(f,x,v)))
  raise AssertionError(reason)
 for count,a,b,reason in events:
  while len(parent)<count:declare(len(parent))
  assert root(a)==a and root(b)==b and base[a]==base[b]
  if reason[0]=='congruence':
   _,x,y=reason;hx,ax,bx=nodes[x];hy,ay,by=nodes[y];assert key(hx,ax,bx)==key(hy,ay,by);lhs,rhs=x,y
  elif reason[0]=='idempotence':
   _,x=reason;h,v,w=nodes[x];assert root(v)==root(w);lhs,rhs=x,v
  else:lhs,rhs=equation(reason)
  assert {root(lhs),root(rhs)}=={a,b},('INVALID MERGE',a,b,reason,root(lhs),root(rhs));union(a,b);counts[reason[0]]+=1
 while len(parent)<len(nodes):declare(len(parent))
 assert base==D['base_values'];reps=[v for v in range(len(nodes))if root(v)==v];assert reps==T['representatives'];position={v:i for i,v in enumerate(reps)};tables=T['operations'][:2]+[T['join']]
 for v in range(5,len(nodes)):
  h,a,b=nodes[v];assert position[root(v)]==tables[h][position[root(a)]][position[root(b)]]
 for h,H in enumerate(tables):
  for x,y in itertools.product(range(len(reps)),repeat=2):assert position[root(op(h,reps[x],reps[y]))]==H[x][y]
 assert [position[root(v)]for v in range(4)]==T['constants'];assert position[root(4)]==T['u']
 for h,H in enumerate(tables):
  for a,b in itertools.product(range(4),repeat=2):assert H[T['constants'][a]][T['constants'][b]]==T['constants'][C[h][a][b]]
  assert H[T['constants'][c]][T['u']]==T['u']
 assert full_laws(T['join'],T['operations'])is None
 reached=set(T['constants']+[T['u']]);old=-1
 while len(reached)!=old:
  old=len(reached);reached|={H[a][b]for H in tables for a,b in itertools.product(reached,repeat=2)}
 assert len(reached)==len(reps)
 projection=[base[x]for x in reps]
 for H,N in zip(tables,C):
  for a,b in itertools.product(range(len(reps)),repeat=2):assert projection[H[a][b]]==N[projection[a]][projection[b]]
  for a in range(len(reps)):assert H[T['constants'][projection[a]]][a]==a
 return {'states':len(reps),'nodes':len(nodes),'merges':sum(counts.values()),'table_entries':3*len(reps)**2,'fibers':[projection.count(a)for a in range(4)]}

def check_native(T,maps):
 J=[[a if a==b else max(2,a,b)for b in range(4)]for a in range(4)]
 native=[[[i if i in(a,b)else J[a][b]for b in range(4)]for a in range(4)]for i in range(2)]+[J]
 tables=T['operations'][:2]+[T['join']];n=len(T['join']);entries=0
 for m in maps:
  assert len(m)==n and all(0<=x<4 for x in m)
  for H,N in zip(tables,native):
   for a,b in itertools.product(range(n),repeat=2):assert m[H[a][b]]==N[m[a]][m[b]];entries+=1
 assert len({tuple(m[x]for m in maps)for x in range(n)})==n
 return entries

def main():
 start=time.monotonic();data=json.loads(Path(__file__).with_name('core_native_supported_extensions.json').read_text());stats={};native_entries=0
 for c,D in data['cases'].items():
  stats[c]=replay(D);native_entries+=check_native(D['table'],D['native_maps']);stats[c]['native_coordinates']=len(D['native_maps'])
 symmetry=data['symmetry'];assert symmetry=={'source':0,'target':1,'coefficient_permutation':[1,0,2,3],'operation_permutation':[1,0,2]}
 A=data['cases']['0']['table'];swap=symmetry['coefficient_permutation'];B={'join':A['join'],'operations':[A['operations'][1],A['operations'][0],A['join']],'constants':[A['constants'][i]for i in swap],'u':A['u']}
 assert full_laws(B['join'],B['operations'])is None
 maps=[[swap[x]for x in m]for m in data['cases']['0']['native_maps']];native_entries+=check_native(B,maps)
 J=[[a if a==b else max(2,a,b)for b in range(4)]for a in range(4)];native=[[[i if i in(a,b)else J[a][b]for b in range(4)]for a in range(4)]for i in range(2)]+[J]
 for h,H in enumerate(B['operations'][:2]+[B['join']]):
  for a,b in itertools.product(range(4),repeat=2):assert H[B['constants'][a]][B['constants'][b]]==B['constants'][native[h][a][b]]
  assert H[B['constants'][1]][B['u']]==B['u']
 stats['1']={'states':len(B['join']),'proof':'signature symmetry','native_coordinates':len(maps)}
 # The three-state base embeds into D^2, but the universal supported
 # extension does not preserve this embedding. Check the base and source
 # distinction independently of the ground certificates above. The target
 # identification is the associativity/coverage proof in the manuscript.
 coefficient_pairs=[(0,2),(2,1),(2,2)];coefficient_image=[0,1,2]
 coefficient_index={v:i for i,v in enumerate(coefficient_pairs)};base_entries=0
 for H in native:
  for x,y in itertools.product(range(3),repeat=2):
   value=tuple(H[a][b]for a,b in zip(coefficient_pairs[x],coefficient_pairs[y]))
   assert value in coefficient_index
   assert coefficient_image[coefficient_index[value]]==H[coefficient_image[x]][coefficient_image[y]]
   base_entries+=1
 d=(0,1);c=coefficient_pairs[2]
 assert tuple(J[x][y]for x,y in zip(d,c))==c
 assert tuple(native[0][x][y]for x,y in zip(d,c))==coefficient_pairs[0]
 assert tuple(native[1][x][y]for x,y in zip(d,c))==coefficient_pairs[1]
 assert all(H[2][3]==3 for H in native)
 assert J[native[0][3][0]][native[1][3][1]]==2
 print('Verified exact free presentations:',stats)
 print('Ground merges:',sum(v.get('merges',0)for v in stats.values()),'; native homomorphism entries:',native_entries,'; seconds:',round(time.monotonic()-start,3))
 print('Embedding-preservation obstruction: base entries',base_entries,'; source pair p != n; target lower coefficient d=(alpha,beta) verified.')

if __name__=='__main__':main()
