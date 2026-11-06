#!/usr/bin/env python3
"""Exact B3 plus ONE new global f0-absorber presentation.
No native values justify a ground or Horn identification.
The other two absorber names used in the auxiliary ground proof are
interpreted by fi(ci,a0), using the absorber-fiber subalgebra lemma.
"""
import json,gzip,itertools,collections,time,argparse
from pathlib import Path
K=3
j=[[a if a==b else 3 for b in range(4)]for a in range(4)]
flat_native=[[[i if i in(a,b)else j[a][b]for b in range(4)]for a in range(4)]for i in range(3)]+[j]
def full_laws(tables):
 f,g,j=tables;choices=[f,g,j];R=range(len(j))
 for h in tables:
  assert all(h[x][x]==x for x in R)
  assert all(h[x][y]==h[y][x]for x,y in itertools.product(R,repeat=2))
  assert all(h[x][h[y][z]]==h[h[x][y]][z]for x,y,z in itertools.product(R,repeat=3))
 for h in choices:
  assert all(h[x][j[y][z]]==j[h[x][y]][h[x][z]]for x,y,z in itertools.product(R,repeat=3))
 for h,k in itertools.combinations(choices,2):
  assert all(j[h[x][y]][k[x][y]]==j[x][y]and h[x][k[x][y]]==k[x][h[x][y]]for x,y in itertools.product(R,repeat=2))
 for h,k,l in itertools.permutations(choices,3):assert all(l[h[x][y]][k[x][y]]==j[x][y]for x,y in itertools.product(R,repeat=2))
 for h,k in itertools.permutations(choices,2):assert all(h[x][k[y][h[y][z]]]==h[x][k[y][h[x][h[y][z]]]]for x,y,z in itertools.product(R,repeat=3))
 for c in R:
  sums=set(f[c])
  for h in choices[1:]:sums={j[a][b]for a in sums for b in h[c]}
  assert all(j[c][z]==z for z in sums)

def check_unary_schema(D):
 a,b,z='a','b','z';F=[0,b,z];G=[1,a,z]
 asts=[a,b,[2,a,b],z,F,G,[0,b,G],[2,a,z],[2,a,F],[2,b,z],[2,b,G],[2,[2,a,b],z]]
 assert D['proved_unary_schema']['form_asts']==asts
 def join(x,y):
  if x==y:return x
  if 6 in(x,y):return 6
  return 2+((1<<x if x<2 else x-2)|(1<<y if y<2 else y-2))
 J=[[join(x,y)for y in range(7)]for x in range(7)]
 H=[[[i if i in(x,y)else J[x][y]for y in range(7)]for x in range(7)]for i in range(2)]+[J]
 full_laws(H)
 assert set(H[0][0])=={0}and set(H[1][1])=={1}
 # The singleton coefficient theorem bounds its universal extension by12.
 # These12 distinct closed functions on the candidate A* attain that bound.
 def ev(t,x):
  if isinstance(t,str):return {'a':0,'b':1,'z':x}[t]
  h,u,v=t;return H[h][ev(u,x)][ev(v,x)]
 vals=[tuple(ev(t,x)for x in range(7))for t in asts];assert len(set(vals))==12
 for table,h in zip(D['proved_unary_schema']['operations'],H):
  assert len(table)==12 and all(len(row)==12 for row in table)
  for i,j in itertools.product(range(12),repeat=2):assert vals[table[i][j]]==tuple(h[x][y]for x,y in zip(vals[i],vals[j]))

def types_for(h,x,y,C):
 out=[]
 for owner in range(K):
  a,b=x[owner],y[owner]
  if h==owner:
   if a[0]=='a'or b[0]=='a':t=('a',)
   elif a[0]==b[0]=='s':t=('s',C[h][a[1]][b[1]])
   elif a[0]==b[0]=='e':t=('e',)
   else:t=a if a[0]=='s'else b
  else:
   if a[0]=='e'or b[0]=='e':t=('e',)
   elif a[0]==b[0]=='s':t=('s',C[h][a[1]][b[1]])
   elif a[0]==b[0]=='a':t=('a',)
   else:t=a if a[0]=='s'else b
  out.append(t)
 return out

def replay_words(D):
 check_unary_schema(D)
 assert D['base_tables']==flat_native
 C=D['base_tables'];m=len(C[0]);nodes=D['nodes_dag'];parent=[];uses=[];keys=[];base=[];types=[];index=collections.defaultdict(set);unary=D['proved_unary_schema'];counts=collections.Counter()
 split={x:next(((a,b)for a in range(m)for b in range(a+1,m)if C[K][a][b]==x and a!=x and b!=x),None)for x in range(m)}
 def root(x):
  while parent[x]!=x:x=parent[x]
  return x
 def key(h,a,b):
  a,b=root(a),root(b);return(h,min(a,b),max(a,b))
 def declare(v):
  parent.append(v);uses.append(set());keys.append(None)
  if v<m+K:
   assert nodes[v]is None
   base.append(v if v<m else D['base_absorbers'][v-m]);types.append([('s',v)]*K if v<m else[('a',)if h==v-m else('e',)for h in range(K)])
  else:
   h,a,b=nodes[v];assert a<v and b<v
   base.append(C[h][base[a]][base[b]]);types.append(types_for(h,types[a],types[b],C));k=key(h,a,b);keys[v]=k;index[k].add(v);uses[root(a)].add(v);uses[root(b)].add(v)
  assert types[v]==[tuple(t)for t in D['node_types'][v]],('TYPE',v)
 def op(h,a,b):
  k=key(h,a,b);_,a,b=k
  if a==b:return a
  assert k in index and index[k],('MISSING',k)
  images={root(v)for v in index[k]}
  assert len(images)==1,('PENDING',k,images)
  return next(iter(images))
 def union(a,b):
  assert root(a)==a and root(b)==b and a<b
  affected=list(uses[b]);parent[b]=a;uses[a].update(uses[b]);uses[b].clear()
  for v in affected:
   old=keys[v];index[old].remove(v)
   if not index[old]:del index[old]
   h,x,y=nodes[v];new=key(h,x,y);keys[v]=new;index[new].add(v)
 def unary_ast(t,x,f,h):
  if isinstance(t,str):return {'a':m+f,'b':m+h,'z':x}[t]
  k,a,b=t;return op([f,h,K][k],unary_ast(a,x,f,h),unary_ast(b,x,f,h))
 def flat(x):
  x=root(x)
  if x<m and split[x]is not None:return flat(split[x][0])|flat(split[x][1])
  t=nodes[x]
  return flat(t[1])|flat(t[2])if t is not None and t[0]==K else{x}
 def equation(reason):
  name,v=reason
  if name=='coefficient-table':h,a,b=v;return op(h,a,b),C[h][a][b]
  if name in('generator-absorption','global-absorption'):h,x=v;return op(h,m+h,x),m+h
  if name=='typed-support':h,x,a,k=v;assert k in(h,K);assert ('s',a)in[types[z][h]for z in range(len(parent))if root(z)==root(x)];return op(k,a,x),x
  if name=='typed-join-support':
   x,supports,d=v;assert supports
   z=None
   for h,c in supports:
    assert types[x][h]==('s',c)
    z=c if z is None else C[K][z][c]
   assert z==d
   return op(K,d,x),x
  if name in('upper-coefficient-normalization','fixed-floor-monotonicity'):
   h,c,T,z=v;assert C[K][c][T]==T and C[h][c][T]==T
   assert root(op(K,T,z))==root(z)
   a=op(h,c,z)
   return (a,op(h,T,z))if name=='upper-coefficient-normalization'else(op(K,T,a),a)
  if name=='word-join-evaluation':
   start,path,T=v;x=start;q=op(K,T,start);b=T
   for h,c in path:
    assert 0<=h<K and 0<=c<m
    x=op(h,c,x);q=op(h,c,q);b=C[h][c][b]
   return q,op(K,x,b)
  if name=='typed-linearization':
   h,a,b=v;x,y=types[a][h],types[b][h]
   if x[0]==y[0]=='e':target=op(K,a,b)
   elif x[0]==y[0]=='s':target=op(K,op(h,x[1],b),op(h,y[1],a))
   elif x[0]=='e'and y[0]=='s':target=op(K,b,op(h,y[1],a))
   elif y[0]=='e'and x[0]=='s':target=op(K,a,op(h,x[1],b))
   else:raise AssertionError(reason)
   return op(h,a,b),target
  if name=='join-ACI':
   a,b,atoms=v;assert flat(a)|flat(b)==set().union(*(flat(x)for x in atoms)),('JOIN FLATTEN',v)
   target=atoms[0]
   for z in atoms[1:]:target=op(K,target,z)
   return op(K,a,b),target
  if name=='eager-distribution':h,a,b,c=v;return op(h,a,op(K,b,c)),op(K,op(h,a,b),op(h,a,c))
  if name=='coefficient-distribution':h,c,z,a,b=v;assert C[K][a][b]==c;return op(h,c,z),op(K,op(h,a,z),op(h,b,z))
  if name=='coefficient-composition':h,a,b,z=v;return op(h,a,op(h,b,z)),op(h,C[h][a][b],z)
  if name=='coefficient-commutation':h,k,a,z=v;assert h!=k and h<K and k<K;return op(h,a,op(k,a,z)),op(k,a,op(h,a,z))
  if name=='proved-pair-unary-table':f,h,k,x,i,j=v;assert 0<=f<h<K;forms=[unary_ast(t,x,f,h)for t in unary['form_asts']];return op([f,h,K][k],forms[i],forms[j]),forms[unary['operations'][k][i][j]]
  if name=='proved-sandwich':f,h,x,y,z=v;assert f!=h and 0<=f<K and 0<=h<K;r=C[f][x][C[h][x][y]];return op(f,x,op(h,y,op(f,x,z))),op(f,r,op(h,y,z))
  if name=='proved-ordered-profile':f,h,x,y=v;assert f!=h and 0<=f<K and 0<=h<K and C[K][x][y]==y;return op(f,x,op(h,m+f,y)),op(h,m+f,C[f][x][y])
  if name=='coverage':f,h,x,y=v;assert f!=h and f<K and h<K;return op(K,op(f,x,y),op(h,x,y)),op(K,x,y)
  if name=='Birkhoff':f,h,x,y=v;assert f!=h and f<K and h<K;return op(f,x,op(h,x,y)),op(h,x,op(f,x,y))
  if name=='triple-union':f,h,k,x,y=v;assert {f,h,k}==set(range(K));return op(k,op(f,x,y),op(h,x,y)),op(K,x,y)
  if name=='mixed':f,h,x,y,z=v;q=op(f,y,z);return op(f,x,op(h,y,q)),op(f,x,op(h,y,op(f,x,q)))
  raise AssertionError(reason)
 for event,(count,a,b,reason)in enumerate(D['merges_proof']):
  while len(parent)<count:declare(len(parent))
  assert root(a)==a and root(b)==b and base[a]==base[b]
  if reason[0]=='congruence':
   _,x,y=reason;hx,ax,bx=nodes[x];hy,ay,by=nodes[y];assert key(hx,ax,bx)==key(hy,ay,by);lhs,rhs=x,y
  elif reason[0]=='idempotence':_,x=reason;h,u,v=nodes[x];assert root(u)==root(v);lhs,rhs=x,u
  else:lhs,rhs=equation(reason)
  assert {root(lhs),root(rhs)}=={a,b},('MERGE',event,a,b,reason,root(lhs),root(rhs));union(a,b);counts[reason[0]]+=1
 while len(parent)<len(nodes):declare(len(parent))
 assert base==D['base_values']
 basis=list(range(m))+list(D['representatives'].values());ix={root(v):i for i,v in enumerate(basis)};assert len(ix)==79
 assert D['missing']==[]
 for h in range(K):
  for c in range(m):
   for w in basis:assert root(op(h,c,w))in ix
 print('VALID CLOSED WORD BASIS:',len(nodes),'nodes;',len(D['merges_proof']),'merges;',len(basis),'basis terms',flush=True)

 actions=[[[ix[root(op(h,c,w))]for w in basis]for c in range(m)]for h in range(K)]
 return C,basis,types,actions,[root(v)for v in range(len(nodes))]

def members(mask):
 while mask:
  bit=mask&-mask;yield bit.bit_length()-1;mask^=bit

def verify_one_absorber(D,H,C,full_basis,types,full_actions,roots,coordinates):
 m=len(C[0]);nodes=D['nodes_dag'];pure=[]
 for v,t in enumerate(nodes):pure.append(v<m or v==m if t is None else pure[t[1]]and pure[t[2]])
 basis=H['basis_nodes'];assert basis==list(range(m))+[v for v in D['representatives'].values()if pure[v]]
 B=len(basis);assert B==29;bits=[1<<i for i in range(B)];index={roots[v]:i for i,v in enumerate(basis)};full_index={roots[v]:i for i,v in enumerate(full_basis)}
 assert len(index)==B
 def action(h,c,i):return bits[index[roots[full_basis[full_actions[h][c][full_index[roots[basis[i]]]]]]]]
 products=[[[0]*B for _ in range(B)]for _ in range(K)]
 for h in range(K):
  for i,j in itertools.product(range(B),repeat=2):
   if i==j:q=bits[i]
   elif i<m:q=action(h,i,j)
   elif j<m:q=action(h,j,i)
   elif basis[i]==m+h or basis[j]==m+h:q=bits[index[roots[m+h]]]
   else:
    x,y=types[basis[i]][h],types[basis[j]][h]
    if x[0]==y[0]=='e':q=bits[i]|bits[j]
    elif x[0]==y[0]=='s':q=action(h,x[1],j)|action(h,y[1],i)
    elif x[0]=='e'and y[0]=='s':q=bits[j]|action(h,y[1],i)
    elif y[0]=='e'and x[0]=='s':q=bits[i]|action(h,x[1],j)
    else:raise AssertionError((h,i,j,x,y))
   products[h][i][j]=q
 assert products==H['basis_products']
 def op(h,a,b):
  if h==K:return a|b
  q=0
  for i in members(a):
   for j in members(b):q|=products[h][i][j]
  return q
 values=[]
 for v,t in enumerate(nodes):
  if not pure[v]:q=None
  elif t is None:q=bits[v]if v<m else bits[index[roots[v]]]
  else:q=op(t[0],values[t[1]],values[t[2]])
  values.append(q)
 rules={}
 for lhs,rhs,why in H['rule_events']:
  name=why[0];equiv=False
  if name=='basis-definition':_,i,v=why;assert basis[i]==v;a,b=bits[i],values[v];equiv=True
  elif name=='pure-full-congruence':
   _,x,y=why;assert pure[x]and pure[y]and roots[x]==roots[y]
   a,b=values[x],values[y];equiv=True
  elif name=='choice-bound':_,h,i,j=why;a,b=bits[i]|bits[j],products[h][i][j]
  elif name=='associativity':_,h,i,j,k=why;a,b=op(h,bits[i],op(h,bits[j],bits[k])),op(h,op(h,bits[i],bits[j]),bits[k]);equiv=True
  elif name=='translated-rule':
   _,h,i,x,y=why;assert y&~rules.get(x,0)==0
   a,b=op(h,x,bits[i]),op(h,y,bits[i])
  else:raise AssertionError(why)
  assert rhs and rhs&lhs==0
  assert(lhs==a and rhs&~b==0)or(equiv and lhs==b and rhs&~a==0)
  rules[lhs]=rules.get(lhs,0)|rhs
 assert rules==dict(H['rules'])
 bybit=[[]for _ in range(B)]
 for a,b in rules.items():
  for i in members(a):bybit[i].append((a,b))
 cache={}
 def close(q):
  if q in cache:return cache[q]
  initial=q;todo=q
  while todo:
   bit=todo&-todo;todo^=bit
   for a,b in bybit[bit.bit_length()-1]:
    if a&q==a:
     new=b&~q
     if new:q|=new;todo|=new
  cache[initial]=q;return q
 # Compatibility makes the quotient operations independent of representatives.
 for a,b in rules.items():
  for h in range(K):
   for i in range(B):assert op(h,b,bits[i])&~close(op(h,a,bits[i]))==0
 S=H['join_classes'];pos={s:i for i,s in enumerate(S)};assert len(S)==len(pos)==41
 assert all(close(s)==s for s in S)
 assert all(close(b)in pos for b in bits)
 assert all(close(s|b)in pos for s in S for b in bits)
 tables=[[[pos[close(op(h,a,b))]for b in S]for a in S]for h in range(K+1)]
 constants=[pos[close(bits[i])]for i in range(m)];a0=pos[close(bits[index[roots[m]]])]
 for h in range(K+1):
  for i,j in itertools.product(range(m),repeat=2):assert tables[h][constants[i]][constants[j]]==constants[C[h][i][j]]
 assert len(set(constants))==m and set(tables[0][a0])=={a0}
 reached=set(constants+[a0])
 while True:
  new=reached|{h[x][y]for h in tables for x in reached for y in reached}
  if new==reached:break
  reached=new
 assert len(reached)==41
 evaluations=[]
 for v,t in enumerate(nodes):
  if not pure[v]:value=None
  elif t is None:value=constants[v]if v<m else a0
  else:value=tables[t[0]][evaluations[t[1]]][evaluations[t[2]]]
  if pure[v]:assert value==pos[close(values[v])]
  evaluations.append(value)
 # Verify the explicit auxiliary-absorber interpretation on the actual model.
 folds=[tables[h][constants[h]][a0]for h in range(K)]
 assert folds[0]==a0
 for h in range(K):assert all(tables[h][folds[h]][x]==folds[h]for x in range(41))
 # Native maps certify all laws by an embedding; no native equality was a rule.
 J=[[x if x==y else max(K,x,y)for y in range(K+2)]for x in range(K+2)]
 NH=[[[i if i in(x,y)else J[x][y]for y in range(K+2)]for x in range(K+2)]for i in range(K)]+[J]
 assert len(coordinates)==32
 native_values=[]
 for v,t in enumerate(nodes):
  if not pure[v]:q=None
  elif t is None:q=tuple(c['coefficient_map'][v]if v<m else c['absorber']for c in coordinates)
  else:q=tuple(NH[t[0]][x][y]for x,y in zip(native_values[t[1]],native_values[t[2]]))
  native_values.append(q)
 nv=[native_values[v]for v in basis]
 def native_sum(mask):
  it=iter(members(mask));v=nv[next(it)]
  for i in it:v=tuple(J[x][y]for x,y in zip(v,nv[i]))
  return v
 vectors=[native_sum(s)for s in S];assert vectors==[tuple(v)for v in H['native_vectors']]
 assert len(set(vectors))==41
 for h in range(K+1):
  for x,y in itertools.product(range(41),repeat=2):assert vectors[tables[h][x][y]]==tuple(NH[h][a][b]for a,b in zip(vectors[x],vectors[y]))
 exhaustion_instances=0
 for column,c in enumerate(coordinates):
  phi=c['coefficient_map'];a=c['absorber'];image=set(phi)|{a}
  assert all(phi[t[x][y]]==h[phi[x]][phi[y]]for t,h in zip(C,NH)for x,y in itertools.product(range(m),repeat=2))
  while True:
   new=image|{h[x][y]for h in NH for x in image for y in image}
   if new==image:break
   image=new
  assert sorted(image)==c['generated_image']
  assert all(NH[0][a][x]==a for x in image)
  for h in range(K):
   b=NH[h][phi[h]][a]
   assert b==c['canonical_folds'][h]and all(NH[h][b][x]==b for x in image)
  assert K+1 not in image or any(i not in image for i in range(K))
  for x in image:
   for ys in itertools.product(image,repeat=K):
    value=NH[0][x][ys[0]]
    for h in range(1,K):value=J[value][NH[h][x][ys[h]]]
    assert J[x][value]==value;exhaustion_instances+=1
 column=next(i for i,c in enumerate(coordinates)if c['coefficient_map']==[0,1,2,3]and c['absorber']==0)
 retraction=[constants[v[column]]for v in vectors]
 assert all(retraction[retraction[x]]==retraction[x]for x in range(41))
 assert all(retraction[h[x][y]]==h[retraction[x]][retraction[y]]for h in tables for x,y in itertools.product(range(41),repeat=2))
 supported=[x for x in range(41)if all(h[retraction[x]][x]==x for h in tables)]
 assert len(supported)==18
 assert tables[0][constants[0]][a0]==a0 and tables[K][constants[0]][a0]!=a0
 print('EXACT ONE-ABSORBER MODEL:',len(S),'states;',len(H['rule_events']),'Horn events;',len(rules),'premises;',4*41**2,'derived table entries;',4*41**2*len(coordinates),'native entries',flush=True)
 return dict(states=41,operations=tables,coefficients=constants,absorber=a0,canonical_absorbers=folds,retraction=retraction,supported_states=supported,auxiliary_word_nodes=len(nodes),auxiliary_word_merges=len(D['merges_proof']),horn_events=len(H['rule_events']),horn_premises=len(rules),native_coordinates=len(coordinates),native_operation_entries=4*41**2*len(coordinates),exhaustion_instances=exhaustion_instances)

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--json',type=Path);args=parser.parse_args();start=time.monotonic()
 with gzip.open(Path(__file__).parent/'data'/'core_atomic_three_owner_absorber.json.gz','rt')as f:data=json.load(f)
 D=data['auxiliary_word_proof'];H=data['one_absorber_horn'];C,full_basis,types,actions,roots=replay_words(D)
 result=verify_one_absorber(D,H,C,full_basis,types,actions,roots,data['native_coordinates']);result['seconds']=time.monotonic()-start
 if args.json:args.json.write_text(json.dumps(result,indent=2)+'\n')
 print('PASS',round(result['seconds'],3),'seconds',flush=True)

if __name__=='__main__':main()
