"""Independent replay of C11 plus two global absorber presentations.
No native values justify equalities. Named proved schemas are dependencies
on the mathematical Γ+M consequences, including the ordered-profile law.
"""
import json,collections,itertools,time
from pathlib import Path

DATA=Path(__file__).with_name('core_two_owner_pointed_binary.json')

def types_for(h,x,y,C):
 out=[]
 for owner in range(2):
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

def check_coefficient_and_unary_schemas(D):
 # Completeness of the displayed binary/unary normal forms is a proved
 # dependency. These semantic checks determine their reduction tables;
 # they never identify arbitrary terms in the presented binary extension.
 J=[[a if a==b else max(2,a,b)for b in range(4)]for a in range(4)]
 f,g=[[[i if i in(a,b)else J[a][b]for b in range(4)]for a in range(4)]for i in range(2)]
 rows=[]
 for x,y in itertools.product(range(4),repeat=2):
  rows.append([x,y,J[x][y],f[x][y],g[x][y],f[y][J[x][y]],g[y][J[x][y]],g[y][f[x][y]],f[x][J[x][y]],g[x][J[x][y]],g[x][f[x][y]]])
 values=list(zip(*rows));assert len(set(values))==11
 for H,h in zip(D['base_tables'],[f,g,J]):
  assert len(H)==11 and all(len(row)==11 for row in H)
  for x,y in itertools.product(range(11),repeat=2):assert values[H[x][y]]==tuple(h[a][b]for a,b in zip(values[x],values[y]))
 assert D['base_absorbers']==[3,4]
 for h,a in enumerate(D['base_absorbers']):assert set(D['base_tables'][h][a])=={a}
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

def replay_words(D):
 check_coefficient_and_unary_schemas(D)
 C=D['base_tables'];m=len(C[0]);nodes=D['nodes_dag'];parent=[];uses=[];keys=[];base=[];types=[];index=collections.defaultdict(set);unary=D['proved_unary_schema'];counts=collections.Counter()
 split={x:next(((a,b)for a in range(m)for b in range(a+1,m)if C[2][a][b]==x and a!=x and b!=x),None)for x in range(m)}
 def root(x):
  while parent[x]!=x:x=parent[x]
  return x
 def key(h,a,b):
  a,b=root(a),root(b);return(h,min(a,b),max(a,b))
 def declare(v):
  parent.append(v);uses.append(set());keys.append(None)
  if v<m+2:
   assert nodes[v]is None
   base.append(v if v<m else D['base_absorbers'][v-m]);types.append([('s',v),('s',v)]if v<m else([('a',),('e',)]if v==m else[('e',),('a',)]))
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
 def unary_ast(t,x):
  if isinstance(t,str):return {'a':m,'b':m+1,'z':x}[t]
  h,a,b=t;return op(h,unary_ast(a,x),unary_ast(b,x))
 def flat(x):
  x=root(x)
  if x<m and split[x]is not None:return flat(split[x][0])|flat(split[x][1])
  t=nodes[x]
  return flat(t[1])|flat(t[2])if t is not None and t[0]==2 else{x}
 def equation(reason):
  name,v=reason
  if name=='coefficient-table':h,a,b=v;return op(h,a,b),C[h][a][b]
  if name in('generator-absorption','global-absorption'):h,x=v;return op(h,m+h,x),m+h
  if name=='absorber-neutrality':h,x=v;q=op(h,m+1-h,x);return op(2,x,q),q
  if name=='typed-support':h,x,a,k=v;assert k in(h,2);assert ('s',a)in[types[z][h]for z in range(len(parent))if root(z)==root(x)];return op(k,a,x),x
  if name=='typed-linearization':
   h,a,b=v;x,y=types[a][h],types[b][h]
   if x[0]==y[0]=='e':target=op(2,a,b)
   elif x[0]==y[0]=='s':target=op(2,op(h,x[1],b),op(h,y[1],a))
   elif x[0]=='e'and y[0]=='s':target=op(2,b,op(h,y[1],a))
   elif y[0]=='e'and x[0]=='s':target=op(2,a,op(h,x[1],b))
   else:raise AssertionError(reason)
   return op(h,a,b),target
  if name=='join-ACI':
   a,b,atoms=v;assert flat(a)|flat(b)==set().union(*(flat(x)for x in atoms)),('JOIN FLATTEN',v)
   target=atoms[0]
   for z in atoms[1:]:target=op(2,target,z)
   return op(2,a,b),target
  if name=='eager-distribution':h,a,b,c=v;return op(h,a,op(2,b,c)),op(2,op(h,a,b),op(h,a,c))
  if name=='coefficient-distribution':h,c,z,a,b=v;assert C[2][a][b]==c;return op(h,c,z),op(2,op(h,a,z),op(h,b,z))
  if name=='coefficient-composition':h,a,b,z=v;return op(h,a,op(h,b,z)),op(h,C[h][a][b],z)
  if name=='coefficient-commutation':a,z=v;return op(1,a,op(0,a,z)),op(0,a,op(1,a,z))
  if name=='proved-unary-table':h,x,i,j=v;forms=[unary_ast(t,x)for t in unary['form_asts']];return op(h,forms[i],forms[j]),forms[unary['operations'][h][i][j]]
  if name=='proved-sandwich':f,h,x,y,z=v;assert {f,h}=={0,1};r=C[f][x][C[h][x][y]];return op(f,x,op(h,y,op(f,x,z))),op(f,r,op(h,y,z))
  if name=='proved-ordered-profile':f,h,x,y=v;assert {f,h}=={0,1}and C[2][x][y]==y;return op(f,x,op(h,m+f,y)),op(h,m+f,C[f][x][y])
  if name=='coverage':x,y=v;return op(2,op(0,x,y),op(1,x,y)),op(2,x,y)
  if name=='Birkhoff':x,y=v;return op(0,x,op(1,x,y)),op(1,x,op(0,x,y))
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
 basis=list(range(m))+list(D['representatives'].values());ix={root(v):i for i,v in enumerate(basis)};assert len(ix)==67
 actions=[[[ix[root(op(h,c,w))]for w in basis]for c in range(m)]for h in range(2)]
 print('WORD REPLAY',len(nodes),'nodes',len(D['merges_proof']),'merges',len(basis),'basis',flush=True)
 return C,basis,types,actions


def members(q):
 while q:
  b=q&-q;yield b.bit_length()-1;q^=b

def replay_horn(D,H,C,basis,types,actions):
 m=len(C[0]);B=len(basis);bits=[1<<i for i in range(B)];assert H['basis_nodes']==basis
 ix={v:i for i,v in enumerate(basis)};assert m in ix and m+1 in ix
 products=[[[0]*B for _ in range(B)]for _ in range(2)]
 def action(h,c,i):return bits[actions[h][c][i]]
 for h in range(2):
  for i,j in itertools.product(range(B),repeat=2):
   if i==j:q=bits[i]
   elif i<m:q=action(h,i,j)
   elif j<m:q=action(h,j,i)
   elif basis[i]==m+h or basis[j]==m+h:q=bits[ix[m+h]]
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
  if h==2:return a|b
  q=0
  for i in members(a):
   for j in members(b):q|=products[h][i][j]
  return q
 values=[]
 for v,t in enumerate(D['nodes_dag']):
  if t is None:q=bits[v]if v<m else bits[ix[v]]
  else:q=op(t[0],values[t[1]],values[t[2]])
  values.append(q)
 rules={};counts=collections.Counter()
 for lhs,rhs,why in H['rule_events']:
  name=why[0];equiv=False
  if name=='basis-definition':_,i,v=why;assert basis[i]==v;a,b=bits[i],values[v];equiv=True
  elif name=='ground-merge':_,event=why;_,x,y,_=D['merges_proof'][event];a,b=values[x],values[y];equiv=True
  elif name=='choice-bound':_,h,i,j=why;a,b=bits[i]|bits[j],products[h][i][j]
  elif name=='associativity':_,h,i,j,k=why;a,b=op(h,bits[i],op(h,bits[j],bits[k])),op(h,op(h,bits[i],bits[j]),bits[k]);equiv=True
  elif name=='translated-rule':
   _,h,i,x,y=why;assert y&~rules.get(x,0)==0,('UNJUSTIFIED SOURCE',why)
   a,b=op(h,x,bits[i]),op(h,y,bits[i])
  else:raise AssertionError(why)
  assert rhs and rhs&lhs==0
  assert(lhs==a and rhs&~b==0)or(equiv and lhs==b and rhs&~a==0),('INVALID HORN',lhs,rhs,why,a,b)
  rules[lhs]=rules.get(lhs,0)|rhs;counts[name]+=1
 assert rules==dict(H['rules'])
 bybit=[[]for _ in range(B)]
 for a,b in rules.items():
  for i in members(a):bybit[i].append((a,b))
 cache={}
 def close(q):
  if q in cache:return cache[q]
  original=q;todo=q
  while todo:
   bit=todo&-todo;todo^=bit
   for a,b in bybit[bit.bit_length()-1]:
    if a&q==a:
     new=b&~q
     if new:q|=new;todo|=new
  cache[original]=q;return q
 S=H['join_classes'];index={s:i for i,s in enumerate(S)};tables=H['operations']
 assert len(index)==len(S)==221
 assert all(close(s)==s for s in S)
 for h,table in enumerate(tables):
  for i,j in itertools.product(range(len(S)),repeat=2):assert close(op(h,S[i],S[j]))==S[table[i][j]],('TABLE REDUCTION',h,i,j)
 constants=[index[close(bits[i])]for i in range(m)];absorbers=[index[close(bits[ix[m+h]])]for h in range(2)]
 for h in range(3):
  for i,j in itertools.product(range(m),repeat=2):assert tables[h][constants[i]][constants[j]]==constants[C[h][i][j]]
 for h in range(2):assert all(tables[h][absorbers[h]][i]==absorbers[h]for i in range(len(S)))
 # Every original DAG node evaluates to its derived semilattice form.
 evaluations=[]
 for v,t in enumerate(D['nodes_dag']):
  value=constants[v]if v<m else absorbers[v-m]if t is None else tables[t[0]][evaluations[t[1]]][evaluations[t[2]]]
  assert value==index[close(values[v])],('DAG REDUCTION',v);evaluations.append(value)
 for i,v in enumerate(basis):assert evaluations[v]==index[close(bits[i])]
 reached=set(constants[:2]+absorbers)
 while True:
  new=reached|{table[a][b]for table in tables for a in reached for b in reached}
  if new==reached:break
  reached=new
 assert len(reached)==len(S)
 print('HORN REPLAY',len(H['rule_events']),'events',len(rules),'premises',3*len(S)**2,'derived table entries',flush=True)
 return tables,constants,absorbers

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

def check_native(tables,maps):
 n=len(tables[0]);J=[[a if a==b else max(2,a,b)for b in range(4)]for a in range(4)]
 native=[[[i if i in(a,b)else J[a][b]for b in range(4)]for a in range(4)]for i in range(2)]+[J]
 for p in maps:
  assert len(p)==n and all(0<=x<4 for x in p)
  for H,h in zip(tables,native):
   for a,b in itertools.product(range(n),repeat=2):assert p[H[a][b]]==h[p[a]][p[b]]
 assert len({tuple(p[a]for p in maps)for a in range(n)})==n
 return 3*n*n*len(maps)

def main():
 start=time.monotonic();data=json.loads(DATA.read_text());D=data['word_proof'];H=data['semilattice_proof'];C,basis,types,actions=replay_words(D)
 tables,constants,absorbers=replay_horn(D,H,C,basis,types,actions)
 print('GROUND AND TABLE REDUCTIONS PASSED',round(time.monotonic()-start,3),flush=True)
 full_laws(tables)
 entries=check_native(tables,data['native_maps'])
 print('EXACT PRESENTATION VERIFIED:',len(tables[0]),'states;',len(data['native_maps']),'native coordinates;',entries,'native operation entries;',round(time.monotonic()-start,3),'seconds',flush=True)

if __name__=='__main__':main()
