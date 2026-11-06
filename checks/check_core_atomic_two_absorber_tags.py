"""Check supported-coefficient absorber tags, prototypes, and the atomic case."""
from itertools import product, permutations

def tag_extension(ops,F,G):
 n=len(F); FG=[F[G[x]]for x in range(n)]
 assert all(F[F[x]]==F[x] and G[G[x]]==G[x] and F[G[x]]==G[F[x]]for x in range(n))
 tags=[(0,x)for x in range(n)]+[(k,None)for k in (1,2,3)]
 tags += [(k,x)for k,im in ((1,G),(2,F),(3,FG))for x in sorted(set(im))]
 idx={t:i for i,t in enumerate(tags)}
 def norm(k,d):
  if d is None:return(k,None)
  return(k,[list(range(n)),G,F,FG][k][d])
 def plus(a,b):
  k,x=a;l,y=b
  z=y if x is None else x if y is None else ops[2][x][y]
  return norm(k|l,z)
 constant=[{(1,1):1,(1,2):1,(1,3):1,(2,2):2,(2,3):3,(3,3):3},
           {(1,1):1,(1,2):2,(1,3):3,(2,2):2,(2,3):2,(3,3):3}]
 def atom(h,a,b):
  k,x=a;l,y=b
  if k and l:return (constant[h][tuple(sorted((k,l)))],None)
  if not k and not l:return (0,ops[h][x][y])
  if not k:k,x=l,x
  else:x=y
  if h==0:
   return (1,None)if k==1 else (0,F[x])if k==2 else norm(1,FG[x])
  return (0,G[x])if k==1 else (2,None)if k==2 else norm(2,FG[x])
 def operation(h,a,b):
  if h==2:return plus(a,b)
  def parts(t):
   k,x=t
   return ([(k,None)]if k else [])+([(0,x)]if x is not None else [])
  out=None
  for x,y in product(parts(a),parts(b)):
   v=atom(h,x,y);out=v if out is None else plus(out,v)
  return out
 tables=[[[idx[operation(h,a,b)]for b in tags]for a in tags]for h in range(3)]
 return tags,tables

def opposite_unitize(ops,unit_owner):
 # U_g adds a g-unit/f-absorber. Owner exchange gives U_f.
 if unit_owner==0:
  ts,H=opposite_unitize([ops[1],ops[0],ops[2]],1)
  return ts,[H[1],H[0],H[2]]
 n=len(ops[0]);tags=[('old',x)for x in range(n)]+[('a',None)]+[('bar',x)for x in range(n)]
 idx={t:i for i,t in enumerate(tags)};f,g,j=ops
 def op(h,a,b):
  ka,x=a;kb,y=b
  if ka=='a' and kb=='a':return('a',None)
  if kb=='a':return op(h,b,a)
  if ka=='a':return('a',None)if h==0 else b if h==1 else ('bar',y)
  if ka=='old' and kb=='old':return('old',ops[h][x][y])
  if ka=='old':return op(h,b,a)
  if kb=='old':
   return ('bar',f[x][y])if h==0 else ('old',j[y][g[x][y]])if h==1 else ('bar',j[x][y])
  return ('bar',f[x][y]if h==0 else j[x][y])
 return tags,[[[idx[op(h,a,b)]for b in tags]for a in tags]for h in range(3)]

def check_iso(H,K,p):
 assert len(set(p))==len(H[0])==len(K[0])
 for h in range(3):
  for x,y in product(range(len(p)),repeat=2):assert p[H[h][x][y]]==K[h][p[x]][p[y]]
 return 3*len(p)**2

def laws(H):
 R=range(len(H[0]));f,g,j=H
 for h in H:
  assert all(h[x][x]==x for x in R)
  assert all(h[x][y]==h[y][x]for x,y in product(R,repeat=2))
  assert all(h[x][h[y][z]]==h[h[x][y]][z]for x,y,z in product(R,repeat=3))
 for h in (f,g):
  assert all(h[x][j[y][z]]==j[h[x][y]][h[x][z]]for x,y,z in product(R,repeat=3))
 assert all(j[f[x][y]][g[x][y]]==j[x][y]and f[x][g[x][y]]==g[x][f[x][y]]for x,y in product(R,repeat=2))
 for h,k in ((f,g),(g,f)):
  assert all(h[x][k[y][h[y][z]]]==h[x][k[y][h[x][h[y][z]]]]for x,y,z in product(R,repeat=3))

def main():
 j=[[x if x==y else 2 for y in range(3)]for x in range(3)]
 f=[[0 if 0 in(x,y)else j[x][y]for y in range(3)]for x in range(3)]
 g=[[1 if 1 in(x,y)else j[x][y]for y in range(3)]for x in range(3)]
 base0=[f,g,j]
 jc=[[max(x,y)for y in range(3)]for x in range(3)]
 fc=[[0 if 0 in(x,y)else max(x,y)for y in range(3)]for x in range(3)]
 basef=[fc,jc,jc];ident=[0,1,2];mark=[0,2,2]
 tags0,H0=tag_extension(base0,ident,ident)
 tagsf,Hf=tag_extension(basef,mark,ident)
 tagsg,Hg=tag_extension([jc,fc,jc],ident,mark)
 assert list(map(len,(tags0,tagsf,tagsg)))==[15,13,13]
 for H in (H0,Hf,Hg):laws(H)
 # P0: exact double unitization.
 inner,I=opposite_unitize(base0,0);outer,O=opposite_unitize(I,1)
 ii={t:i for i,t in enumerate(inner)};oi={t:i for i,t in enumerate(outer)}
 def image0(t):
  k,x=t
  if k==0:return oi[('old',ii[('old',x)])]
  if k==1:return oi[('a',None)]if x is None else oi[('bar',ii[('old',x)])]
  if k==2:return oi[('old',ii[('a',None)])]if x is None else oi[('old',ii[('bar',x)])]
  return oi[('bar',ii[('a',None)])]if x is None else oi[('bar',ii[('bar',x)])]
 entries=check_iso(H0,O,[image0(t)for t in tags0])
 # Stronger supported-coefficient prototype: FULL D2 with F=G=id.
 nj=[[x if x==y else max(2,x,y)for y in range(4)]for x in range(4)]
 nf=[[0 if 0 in(x,y)else nj[x][y]for y in range(4)]for x in range(4)]
 ng=[[1 if 1 in(x,y)else nj[x][y]for y in range(4)]for x in range(4)]
 native=[nf,ng,nj];tagsN,HN=tag_extension(native,list(range(4)),list(range(4)))
 assert len(tagsN)==19; laws(HN)
 inner,I=opposite_unitize(native,0);outer,O=opposite_unitize(I,1)
 ii={t:i for i,t in enumerate(inner)};oi={t:i for i,t in enumerate(outer)}
 full_entries=check_iso(HN,O,[image0(t)for t in tagsN])
 # Nontrivial expanded quotient D2->atomic B2, and its surjective tag lift.
 qi={t:i for i,t in enumerate(tags0)}
 quotient=[qi[(k,None if x is None else min(x,2))]for k,x in tagsN]
 assert set(quotient)==set(range(15))
 for h in range(3):
  for x,y in product(range(19),repeat=2):
   assert quotient[HN[h][x][y]]==H0[h][quotient[x]][quotient[y]]
 full_entries+=3*19**2
 # Pf: extract exactly the known six-state opposite-absorber table;
 # its membership is the prior one-owner theorem, separate from this audit.
 selected=[i for i,(k,x)in enumerate(tagsf)if k in(0,2)]
 si={v:i for i,v in enumerate(selected)}
 S=[[[si[h[x][y]]for y in selected]for x in selected]for h in Hf]
 assert len(S[0])==6; laws(S)
 outer,O=opposite_unitize(S,1);oi={t:i for i,t in enumerate(outer)};ti={t:i for i,t in enumerate(tagsf)}
 def imagef(t):
  k,x=t
  if k in(0,2):return oi[('old',si[ti[t]])]
  if k==1:return oi[('a',None)]if x is None else oi[('bar',si[ti[(0,x)]])]
  return oi[('bar',si[ti[(2,None)]]) ]if x is None else oi[('bar',si[ti[(2,x)]])]
 entries+=check_iso(Hf,O,[imagef(t)for t in tagsf])
 gi={t:i for i,t in enumerate(tagsg)}
 dual=[gi[({0:0,1:2,2:1,3:3}[k],x)]for k,x in tagsf]
 entries+=check_iso([Hf[1],Hf[0],Hf[2]],Hg,dual)
 # Exact flat-atomic coefficient envelope with supported generators at alpha,beta.
 homs=[p for p in product(range(3),repeat=3)if p[2]==2 and all(p[h[x][y]]==h[p[x]][p[y]]for h in base0 for x,y in product(range(3),repeat=2))]
 assert len(homs)==4
 order=lambda p,q:all(j[x][y]==y for x,y in zip(p,q))
 upsets=[U for U in range(1<<len(homs))if all(not(U>>i&1)or not order(homs[i],homs[k])or U>>k&1 for i,k in product(range(len(homs)),repeat=2))]
 Z=[sum(1<<i for i,p in enumerate(homs)if p[d]==2)for d in range(3)]
 env=[(d,U,V)for d in range(3)for U in upsets for V in upsets if U&~(Z[d]&Z[0])==0 and V&~(Z[d]&Z[1])==0]
 ei={v:i for i,v in enumerate(env)};assert len(env)==21
 E=[[[ei[(h[d][e],Z[h[d][e]]&(U|W),Z[h[d][e]]&(V|X))]for e,W,X in env]for d,U,V in env]for h in base0]
 EF=[ei[(d,U,Z[d]&Z[1])]for d,U,V in env];EG=[ei[(d,Z[d]&Z[0],V)]for d,U,V in env]
 assert [len(set(EF)),len(set(EG)),len({EF[EG[x]]for x in range(21)})]==[8,8,3]
 fulltags,full=tag_extension(E,EF,EG);assert len(fulltags)==43; laws(full)
 # Exact internal clamping translations.
 uf=ei[(0,Z[0],0)];ug=ei[(1,0,Z[1])]
 assert EF==E[0][ug]and EG==E[1][uf]
 ti={t:i for i,t in enumerate(fulltags)}
 seed={ti[(0,ei[(d,0,0)])]for d in range(3)}|{ti[(1,None)],ti[(2,None)]}
 while True:
  more=seed|{h[x][y]for h in full for x,y in product(seed,repeat=2)}
  if more==seed:break
  seed=more
 assert len(seed)==43
 observers=[]
 for pos,p in enumerate(homs):
  observers.append((tags0,H0,[p[d]for d,U,V in env]))
  if p[0]==2:
   observers.append((tagsg,Hg,[2 if U>>pos&1 else 0 if p[d]==1 else 1 for d,U,V in env]))
  if p[1]==2:
   observers.append((tagsf,Hf,[2 if V>>pos&1 else 0 if p[d]==0 else 1 for d,U,V in env]))
 lifted=[];native_entries=0
 for tt,HH,mapD in observers:
  tix={t:i for i,t in enumerate(tt)}
  row=[tix[(k,None if d is None else mapD[d])]for k,d in fulltags]
  for h in range(3):
   for x,y in product(range(43),repeat=2):assert row[full[h][x][y]]==HH[h][row[x]][row[y]]
  lifted.append(row);native_entries+=3*43**2
 assert len(set(zip(*lifted)))==43
 print('PASS: 15/13/13 candidate prototypes; exact tag/unitization/duality entries',entries)
 print('PASS: flat atomic envelope21; clamp images8/8/3; exact tag algebra43; lifted observer entries',native_entries)
 print('PASS: full19 prototype double unitization and nontrivial19-to15 tag quotient; entries',full_entries)

if __name__=='__main__':main()
