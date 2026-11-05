"""Audit the canonical absorber functor on its three-element coefficient generator.

Products are computed from the proved coefficient and fork formulas and then
normalized. Native observer values check them independently; they do not define
the operation table. The unary table used for constant interactions is pinned
by the previously proved pointed unary completeness theorem.
"""
from itertools import product
import argparse,time,pickle
parser=argparse.ArgumentParser(description="Audit the K=3 canonical one-owner absorber functor on the three-state generator.")
parser.add_argument("--artifact", help="Optional path for the carrier pickle")
args=parser.parse_args()
K=3;r=0
J=lambda a,b:a if a==b else max(K,a,b)
H=lambda h,a,b:h if h in (a,b) else J(a,b)
CJ=lambda a,b:max(a,b)
CF=lambda a,b:0 if 0 in (a,b) else max(a,b)
ch=lambda h,a,b:CF(a,b) if h==r else CJ(a,b)
coords=[]
for mask in range(8):
 vals=[i for i in range(K) if mask>>i&1]+[3,4]
 for phi in product(vals,repeat=3):
  if all(phi[CJ(a,b)]==J(phi[a],phi[b]) and phi[CF(a,b)]==H(0,phi[a],phi[b]) and all(phi[CJ(a,b)]==H(h,phi[a],phi[b]) for h in (1,2)) for a,b in product(range(3),repeat=2)):
   coords.append((mask,phi))
join=lambda a,b:tuple(J(x,y) for x,y in zip(a,b))
choice=lambda h,a,b:tuple(H(h,x,y) for x,y in zip(a,b))
C=[tuple(phi[c] for _,phi in coords) for c in range(3)]
A=[tuple(i if mask>>i&1 else 4 for mask,_ in coords) for i in range(K)]
E={}
for c,j,i in product(range(3),range(K),range(K)):
 z=join(C[c],A[i])
 for h in range(K):
  if h!=j:z=choice(h,C[c],z)
 E[j,i,c]=z
AC={}
for mask in range(1,8):
 vs=[A[i] for i in range(K) if mask>>i&1];z=vs[0]
 for v in vs[1:]:z=join(z,v)
 AC[mask]=z
# Atom entries are C(c), E(row,column,c), A(mask).
def norm(atoms):
 cm=0;coeff=[];ee=[]
 for a in atoms:
  if a[0]=='A':cm|=a[1]
  elif a[0]=='C':coeff.append(a[1])
  else:ee.append(a[1:]);coeff.append(a[3])
 if not coeff:return ('A',cm)
 c=max(coeff)
 for i in range(K):
  if cm>>i&1:
   for j in range(K):ee.append((j,i,c))
 cols=[]
 for i in range(K):
  entries=[(j,d) for j,k,d in ee if k==i]
  if not entries:cols.append((0,-1));continue
  rows=sum(1<<j for j in set(j for j,d in entries if j!=i))
  if not rows:rows=1<<i
  if i==r or any(j==r for j,d in entries):d=c
  else:d=max(CF(c,d) for j,d in entries)
  cols.append((rows,d))
 return ('N',c,tuple(cols))
def expand(t):
 if t[0]=='A':return [t]
 ans=[('C',t[1])]
 for i,(mask,d) in enumerate(t[2]):
  for j in range(K):
   if mask>>j&1:ans.append(('E',j,i,d))
 return ans
def value(t):
 vals=[]
 for a in expand(t):
  if a[0]=='A':vals.append(AC[a[1]])
  elif a[0]=='C':vals.append(C[a[1]])
  else:vals.append(E[a[1:]])
 z=vals[0]
 for v in vals[1:]:z=join(z,v)
 return z
forms=[('A',mask) for mask in range(1,8)]
for c in range(3):
 adm=[d for d in range(3) if CJ(c,d)==c and CF(c,d)==d]
 choices=[]
 for i in range(K):
  masks=[0,1<<i]+[s for s in range(1,8) if not s>>i&1]
  col=[]
  for mask in masks:
   ds=[-1] if not mask else [c] if i==r or mask>>r&1 else adm
   col += [(mask,d) for d in ds]
  choices.append(col)
 forms.extend(('N',c,cols) for cols in product(*choices))
vals=[value(t) for t in forms]
assert len(set(forms))==len(forms)==622
assert len(set(vals))==622
for t in forms:assert norm(expand(t))==t
print('canonical forms/separation/idempotent normalizer',len(forms),flush=True)
# Unary normal form table, using total coefficient beta; constant coefficient
# observers among coords already jointly separate unary pointed forms.
unary=[]
colchoices=[]
for i in range(K):colchoices.append([0,1<<i]+[s for s in range(1,8) if not s>>i&1])
for masks in product(*colchoices):unary.append(('N',0,tuple((mask,0 if mask else -1) for mask in masks)))
unary += [('A',mask) for mask in range(1,8)]
# Evaluate unary forms on ALL native values under every observer mask.
ucoords=[(mask,x) for mask in range(8) for x in [i for i in range(K) if mask>>i&1]+[3,4]]
def ueval(t):
 ans=[]
 for mask,x in ucoords:
  av=[i if mask>>i&1 else 4 for i in range(K)]
  if t[0]=='A':
   z=None
   for i in range(K):
    if t[1]>>i&1:z=av[i] if z is None else J(z,av[i])
  else:
   z=x
   for i,(rows,_) in enumerate(t[2]):
    for j in range(K):
     if rows>>j&1:
      e=J(x,av[i])
      for h in range(K):
       if h!=j:e=H(h,x,e)
      z=J(z,e)
  ans.append(z)
 return tuple(ans)
udict={ueval(t):t for t in unary};assert len(udict)==132
constaction={}
for h,mask in product(range(K),range(1,8)):
 av=ueval(('A',mask))
 for j,i in [(-1,-1)]+list(product(range(K),repeat=2)):
  t=('N',0,tuple(((1<<j,0) if k==i else (0,-1)) for k in range(K))) if j>=0 else ('N',0,((0,-1),)*K)
  uv=ueval(t)
  constaction[h,mask,j,i]=udict[tuple(H(h,a,b) for a,b in zip(av,uv))]
def replace_index(t,c):
 return [a if a[0]=='A' else ('C',c) if a[0]=='C' else ('E',a[1],a[2],c) for a in expand(t)]
def coefbasis(h,c,e):
 _,j,i,d=e
 if h!=r:return [('C',c),('E',j if j!=h else i,i,d)]
 if j!=r or i==r:return [('E',j,i,CF(c,d))]
 return [('E',i,i,c),('C',CF(c,d))]
def atomic(h,a,b):
 if a[0]=='A' or b[0]=='A':
  if a[0]!='A':a,b=b,a
  if b[0]=='A':return [('A',1<<h if a[1]==1<<h or b[1]==1<<h else a[1]|b[1])]
  if b[0]=='C':return replace_index(constaction[h,a[1],-1,-1],b[1])
  return replace_index(constaction[h,a[1],b[1],b[2]],b[3])
 if a[0]=='C' or b[0]=='C':
  if a[0]!='C':a,b=b,a
  if b[0]=='C':return [('C',ch(h,a[1],b[1]))]
  return coefbasis(h,a[1],b)
 # Two basis entries: row=owner offdiagonal means extensive; otherwise support.
 ae=a[1]==h and a[2]!=h;be=b[1]==h and b[2]!=h
 if ae and be:return [a,b]
 if ae:return [b]+coefbasis(h,b[3],a)
 if be:return [a]+coefbasis(h,a[3],b)
 return coefbasis(h,a[3],b)+coefbasis(h,b[3],a)
expanded=[expand(t) for t in forms]
start=time.monotonic();checked=0
for op in range(-1,K):
 for ai,a in enumerate(forms):
  for bi in range(ai+1):
   b=forms[bi]
   raw=expanded[ai]+expanded[bi] if op==-1 else [v for x in expanded[ai] for y in expanded[bi] for v in atomic(op,x,y)]
   out=norm(raw)
   expected=join(vals[ai],vals[bi]) if op==-1 else choice(op,vals[ai],vals[bi])
   assert value(out)==expected,(op,a,b,out)
   checked+=1
 print('op',op,'passed',checked,'seconds',round(time.monotonic()-start,2),flush=True)
print('PASS all canonical products',checked,flush=True)
if args.artifact:
 with open(args.artifact,'wb') as out:pickle.dump({'forms':forms,'values':vals,'coords':coords},out)
