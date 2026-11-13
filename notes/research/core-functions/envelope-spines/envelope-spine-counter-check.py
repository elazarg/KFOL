"""Self-contained finite certificate against all max-envelope sibling spines.
No external data, SAT solver, or full-clone enumeration is used.
Winner masks are 1=owner0,2=owner1,4=owner2.
"""
from itertools import product
from functools import reduce
rows=[(2,1,2),(4,2,1),(2,1,1),(1,4,2),(1,2,4)]
forbidden=[0,0,1,1];positive=2
P=[f for f in range(256)if not(f&1)and(f>>7&1)and all(not(f>>s&1)or f>>t&1 for s in range(8)for t in range(8)if s&t==s)]
mins={f:[s for s in range(8)if f>>s&1 and not any(t!=s and t&s==t and f>>t&1 for t in range(8))]for f in P}
def envelope(fs,S,v):
 E=[sum((v[j]==1<<r)<<j for j in range(3))for r in range(3)]
 winners=[r for r in range(3)if fs[r]>>E[r]&1]
 assert len(winners)<=1
 return 1<<winners[0]if winners else reduce(int.__or__,[v[j]for j in range(3)if S>>j&1])
basis={}
for fs in product(P,repeat=3):
 if any(not(a&b&c)for a,b,c in product(*(mins[f]for f in fs))):continue
 dependency=reduce(int.__or__,[s for f in fs for s in mins[f]])
 for S in range(1,8):
  if dependency&~S:continue
  table=tuple(envelope(fs,S,v)for v in rows)
  basis[(fs,S)]=table
B=sorted(set(basis.values()))
assert len(P)==18 and len(basis)==625 and len(B)==100

def op(x,y,r):return 1<<r if x==1<<r or y==1<<r else x|y
def action(x,y,r):return tuple(op(a,b,r)for a,b in zip(x,y))
projections=[tuple(v[j]for v in rows)for j in range(3)]
R=set(projections);queue=list(R);i=0
while i<len(queue):
 for E in B:
  for r in range(3):
   w=action(queue[i],E,r)
   if w not in R:R.add(w);queue.append(w)
 i+=1
assert len(R)==414
# Add the finite unions allowed by the proposed normal form.
spine_count=len(R);queue=list(R);i=0
while i<len(queue):
 for y in queue[:i+1]:
  w=tuple(a|b for a,b in zip(queue[i],y))
  if w not in R:R.add(w);queue.append(w)
 i+=1
assert len(R)==416
# Certificate checks: only inclusion/closure/soundness, not search completeness.
assert all(p in R for p in projections) and all(E in R for E in B)
assert all(tuple(a|b for a,b in zip(x,y))in R for x in R for y in R)
assert all(action(x,E,r)in R for x in R for E in B for r in range(3))
assert all(not(x[-1]>>positive&1)or any(x[i]>>r&1 for i,r in enumerate(forbidden))for x in R)

def counter(v):
 x,y,z=v
 return op(op(op(z,op(y,x,2),2),x,1),op(op(z,x,0),y,1),0)
F=tuple(map(counter,rows));assert F==(2,6,1,5,7)
assert all(not(F[i]>>r&1)for i,r in enumerate(forbidden))and F[-1]>>positive&1
assert F not in R
# The fourth owner also checks the unanimous profile for an unused owner.
for r,profile in enumerate((200,168,128,128)):
 for S in range(8):
  v=tuple((1<<r)if S>>j&1 else 15^(1<<r)for j in range(3))
  assert (counter(v)==1<<r)==bool(profile>>S&1),(r,S,counter(v),profile)
safe=sorted(x for x in R if all(not(x[i]>>r&1)for i,r in enumerate(forbidden)))
print('PASS: 18 monotone profiles; 625 support/profile envelopes; 100 five-row actions; 414 spine tuples; 416 closed union/envelope-action tuples.')
print('Negative-safe tuples:',safe,'; counter:',F)
