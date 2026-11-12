"""Standalone exact checks for the accompanying mathematical counterexample."""
from itertools import product

def star(x,y,r):
    return 1<<r if x==1<<r or y==1<<r else x|y

def F(a,b,c):
    return star(star(a,b,0),star(a,star(b,c,1),1),2)

# Antitone predicates on the two other-variable atom sets, truth-table masks.
PRED=(1,3,5,7,15)
TYPES=tuple(product(PRED,repeat=3))
LEFT=(5,15,15)       # owner-0 excludes b
PRIME=(15,3,15)      # owner-1 excludes c
RIGHT=(15,1,15)      # owner-1 excludes b and c

def below(t,u):
    return all(x|y==y for x,y in zip(t,u))

def maximal(ts):
    return {t for t in ts if not any(t!=u and below(t,u)for u in ts)}

def factors(t,st):
    return [bool(t[r]>>sum((st[i]==r)<<i for i in range(2))&1)
            for r in range(3)]

def contributes(t,k,st):
    bs=factors(t,st)
    return all(bs[r]for r in range(3)if r!=k)

probes=[]
for k in range(3):
    statuses=[r for r in range(3)if r!=k]+[None]
    for st in product(statuses,repeat=2):
        b,c=[7^(1<<k)if r is None else 1<<r for r in st]
        actual=bool(F(1<<k,b,c)>>k&1)
        expected=(k!=2 or st[0]!=0 or st[1]!=1)
        assert actual==expected,(k,st,actual,expected)
        probes.append((k,st,actual))

def sound(t):
    return all(not contributes(t,k,st)or good for k,st,good in probes)

safe={t for t in TYPES if sound(t)}
assert len(safe)==80
assert maximal(safe)=={LEFT,PRIME}

# Owner-shadow: every minimal avoidance guard of B_r gives a clique label E.
# Every label in E must be a permitted pure-rival source on that same E.
def shadow(t):
    for r in range(3):
        gs=[]
        for g in range(4):
            if not(t[r]>>(3^g)&1)or any(h&g==h for h in gs):
                continue
            gs.append(g)
        for g in gs:
            labels={0}|{i+1 for i in range(2)if g>>i&1}
            for j in labels:
                for k in range(3):
                    if k==r:continue
                    v=[7^(1<<k)if i in labels else 1<<r for i in range(3)]
                    v[j]=1<<k
                    if not F(*v)>>k&1:return False
    return True

shadow_safe={t for t in safe if shadow(t)}
assert maximal(shadow_safe)=={LEFT,RIGHT}
assert not shadow(PRIME)
assert F(6,2,1)==6

# Direct path-factor extraction of the two marked a leaves. A sibling's
# r-singleton test is made with a non-r; singleton profiles depend only on
# which variables are r singletons, so the chosen non-r representative is free.
def L(a,b,c):return star(a,b,0)
def R(a,b,c):return star(a,star(b,c,1),1)
for e in range(4):
    for r in range(3):
        av=7^(1<<r)
        bv=1<<r if e&1 else av
        cv=1<<r if e&2 else av
        left=not (r==0 and bv==1) and not(r==2 and R(av,bv,cv)==4)
        right=not(r==1 and star(bv,cv,1)==2) and not(r==2 and L(av,bv,cv)==4)
        assert left==bool(LEFT[r]>>e&1)
        assert right==bool(RIGHT[r]>>e&1)

# No occurrence with product B0*B1 exactly the observer-2 prime box can avoid
# the impossible owner-1 factor: the other coordinate factor is immaterial.
for t in TYPES:
    exact=all(contributes(t,2,st)==(st[1]!=1)
              for st in product([0,1,None],repeat=2))
    if exact:assert t[0]==15 and t[1]==3

print('PASS: 27 probes; 125 types; sound maxima LEFT/PRIME; shadow maxima LEFT/RIGHT;')
print('      marked path factors; impossible prime-box output (6,2,1) -> 6.')
