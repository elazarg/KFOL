"""Independent closed-certificate check for binary free polarized semantics."""
import json
import re
from pathlib import Path

ROLES=range(3)
RIVALS={k:[r for r in ROLES if r!=k]for k in ROLES}
BLOCK={(k,r):sum((not(e>>RIVALS[k].index(r)&1))<<e for e in range(4))
       for k in ROLES for r in RIVALS[k]}
A=((10,10,10),(15,15,15,0,0,0))
B=((12,12,12),(0,0,0,15,15,15))

def star(s,t,r):
    p,c=s;q,d=t;out=[]
    for j in range(2):
        other_singleton=2 if j==0 else 1
        for k in ROLES:
            left=c[3*j+k];right=d[3*j+k]
            if k!=r:
                if q[r]>>other_singleton&1:left&=BLOCK[k,r]
                if p[r]>>other_singleton&1:right&=BLOCK[k,r]
            out.append(left|right)
    return (tuple(p[h]|q[h]if h==r else p[h]&q[h]for h in ROLES),tuple(out))

def parse(text):
    tokens=re.findall(r'[ab()]|\*[012]',text);cursor=0
    def read():
        nonlocal cursor
        tok=tokens[cursor];cursor+=1
        if tok=='a':return A
        if tok=='b':return B
        assert tok=='('
        left=read();op=tokens[cursor];cursor+=1
        right=read();assert tokens[cursor]==')';cursor+=1
        return star(left,right,int(op[1]))
    out=read();assert cursor==len(tokens)
    return out

path=Path(__file__).with_name('free-polarization-binary.json')
data=json.loads(path.read_text())
records=[(tuple(p),tuple(c))for p,c in data['states']]
S=set(records)
assert len(S)==43 and A in S and B in S
for state,term in zip(records,data['syntax']):assert parse(term)==state
for s in S:
    for t in S:
        for r in ROLES:assert star(s,t,r)in S
union={s for s in S if s[0]==(8,8,8)}
assert len(union)==18
for p,c in union:
    assert set(c)<={7,15}
    zeros={(j,k)for j in range(2)for k in ROLES if c[3*j+k]==7}
    assert (len({j for j,k in zeros})<=1 or len({k for j,k in zeros})<=1)
assert ((8,8,8),(7,7,7,7,7,7))not in S
assert ((8,8,8),(15,15,15,15,15,15))in S
# The three simplest union realizers have pairwise incomparable lower bounds;
# a common lower bound would have to be the excluded all-7 record.
for k in ROLES:
    r,s=RIVALS[k]
    u=star(star(A,B,r),star(A,B,s),k)
    assert u[0]==(8,8,8)
    assert u[1]==tuple(7 if h==k else 15 for j in range(2)for h in ROLES)
# A compact necessary persistence clause, useful independently of the count:
# e_(a,k) OR e_(b,l) OR (f_r({a}) AND f_r({b})), k,l,r distinct.
for p,c in S:
    for k in ROLES:
        for l in ROLES:
            if l==k:continue
            r=3-k-l
            assert (c[k]>>3&1)or(c[3+l]>>3&1)or((p[r]>>1&1)and(p[r]>>2&1))
print('PASS: 43 witnessed records, closed under all three gates; exactly 18 union extensions;')
print('      all-minimum completion excluded; maximum attained; 6 compact persistence clauses.')
