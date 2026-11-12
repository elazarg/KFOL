"""Six-bit closed invariant proving no common lower free extension for U0,U1."""
from itertools import product

def permitted(s):
    a,g,b,d,x,y=s
    return ((not a or x) and not(g and b) and (not b or not x)
            and (not d or not x) and (g or x or y))

def gate(s,t,h):
    a,g,b,d,x,y=s;A,G,B,D,X,Y=t
    aa=a|A if h==0 else a&A
    gg=g|G if h==2 else g&G
    bb=b|B if h==1 else b&B
    dd=d|D if h==2 else d&D
    xx=(x|X)if h==0 else((x and not B)or(X and not b))if h==1 else((x and not D)or(X and not d))
    yy=(y|Y)if h==1 else((y and not A)or(Y and not a))if h==0 else((y and not G)or(Y and not g))
    return tuple(map(int,(aa,gg,bb,dd,xx,yy)))

S={s for s in product(range(2),repeat=6)if permitted(s)}
assert len(S)==16
leaf_a=(1,1,0,0,1,0);leaf_b=(0,0,1,1,0,1)
assert leaf_a in S and leaf_b in S
for s in S:
    for t in S:
        for h in range(3):assert gate(s,t,h)in S
for s in S:
    if not s[1]:assert s[4]or s[5]
u0=gate(gate(leaf_a,leaf_b,1),gate(leaf_a,leaf_b,2),0)
u1=gate(gate(leaf_a,leaf_b,0),gate(leaf_a,leaf_b,2),1)
assert u0[1]==u1[1]==0
assert u0[4]==0 and u1[5]==0
assert u0[5]==1 and u1[4]==1
print('PASS: 16 states; 768 gate checks; leaves; union U0/U1 incomparable with no common lower extension.')
