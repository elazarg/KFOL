"""Check the capped-baseline construction for a generic row instance.
Roles 0=a, 1=b, 2=c (and more).  Inputs: one selector per row, with two unconstrained rows added, and W' = W + pad.
Bichain values: 'b','c','p','n'.  Rows: Z -> W -> value.  Endpoints X, Y subsets of W.
Baseline C is a union of explicit terms; target F = {a} if all W' are {a}, else C.
Checks, for every pure separator found: g <= C pointwise and C *_a g = F; and the
row / endpoint values of C at the coded selector configurations."""
import itertools, random, sys
A,B,Cc=0,1,2
def ch(r,x,y):
    s=frozenset([r])
    return s if (x==s or y==s) else x|y
def fold(r,y,xs):
    for x in xs: y=ch(r,y,x)
    return y
def bjoin(x,y):  # sup: c absorbs, b neutral, p over n
    if 'c' in (x,y): return 'c'
    if x=='b': return y
    if y=='b': return x
    return 'p' if 'p' in (x,y) else 'n'
def bmeet(x,y):
    if 'b' in (x,y): return 'b'
    if x=='c': return y
    if y=='c': return x
    return 'p' if 'p' in (x,y) else 'n'
def pure_terms(nW,depth):
    terms=[('v',i) for i in range(nW)]
    for _ in range(depth):
        new=[]
        for s in terms:
            for t in terms:
                new.append(('m',s,t)); new.append(('j',s,t))
        terms=terms+random.sample(new,min(len(new),400))
    return terms
def beval(t,val):
    if t[0]=='v': return val[t[1]]
    x=beval(t[1],val); y=beval(t[2],val)
    return bjoin(x,y) if t[0]=='j' else bmeet(x,y)
def geval(t,w):   # core word: meet -> b-gate, join -> c-gate
    if t[0]=='v': return w[t[1]]
    x=geval(t[1],w); y=geval(t[2],w)
    return ch(Cc,x,y) if t[0]=='j' else ch(B,x,y)

def check(K,nW,nZ,rng,samples):
    rows0=[[rng.choice('bcpn') for _ in range(nW)] for _ in range(nZ)]
    rows=rows0+[['n']*nW,['n']*nW]      # two unconstrained rows keep the codes distinct
    nZ=nZ+2
    X=[rng.random()<0.5 for _ in range(nW)]; Y=[rng.random()<0.5 for _ in range(nW)]
    # pad input index nW: value b on rows, outside X and Y
    rowsP=[r+['b'] for r in rows]; XP=X+[False]; YP=Y+[False]; nP=nW+1
    nJ=nZ
    sing=lambda r: frozenset([r])
    def Cval(sel,w):
        out=set()
        for u in sel: out|=u
        for j in range(nP):
            x=w[j]
            for u in range(nJ):                                   # Q family
                out|=ch(Cc,ch(B,x,sel[u]),sel[u])
            for u1 in range(nJ):                                  # U2 family
                for u2 in range(nJ):
                    if u1==u2: continue
                    for u3 in range(nJ):
                        if u3 in (u1,u2): continue
                        out|=ch(B,ch(Cc,ch(Cc,x,sel[u1]),sel[u2]),sel[u3])
            KX=lambda y: fold(B,y,sel)
            KY=lambda y: fold(Cc,y,sel)
            if XP[j]: out|=KX(x)
            else:
                for i in range(nP):
                    if XP[i]: out|=KX(ch(Cc,x,w[i]))
            if not YP[j]: out|=KY(x)
            else:
                for i in range(nP):
                    if not YP[i]: out|=KY(ch(B,x,w[i]))
            for z in range(nZ):
                Kz=lambda y,z=z: fold(B,ch(Cc,y,sel[z]),[sel[u] for u in range(nJ) if u!=z])
                if rowsP[z][j]!='p': out|=Kz(x)
                else:
                    for i in range(nP):
                        if rowsP[z][i]=='b': out|=Kz(ch(B,x,w[i]))
                        if rowsP[z][i]=='c': out|=Kz(ch(Cc,x,w[i]))
        return frozenset(out)
    conv={'b':sing(B),'c':sing(Cc),'p':sing(A),'n':frozenset([B,Cc])}
    onehot=lambda z:[sing(B) if u==z else sing(Cc) for u in range(nJ)]
    # coded values
    for z in range(nZ):
        assert A not in Cval(onehot(z),[conv[x] for x in rowsP[z]]),('R2',rows,z)
    assert Cval([sing(Cc)]*nJ,[sing(Cc) if XP[i] else sing(B) for i in range(nP)])==sing(Cc),'R3X'
    assert Cval([sing(B)]*nJ,[sing(Cc) if YP[i] else sing(B) for i in range(nP)])==sing(B),'R3Y'
    # separators
    sols=[]
    for t in pure_terms(nW,2):
        if any(beval(t,r)=='p' for r in rows): continue
        if beval(t,['c' if x else 'b' for x in X])!='c': continue
        if beval(t,['c' if y else 'b' for y in Y])!='b': continue
        sols.append(t)
        if len(sols)>=3: break
    vals=[frozenset(s) for m in range(1,K+1) for s in itertools.combinations(range(K),m)]
    special=[sing(r) for r in range(K)]+[frozenset([B,Cc]),frozenset(range(K))]
    for t in sols:
        # pad: t v (pad ^ all W')
        padded=('j',t,('v',nW))
        for i in range(nW): padded=('j',padded[1],('m',padded[2],('v',i)))
        for _ in range(samples):
            mode=rng.random()
            if mode<0.4: sel=[rng.choice([sing(B),sing(Cc)]) for _ in range(nJ)]
            elif mode<0.6: sel=onehot(rng.randrange(nJ))
            elif mode<0.7: sel=[sing(rng.choice([B,Cc]))]*nJ
            else: sel=[rng.choice(vals) for _ in range(nJ)]
            w=[rng.choice(special) if rng.random()<0.7 else rng.choice(vals) for _ in range(nP)]
            if rng.random()<0.3 and nZ:
                z=rng.randrange(nZ); w=[conv[x] if rng.random()<0.8 else rng.choice(vals) for x in rowsP[z]]
            g=geval(padded,w); c=Cval(sel,w)
            assert g<=c,('P1',rows,X,Y,t,sel,w,g,c)
            F=sing(A) if all(x==sing(A) for x in w) else c
            assert ch(A,c,g)==F,('cap',rows,X,Y,t,sel,w)
    return len(sols)
if __name__=="__main__":
    rng=random.Random(int(sys.argv[1])); random.seed(int(sys.argv[1]))
    tot=0;solv=0
    for it in range(int(sys.argv[2])):
        K=rng.choice([3,4]); nW=rng.choice([2,3]); nZ=rng.choice([0,1,2])
        s=check(K,nW,nZ,rng,400); tot+=1; solv+= s>0
    print('instances',tot,'with a separator',solv,'all checks passed')
