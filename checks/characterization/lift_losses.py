"""Minimal losses of the capped baseline (K = 3), computed from all source probes and
compared with the predicted list:
  selector head: all row inputs at a;
  row input x:   for each row z marking x, the code of z with the fixed inputs of z at their atoms;
                 the first-endpoint code with X at c, if x is outside X;
                 the second-endpoint code with the inputs outside Y at b, if x is in Y.
A loss is listed for an observer when it posts no atom of that observer."""
import itertools, random, sys
from lift_check import ch, fold
A,B,Cc=0,1,2
sing=lambda r: frozenset([r])
def build(rows,X,Y):
    nW=len(X); rowsP=[r+['b'] for r in rows]; XP=X+[False]; YP=Y+[False]; nP=nW+1; nZ=len(rows)
    def Cval(sel,w):
        out=set()
        for u in sel: out|=u
        for j in range(nP):
            x=w[j]
            for u in range(nZ): out|=ch(Cc,ch(B,x,sel[u]),sel[u])
            for u1 in range(nZ):
                for u2 in range(nZ):
                    if u1==u2: continue
                    for u3 in range(nZ): out|=ch(B,ch(Cc,ch(Cc,x,sel[u1]),sel[u2]),sel[u3])
            if XP[j]: out|=fold(B,x,sel)
            else:
                for i in range(nP):
                    if XP[i]: out|=fold(B,ch(Cc,x,w[i]),sel)
            if not YP[j]: out|=fold(Cc,x,sel)
            else:
                for i in range(nP):
                    if not YP[i]: out|=fold(Cc,ch(B,x,w[i]),sel)
            for z in range(nZ):
                Kz=lambda y,z=z: fold(B,ch(Cc,y,sel[z]),[sel[u] for u in range(nZ) if u!=z])
                if rowsP[z][j]!='p': out|=Kz(x)
                else:
                    for i in range(nP):
                        if rowsP[z][i]=='b': out|=Kz(ch(B,x,w[i]))
                        if rowsP[z][i]=='c': out|=Kz(ch(Cc,x,w[i]))
        return frozenset(out)
    def F(v):
        sel=v[:nZ]; w=v[nZ:]
        return sing(A) if all(x==sing(A) for x in w) else Cval(sel,w)
    return F,nZ,nP,rowsP,XP,YP
def run(rng,nW,nZ0):
    rows=[[rng.choice('bcpn') for _ in range(nW)] for _ in range(nZ0)]+[['n']*nW,['n']*nW]
    X=[rng.random()<0.5 for _ in range(nW)]; Y=[rng.random()<0.5 for _ in range(nW)]
    F,nZ,nP,rowsP,XP,YP=build(rows,X,Y); n=nZ+nP
    for k in range(3):
        others=[r for r in range(3) if r!=k]
        amb=frozenset(others)
        for j in range(n):
            rest=[i for i in range(n) if i!=j]
            zeros=[]
            for st in itertools.product([None]+others,repeat=len(rest)):
                v=[None]*n; v[j]=sing(k)
                for i,s in zip(rest,st): v[i]=amb if s is None else sing(s)
                if k not in F(v): zeros.append(frozenset((i,s) for i,s in zip(rest,st) if s is not None))
            mins={z for z in zeros if not any(y<z for y in zeros)}
            pred=set()
            if j<nZ: pred.add(frozenset((nZ+i,A) for i in range(nP)))
            else:
                x=j-nZ
                for z in range(nZ):
                    if rowsP[z][x]=='p':
                        pred.add(frozenset([(u,B if u==z else Cc) for u in range(nZ)]+
                            [(nZ+i,B if rowsP[z][i]=='b' else Cc) for i in range(nP) if rowsP[z][i] in 'bc']))
                if not XP[x]: pred.add(frozenset([(u,Cc) for u in range(nZ)]+[(nZ+i,Cc) for i in range(nP) if XP[i]]))
                if YP[x]: pred.add(frozenset([(u,B) for u in range(nZ)]+[(nZ+i,B) for i in range(nP) if not YP[i]]))
            pred={z for z in pred if all(s!=k for (_,s) in z)}
            pred={z for z in pred if not any(y<z for y in pred)}
            assert mins==pred,(rows,X,Y,k,j,sorted(map(sorted,mins)),sorted(map(sorted,pred)))
    return True
if __name__=="__main__":
    rng=random.Random(int(sys.argv[1])); cnt=0
    for it in range(int(sys.argv[2])):
        run(rng,rng.choice([1,2,3]),rng.choice([0,1,2])); cnt+=1
    print('instances',cnt,'minimal losses agree with the predicted list at every source and observer')
