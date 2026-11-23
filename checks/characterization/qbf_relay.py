"""A simpler reduction from QBF truth to the endpoint game, with one relay per stage.
Left vertices: start, br(i,s) for stages i=1..n, cl(c).  Right: start, relay(i), res(i,s).
Labels (rectangles I x J):
  ch(i,s): {br(i-1,*)} x {relay(i-1)}   marked by br(i,s) (existential) ; universal: both br(i,*) mark ch(i,True)
  rl(i)  : {br(i,*)}   x {relay(i-1)}   marked by relay(i)
  perm(i,s): {br(i,s)} x {res(i,s)}     unmarked
  lit(i,s): {cl(c): (i,s) in clause c} x {relay(n)}   marked by res(i,s)
  kap    : {br(n,*)}   x {relay(n)}     marked by every cl(c)
br(0,*) and relay(0) are the start vertices."""
import sys, random
from qbf_reduction import solve, qbf_true

def reduce_relay(prefix,clauses):
    n=len(prefix)
    labels={}
    def lab(name,I,J):
        labels[name]=(set(I),set(J))
    L=lambda i:[('br',i,True),('br',i,False)] if i>0 else [('startL',)]
    R=lambda i:('relay',i) if i>0 else ('startR',)
    mark={}
    for i in range(1,n+1):
        q=prefix[i-1][0]
        lab(('ch',i,True),L(i-1),[R(i-1)])
        if q=='E':
            lab(('ch',i,False),L(i-1),[R(i-1)])
            mark[('br',i,True)]=('ch',i,True); mark[('br',i,False)]=('ch',i,False)
        else:
            mark[('br',i,True)]=('ch',i,True); mark[('br',i,False)]=('ch',i,True)
        lab(('rl',i),L(i),[R(i-1)]); mark[('relay',i)]=('rl',i)
        for s in (True,False):
            lab(('perm',i,s),[('br',i,s)],[('res',i,s)])
            lab(('lit',i,s),[('cl',c) for c,clz in enumerate(clauses) if (i-1,s) in clz],[R(n)])
            mark[('res',i,s)]=('lit',i,s)
    lab(('kap',),L(n),[R(n)])
    for c in range(len(clauses)): mark[('cl',c)]=('kap',)
    names=list(labels); idx={e:k for k,e in enumerate(names)}; full=(1<<len(names))-1
    left=lambda v: v[0] in ('br','cl','startL')
    low=lambda v: sum(1<<idx[e] for e in names if v in labels[e][0])
    up=lambda v: full & ~sum(1<<idx[e] for e in names if v in labels[e][1])
    rows=[]
    for v,e in mark.items():
        rows.append((low(v),full,idx[e]) if left(v) else (0,up(v),idx[e]))
        l,u,j=rows[-1]; assert (u>>j&1) and not (l>>j&1),(v,e)
    return len(names),rows,low(('startL',)),up(('startR',))

if __name__=="__main__":
    nv=int(sys.argv[1]); nc=int(sys.argv[2]); trials=int(sys.argv[3]); rng=random.Random(int(sys.argv[4]))
    agree=0; tr=0
    for t in range(trials):
        k=rng.randint(1,nv)
        prefix=[(rng.choice('EA'),v) for v in range(k)]
        clauses=[[(rng.randrange(k),rng.random()<0.5) for _ in range(rng.randint(0,3))] for _ in range(rng.randint(0,nc))]
        truth=qbf_true(prefix,clauses)
        nl,rows,X,Y=reduce_relay(prefix,clauses)
        got,m=solve(rows,X,Y); tr+=truth
        if got==truth: agree+=1
        else: print('MISMATCH',prefix,clauses,truth,got)
    print('trials',trials,'agree',agree,'true',tr)
