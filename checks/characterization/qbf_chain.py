"""The reduction verified in Lean, with a chain of binary clause splits so that every
label is marked by at most two rows.  Left vertices br(i,s) and cl(c); right vertices
relay(i) and res(i,s).  br(0,*) and relay(0) are the start; stages 1..n are quantifiers and
br(n+c+1,True), relay(n+c+1) continue past clause c.  Labels and rectangles:
  ch(i,s): br(i-1,*) x relay(i-1), i<=n        marked by br(i,s), or by both branches if universal
  rl(i)  : br(i,*) x relay(i-1)                marked by relay(i)
  perm(i,s): br(i,s) x res(i,s)                unmarked
  lit(i,s): {cl(c): (i,s) in clause c} x {relay(k): k>=n}   marked by res(i,s)
  kap(c) : br(n+c,*) x relay(n+c)              marked by cl(c) and by br(n+c+1,True)"""
import sys, random
from qbf_reduction import solve, qbf_true

def reduce_chain(prefix,clauses):
    n=len(prefix); m=len(clauses)
    rowsV=[]
    for i in range(1,n+1): rowsV+= [('br',i,True),('br',i,False),('relay',i),('res',i,True),('res',i,False)]
    for c in range(m):
        rowsV.append(('cl',c))
        if c+1<m: rowsV+= [('br',n+c+1,True),('relay',n+c+1)]
    def inI(v,e):
        if v[0]=='br':
            i=v[1]
            return (e[0]=='ch' and e[1]==i+1) or (e[0]=='rl' and e[1]==i) or \
                   (e[0]=='perm' and e[1]==i and e[2]==v[2]) or (e[0]=='kap' and i==n+e[1])
        if v[0]=='cl': return e[0]=='lit' and (e[1]-1,e[2]) in clauses[v[1]]
        return False
    def inJ(v,e):
        if v[0]=='relay':
            k=v[1]
            return (e[0]=='ch' and e[1]==k+1 and e[1]<=n and (e[2] or prefix[e[1]-1][0]=='E')) or \
                   (e[0]=='rl' and e[1]==k+1) or (e[0]=='lit' and k>=n) or (e[0]=='kap' and k==n+e[1])
        if v[0]=='res': return e[0]=='perm' and e[1]==v[1] and e[2]==v[2]
        return False
    def mark(v):
        if v[0]=='br':
            i=v[1]
            if i<=n: return ('ch',i,v[2] if prefix[i-1][0]=='E' else True)
            return ('kap',i-n-1)
        if v[0]=='relay': return ('rl',v[1])
        if v[0]=='res': return ('lit',v[1],v[2])
        return ('kap',v[1])
    labels=[('ch',i,s) for i in range(1,n+2) for s in (True,False)]+[('rl',i) for i in range(0,n+m+2)]+\
           [('perm',i,s) for i in range(0,n+1) for s in (True,False)]+[('lit',i,s) for i in range(1,n+1) for s in (True,False)]+\
           [('kap',c) for c in range(0,m+1)]
    idx={e:k for k,e in enumerate(labels)}; full=(1<<len(labels))-1
    low=lambda v: sum(1<<idx[e] for e in labels if inI(v,e))
    up=lambda v: full & ~sum(1<<idx[e] for e in labels if inJ(v,e))
    rows=[]; marks={}
    for v in rowsV:
        e=mark(v); marks.setdefault(e,0); marks[e]+=1
        l,u=low(v),up(v); assert (u>>idx[e]&1) and not (l>>idx[e]&1)
        left=v[0] in ('br','cl')
        rows.append((l,full,idx[e]) if left else (0,u,idx[e]))
    assert max(marks.values(),default=0)<=2
    return rows,low(('br',0,True)),up(('relay',0))

if __name__=="__main__":
    nv=int(sys.argv[1]); nc=int(sys.argv[2]); trials=int(sys.argv[3]); rng=random.Random(int(sys.argv[4]))
    agree=0; tr=0
    for t in range(trials):
        k=rng.randint(0,nv)
        prefix=[(rng.choice('EA'),v) for v in range(k)]
        clauses=[[(rng.randrange(k),rng.random()<0.5) for _ in range(rng.randint(0,3))] if k else [] for _ in range(rng.randint(0,nc))]
        truth=qbf_true(prefix,clauses)
        rows,X,Y=reduce_chain(prefix,clauses)
        got,_=solve(rows,X,Y); tr+=truth
        if got==truth: agree+=1
        else: print('MISMATCH',prefix,clauses,truth,got)
    print('trials',trials,'agree',agree,'true',tr)
