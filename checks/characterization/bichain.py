"""Exact safe-function theory for the four-element bichain with marked cubes.
Values: b=0, n=1, p=2, c=3.  join (c-gate): max.  meet (b-gate): b absorbs, c neutral, else max.
A row z=(l,u,j): c on l, b outside u, p at j, n at other free coordinates.
"""
import itertools, random, numpy as np

def tt_var(n,i):
    # truth table over subsets x (bitmask) : bit x set iff i in x
    t=0
    for x in range(1<<n):
        if x>>i&1: t|=1<<x
    return t

def exact_safe_functions(n,rows):
    """rows: list of (l,u,j) bitmask,bitmask,index. Returns set of truth tables having a safe formula."""
    r=len(rows)
    def var_elem(i):
        vals=[]
        for (l,u,j) in rows:
            if l>>i&1: vals.append(3)
            elif not (u>>i&1): vals.append(0)
            elif i==j: vals.append(2)
            else: vals.append(1)
        return tt_var(n,i), tuple(vals)
    F=[];V=[];seen={}
    def add(f,vals):
        k=(f,vals)
        if k in seen: return
        seen[k]=len(F); F.append(f); V.append(vals)
    for i in range(n): add(*var_elem(i))
    idx=0
    while idx<len(F):
        f=F[idx]; v=np.array(V[idx],dtype=np.int8)
        Fa=np.array(F[:idx+1],dtype=np.int64); Va=np.array(V[:idx+1],dtype=np.int8).reshape(idx+1,r)
        # join
        jf=Fa|f; jv=np.maximum(Va,v[None,:]) if r else Va
        mf=Fa&f
        if r:
            mv=np.where((Va==0)|(v[None,:]==0),0,np.where(Va==3,v[None,:],np.where(v[None,:]==3,Va,np.maximum(Va,v[None,:]))))
        else: mv=Va
        for ff,vv in ((jf,jv),(mf,mv)):
            for a in range(idx+1):
                add(int(ff[a]),tuple(int(t) for t in vv[a]))
        idx+=1
    safe={f for f,v in zip(F,V) if 2 not in v}
    return safe, seen

def exact_preorder(n,rows):
    safe,_=exact_safe_functions(n,rows)
    N=1<<n
    le=[[True]*N for _ in range(N)]
    for f in safe:
        for x in range(N):
            if f>>x&1:
                for y in range(N):
                    if not (f>>y&1): le[x][y]=False
    return le,safe

def transitive(le,N):
    for k in range(N):
        for i in range(N):
            if le[i][k]:
                row_k=le[k]; row_i=le[i]
                for j in range(N):
                    if row_k[j]: row_i[j]=True

def naive_closure(n,rows):
    N=1<<n
    le=[[ (x&~y)==0 for y in range(N)] for x in range(N)]
    byj={}
    for (l,u,j) in rows: byj.setdefault(j,[]).append((l,u))
    changed=True
    while changed:
        changed=False
        for x in range(N):
            for y in range(N):
                if le[x][y]: continue
                d=x&~y; ok=True
                for j in range(n):
                    if d>>j&1:
                        if not any(le[x][u] and le[l][y] for (l,u) in byj.get(j,[])):
                            ok=False;break
                if ok:
                    le[x][y]=True; changed=True
        if changed: transitive(le,N)
    return le

def random_rows(n,r,rng):
    rows=[]
    while len(rows)<r:
        u=rng.randrange(1,1<<n); l=rng.randrange(1<<n)&u
        free=[i for i in range(n) if (u>>i&1) and not (l>>i&1)]
        if not free: continue
        rows.append((l,u,rng.choice(free)))
    return rows

if __name__=="__main__":
    import sys
    n=int(sys.argv[1]); r=int(sys.argv[2]); trials=int(sys.argv[3]); seed=int(sys.argv[4]) if len(sys.argv)>4 else 0
    rng=random.Random(seed)
    N=1<<n; stats={'same':0,'naive_bigger':0,'naive_smaller':0}
    for t in range(trials):
        rows=random_rows(n,rng.randint(1,r),rng)
        ex,safe=exact_preorder(n,rows); nv=naive_closure(n,rows)
        big=[(x,y) for x in range(N) for y in range(N) if nv[x][y] and not ex[x][y]]
        small=[(x,y) for x in range(N) for y in range(N) if ex[x][y] and not nv[x][y]]
        if big:
            stats['naive_bigger']+=1
            if stats['naive_bigger']<=3: print('UNSOUND',rows,big[:5])
        elif small:
            stats['naive_smaller']+=1
            if stats['naive_smaller']<=3: print('INCOMPLETE',rows,small[:5])
        else: stats['same']+=1
    print(n,r,trials,stats)
