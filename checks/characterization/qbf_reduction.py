"""Test the rectangle reduction of core:thm:two-color-pspace: QBF truth <=> P(Z,X,Y).
Vertices are left/right; a label e has a rectangle I_e x J_e; a left row z has
l_z={e: z in I_e}, u_z=V; a right row z has l_z=empty, u_z=V minus {e: z in J_e}."""
import sys, random, itertools
sys.setrecursionlimit(100000)

class Build:
    def __init__(s):
        s.side={}; s.I=[]; s.J=[]; s.mark={}; s.nv=0
    def vertex(s,side):
        v=s.nv; s.nv+=1; s.side[v]=side; return v
    def label(s,verts_a,verts_b):
        # rectangle between two vertex sets on opposite sides
        A=set(verts_a); B=set(verts_b)
        sa={s.side[v] for v in A}; sb={s.side[v] for v in B}
        assert len(sa)==1 and len(sb)==1 and sa!=sb
        if sa=={'L'}: s.I.append(A); s.J.append(B)
        else: s.I.append(B); s.J.append(A)
        return len(s.I)-1
    def opp(s,v): return 'R' if s.side[v]=='L' else 'L'

def reduce_qbf(prefix,clauses):
    """prefix: list of ('E'|'A', var); clauses: list of lists of (var, sign)."""
    b=Build()
    L0=b.vertex('L'); R0=b.vertex('R')
    v2=b.vertex('L')
    e0=b.label([L0],[R0]); b.mark[v2]=e0
    A,B=R0,v2
    branch={}
    for q,var in prefix:
        T=b.vertex(b.side[A]); F=b.vertex(b.side[A])
        if q=='E':
            b.mark[T]=b.label([A],[B]); b.mark[F]=b.label([A],[B])
        else:
            e=b.label([A],[B]); b.mark[T]=e; b.mark[F]=e
        W=b.vertex(b.side[B]); b.mark[W]=b.label([T,F],[B])
        D=b.vertex(b.side[A]); b.mark[D]=b.label([T,F],[W])
        branch[(var,True)]=T; branch[(var,False)]=F
        A,B=W,D
    # occurrence resources
    occ={}   # (clause index, position) -> occurrence label
    res_of={}
    for ci,cl in enumerate(clauses):
        for pi,lit in enumerate(cl):
            beta=branch[lit]
            rho=b.vertex(b.opp(beta)); res_of.setdefault(beta,[]).append(rho)
            occ[(ci,pi)]=rho
    for beta,rs in res_of.items():
        b.label([beta],rs)            # permanently unmarked label
    occlabel={}
    def clause_tree(A,B,idxs):
        if len(idxs)>1:
            h=len(idxs)//2
            C1=b.vertex(b.side[A]); C2=b.vertex(b.side[A])
            e=b.label([A],[B]); b.mark[C1]=e; b.mark[C2]=e
            clause_tree(B,C1,idxs[:h]); clause_tree(B,C2,idxs[h:])
        else:
            ci=idxs[0]; cl=clauses[ci]
            s=b.vertex(b.side[A]); b.mark[s]=b.label([A],[B])
            a_,b_=B,s
            for pi in range(len(cl)):
                # test edge (a_,b_) carries the occurrence label, marked by its resource row
                o=b.label([a_],[b_]); b.mark[occ[(ci,pi)]]=o
                if pi<len(cl)-1:
                    s2=b.vertex(b.side[a_]); b.mark[s2]=b.label([a_],[b_])   # control on test edge
                    s3=b.vertex(b.side[b_]); b.mark[s3]=b.label([b_],[s2])   # separator edge
                    a_,b_=s2,s3
    clause_tree(A,B,list(range(len(clauses))))
    nl=len(b.I)
    full=(1<<nl)-1
    def low(v): return sum(1<<e for e in range(nl) if v in b.I[e])
    def up(v): return full & ~sum(1<<e for e in range(nl) if v in b.J[e])
    rows=[]
    for v,e in b.mark.items():
        if b.side[v]=='L': rows.append((low(v),full,e))
        else: rows.append((0,up(v),e))
        l,u,j=rows[-1]; assert (u>>j&1) and not (l>>j&1)
    X=low(L0); Y=up(R0)
    return nl,rows,X,Y

def solve(rows,X,Y):
    memo={}
    R=len(rows)
    def P(S,A,B):
        d=A&~B
        if d==0: return False
        k=(S,A,B)
        if k in memo: return memo[k]
        marks=0
        for i in range(R):
            if S>>i&1: marks|=1<<rows[i][2]
        if d&~marks: memo[k]=True; return True
        res=False
        for i in range(R):
            if S>>i&1:
                l,u,j=rows[i]; T=S&~(1<<i)
                if (P(T,l,B) or P(T,A,u)) and P(T,A,B): res=True; break
        memo[k]=res; return res
    r=P((1<<R)-1,X,Y)
    return r,len(memo)

def qbf_true(prefix,clauses,assign=None,i=0):
    assign=assign or {}
    if i==len(prefix):
        return all(any(assign[v]==s for v,s in cl) for cl in clauses)
    q,var=prefix[i]
    vals=[qbf_true(prefix,clauses,{**assign,var:b_},i+1) for b_ in (True,False)]
    return any(vals) if q=='E' else all(vals)

if __name__=="__main__":
    nv=int(sys.argv[1]); nc=int(sys.argv[2]); trials=int(sys.argv[3]); rng=random.Random(int(sys.argv[4]))
    agree=0; tr=0; maxmemo=0
    for t in range(trials):
        k=rng.randint(1,nv)
        prefix=[(rng.choice('EA'),v) for v in range(k)]
        clauses=[[(rng.randrange(k),rng.random()<0.5) for _ in range(rng.randint(1,2))] for _ in range(rng.randint(1,nc))]
        truth=qbf_true(prefix,clauses)
        nl,rows,X,Y=reduce_qbf(prefix,clauses)
        got,m=solve(rows,X,Y); maxmemo=max(maxmemo,m)
        tr+=truth
        if got==truth: agree+=1
        else: print('MISMATCH',prefix,clauses,'truth',truth,'game',got,'labels',nl,'rows',len(rows))
    print('trials',trials,'agree',agree,'true instances',tr,'max memo',maxmemo)
