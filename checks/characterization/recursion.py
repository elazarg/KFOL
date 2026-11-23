"""Check the endpoint recursion P(S,A,B) of core:thm:two-color-pspace against brute force.
P(S,A,B): some pure formula safe on S is true at A and false at B.
Recursion claimed: projection in (A\\B)\\M(S), or exists z in S with
P(S-z,A,B) and (P(S-z,l_z,B) or P(S-z,A,u_z))."""
import sys, random
from functools import lru_cache
from bichain import exact_safe_functions, random_rows

def make_P(n,rows):
    @lru_cache(maxsize=None)
    def P(S,A,B):
        if A & ~B == 0: return False
        marks=0
        for i in range(len(rows)):
            if S>>i&1: marks|=1<<rows[i][2]
        if (A&~B)&~marks: return True
        for i in range(len(rows)):
            if S>>i&1:
                T=S&~(1<<i); l,u,j=rows[i]
                if P(T,A,B) and (P(T,l,B) or P(T,A,u)): return True
        return False
    return P

if __name__=="__main__":
    n=int(sys.argv[1]); r=int(sys.argv[2]); trials=int(sys.argv[3]); rng=random.Random(int(sys.argv[4]))
    N=1<<n; bad=0; pos=0; tot=0
    for t in range(trials):
        rows=random_rows(n,rng.randint(1,r),rng)
        P=make_P(n,rows); full=(1<<len(rows))-1
        safe,_=exact_safe_functions(n,rows)
        for A in range(N):
            for B in range(N):
                ex=any((f>>A&1) and not (f>>B&1) for f in safe)
                rec=P(full,A,B); tot+=1; pos+=ex
                if ex!=rec:
                    bad+=1
                    if bad<=3: print('MISMATCH',rows,A,B,ex,rec)
    print('n',n,'max rows',r,'trials',trials,'pairs',tot,'separable',pos,'mismatches',bad)
