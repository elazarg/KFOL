"""
Values of K-player games as Boolean functions of the coalition C (bitmask over 2^K coalitions).
f(C)=1 iff coalition C can force "winner in C" (one-hot) / "some member of C wins" (general).
Choice by player i:   f = (i in C) ? f1|f2 : f1&f2   == maj(x_i, f1, f2)
"""
import itertools, sys, time

def coal_masks(K):
    N = 1 << K
    full = (1 << N) - 1
    # x_j : bit C set iff j in C
    xs = []
    for j in range(K):
        m = 0
        for C in range(N):
            if C >> j & 1: m |= 1 << C
        xs.append(m)
    return N, full, xs

def choice(xi, a, b, full):
    # maj(xi,a,b)
    return (xi & (a | b)) | (~xi & full & (a & b))

def closure(gens, K, ops_first_var=True):
    N, full, xs = coal_masks(K)
    S = set(gens)
    frontier = set(gens)
    while frontier:
        new = set()
        Sl = list(S); Fl = list(frontier)
        for i in range(K):
            xi = xs[i]
            for a in Fl:
                for b in Sl:
                    c = choice(xi, a, b, full)
                    if c not in S: new.add(c)
        S |= new
        frontier = new
    return S

def is_monotone(f, K):
    N = 1 << K
    for C in range(N):
        if f >> C & 1:
            for j in range(K):
                D = C | (1 << j)
                if not (f >> D & 1): return False
    return True

def is_selfdual(f, K):
    N = 1 << K
    for C in range(N):
        if (f >> C & 1) == (f >> ((N - 1) ^ C) & 1): return False
    return True

if __name__ == "__main__":
    print("== Constant-sum (one-hot) games: leaves are dictators x_j ==")
    known = {1: 1, 2: 2, 3: 4, 4: 12, 5: 81, 6: 2646}
    for K in range(1, 7):
        t = time.time()
        N, full, xs = coal_masks(K)
        S = closure(xs, K)
        ok = all(is_monotone(f, K) and is_selfdual(f, K) for f in S)
        print(f"K={K}: |closure|={len(S)}  all monotone+self-dual={ok}  A001206={known.get(K)}  ({time.time()-t:.1f}s)")
        if K <= 4:
            # brute-force count of ALL self-dual monotone functions
            cnt = sum(1 for f in range(1 << N) if is_monotone(f, K) and is_selfdual(f, K))
            print(f"      brute-force #self-dual monotone on {K} vars = {cnt}")
