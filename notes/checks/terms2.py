# Packed representation: for K players, coordinates = non-constant colourings C; each holds an 8-bit truth table over (a,b,c).
import sys, time
K = int(sys.argv[1]); LIMIT = int(sys.argv[2])
coals = list(range(1, (1 << K) - 1)); W = 8
def pack(tabs): 
    v = 0
    for k, t in enumerate(tabs): v |= t << (W*k)
    return v
M = [pack([0xFF if (C >> i & 1) else 0 for C in coals]) for i in range(K)]
FULL = pack([0xFF]*len(coals))
A, B, Cc = 0xF0, 0xCC, 0xAA
gens = [pack([A]*len(coals)), pack([B]*len(coals)), pack([Cc]*len(coals))] + [M[j] for j in range(K)]
maj = (A&B)|(B&Cc)|(A&Cc)
target = pack([maj]*len(coals))
S = set(gens); frontier = list(gens); t0 = time.time(); depth = 0
while frontier and target not in S and len(S) < LIMIT:
    depth += 1; new = []
    Sl = list(S)
    for i in range(K):
        Mi = M[i]; nMi = FULL ^ Mi
        for s in frontier:
            for t in Sl:
                u = ((s | t) & Mi) | ((s & t) & nMi)
                if u not in S: S.add(u); new.append(u)
    frontier = new
    print(f"depth {depth}: |S|={len(S)}  ({time.time()-t0:.1f}s)", flush=True)
print(f"K={K}: majority is a term: {target in S}  (explored {len(S)} ops; frontier empty={not frontier})")
