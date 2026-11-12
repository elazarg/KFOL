#!/usr/bin/env python3
"""Standalone finite checks for the four-input boundary-gluing counterexample.

No clone enumeration, external packages, or /tmp artifacts are used. All
positive realizability assertions are checked against displayed core terms.
The nonrealizability argument is the analytic proof in noncore.md.
"""
from itertools import product, combinations
from pathlib import Path
import argparse
import json

# Winner menus are nonzero masks; owners b=0, c=1, a=2.
B, C, A, N, ALL = 1, 2, 4, 3, 7
V4 = list(product(range(1, 8), repeat=4))
V3 = list(product(range(1, 8), repeat=3))


def star(r, x, y):
    return 1 << r if x == 1 << r or y == 1 << r else x | y


def term(t, v):
    if isinstance(t, int):
        return v[t]
    if t[0] == "union":
        return term(t[1], v) | term(t[2], v)
    _, r, x, y = t
    return star(r, term(x, v), term(y, v))


def s(r, x, y):
    return ["choice", r, x, y]


# H(A,B,C,D)=((D *1 A) *0 B) *1 ((C *1 B) *0 A).
H = s(1, s(0, s(1, 3, 0), 1), s(0, s(1, 2, 1), 0))
# In G_j, variables are the remaining original inputs, in increasing order.
G = [
    ["union", s(0, 2, 0), s(1, 1, 0)],
    ["union", s(1, 2, 0), s(0, 1, 0)],
    s(1, s(0, s(1, 2, 0), 1), s(2, s(0, 1, 0), 0)),
    s(0, s(1, s(0, 2, 0), 1), s(2, s(1, 1, 0), 0)),
]


def F(v):
    x, y, z, w = v
    exceptional = (x == N and y & A and z == C and w == B) or (
        y == N and x & A and z == B and w == C
    )
    return N if exceptional else term(H, v)


def phi(bits):
    x, y, z, w = bits
    return bool((x and y) or (x and z) or (y and w))


def profile(r, coalition):
    bits = [bool(coalition >> j & 1) for j in range(4)]
    if r == 0:
        return not phi([not x for x in bits])
    if r == 1:
        return phi(bits)
    return all(bits)


# Bichain values b=0,c=1,P=2,N=3.
def view(x):
    return 2 if x & A else 0 if x == B else 1 if x == C else 3


def extension(v):
    cubes = list(product(*[(0, 1) if x >= 2 else (x,) for x in v]))
    outputs = {phi(w) for w in cubes}
    if len(outputs) == 1:
        return int(outputs.pop())
    for j, x in enumerate(v):
        if x != 2:
            continue
        for w in cubes:
            if w[j]:
                continue
            other = list(w)
            other[j] = 1
            if phi(w) != phi(other):
                return 2
    return 3


def guard_keys():
    return [(r, j, p) for r in range(3) for j in range(4)
            for p in product([s for s in range(3) if s != r] + [3], repeat=3)]


def probe(r, j, p):
    v = [ALL ^ (1 << r)] * 4
    v[j] = 1 << r
    for i, status in zip([i for i in range(4) if i != j], p):
        v[i] = ALL ^ (1 << r) if status == 3 else 1 << status
    return tuple(v)


KEYS = guard_keys()
GUARDS = {key: bool(F(probe(*key)) >> key[0] & 1) for key in KEYS}


def reconstruct(v):
    out = 0
    for r in range(3):
        other = [s for s in range(3) if s != r]
        for j in range(4):
            if not (v[j] >> r & 1):
                continue
            p = tuple(x.bit_length() - 1 if x in (1 << other[0], 1 << other[1]) else 3
                      for i, x in enumerate(v) if i != j)
            if GUARDS[(r, j, p)]:
                out |= 1 << r
    return out


def residual(deleted, v):
    remaining = [j for j in range(4) if j not in deleted]
    out = 0
    for r in range(3):
        full = [ALL ^ (1 << r)] * 4
        for j, x in zip(remaining, v):
            full[j] = x
        out |= bool(F(full) >> r & 1) << r
    return out


# Explicit witnesses for all six two-coordinate residuals.
U = ["union", 0, 1]
L = s(0, s(1, 0, 1), s(2, s(0, 0, 1), 0))
R = s(2, s(1, 0, 1), s(1, s(0, 0, 1), 0))
PAIR_TERMS = {(0, 1): U, (0, 2): L, (0, 3): R,
              (1, 2): R, (1, 3): L, (2, 3): U}


def certificate():
    return {
        "owners": {"b": 0, "c": 1, "a": 2},
        "term_encoding": "integer=input index; [choice,owner,left,right]; [union,left,right]",
        "atomic_term": H,
        "residual_terms": G,
        "guard_key_order": "r=0..2, j=0..3, p lex in (other owners,3=neutral)^3",
        "guard_bits": [int(GUARDS[k]) for k in KEYS],
        "table_order": "lexicographic product(range(1,8), repeat=4)",
        "table": [F(v) for v in V4],
        "profile_truth_bits": [sum(profile(r, x) << x for x in range(16)) for r in range(3)],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    path = Path(__file__).with_name("certificate.json")
    if args.write_certificate:
        path.write_text(json.dumps(certificate(), indent=2) + "\n")
    assert json.loads(path.read_text()) == certificate()
    assert all(F(v) == term(H, v) for v in product((B, C, A), repeat=4))
    assert sum(F(v) != term(H, v) for v in V4) == 8
    assert all(F(v) == term(H, v) for v in V4 if len(set(v)) < 4)
    assert all(view(F(v)) == extension(tuple(map(view, v))) for v in V4)
    # Four-row Horn invariant, with no term-clone enumeration.
    rows = [(1, 1, 0, 0), (0, 0, 1, 1),
            (3, 2, 1, 0), (2, 3, 0, 1)]
    reps = (B, C, A, N)
    assert [view(F(tuple(reps[x] for x in row))) for row in rows] == [1, 0, 3, 3]

    def invariant(t):
        x, y, z, w = t
        return ((x != 1 or (z != 0 and w != 0))
                and (y != 0 or (z != 1 and w != 1))
                and (x != 1 or y != 0 or z == 2 or w == 2))

    states = [t for t in product(range(4), repeat=4) if invariant(t)]
    assert all(invariant(tuple(row[j] for row in rows)) for j in range(4))
    assert not invariant((1, 0, 3, 3))
    irank, srank = (0, 3, 1, 2), (0, 3, 2, 1)
    meet = [[x if irank[x] <= irank[y] else y for y in range(4)] for x in range(4)]
    join = [[x if srank[x] >= srank[y] else y for y in range(4)] for x in range(4)]
    union = [[view(reps[x] | reps[y]) for y in range(4)] for x in range(4)]
    for gate in (meet, join, union):
        for x in states:
            for y in states:
                assert invariant(tuple(gate[a][b] for a, b in zip(x, y)))
    # Each negative row separately has a pure formula with the same Boolean function.
    t_r = s(1, s(0, 0, s(1, 1, 2)), s(0, 1, 3))
    t_s = s(1, s(0, s(1, 0, 3), 1), s(0, 0, 2))
    for witness in (t_r, t_s):
        for bits in product((0, 1), repeat=4):
            assert view(term(witness, tuple(reps[x] for x in bits))) == phi(bits)
    assert [view(term(t_r, tuple(reps[x] for x in row))) for row in rows[2:]] == [3, 2]
    assert [view(term(t_s, tuple(reps[x] for x in row))) for row in rows[2:]] == [2, 3]
    print("81 joint atomic rows, all proper identification minors, eight modified inputs, full P4 quotient: PASS")

    for j, witness in enumerate(G):
        assert all(residual((j,), v) == term(witness, v) for v in V3)
    for deleted, witness in PAIR_TERMS.items():
        assert all(residual(deleted, v) == term(witness, v)
                   for v in product(range(1, 8), repeat=2))
    for deleted in combinations(range(4), 3):
        assert all(residual(deleted, (x,)) == x for x in range(1, 8))
    assert residual((0, 1, 2, 3), ()) == 0
    print("All proper nonempty-coordinate residuals have explicit core witnesses: PASS")

    assert all(F(v) == reconstruct(v) for v in V4)
    edges = 0
    for (r, j, p), old in GUARDS.items():
        for i, status in enumerate(p):
            if status == 3:
                continue
            new = list(p)
            new[i] = 3
            assert not old or GUARDS[(r, j, tuple(new))]
            edges += 1
    for v in V4:
        out = F(v)
        assert 1 <= out <= ALL
        for r in range(3):
            coalition = sum((x == 1 << r) << j for j, x in enumerate(v))
            assert (out == 1 << r) == profile(r, coalition)
            if out >> r & 1:
                assert any((x >> r & 1) and not (x & ~out) for x in v)
    # Complete observer views, including every rival singleton test, factor
    # through the coordinatewise observation quotient.
    for r in range(3):
        def pv(x):
            if x >> r & 1:
                return ("possible",)
            if x in (1, 2, 4):
                return ("other", x.bit_length() - 1)
            return ("impossible",)
        observed = {}
        for v in V4:
            key = tuple(map(pv, v))
            image = pv(F(v))
            assert observed.setdefault(key, image) == image
    print(f"324 canonical guards, {edges} passive edges, singleton profiles, whole-input sources: PASS")

    changes = 0
    for v in V4:
        out = F(v)
        for r in range(3):
            if out >> r & 1:
                continue
            for j, x in enumerate(v):
                if not (x >> r & 1):
                    continue
                for y in range(1, 8):
                    w = list(v)
                    w[j] = y
                    assert F(w) == out
                    changes += 1
    print(f"Full omission independence ({changes} elementary replacements): PASS")
    print("Four-row Horn invariant closed under all three operations; separate witnesses: PASS")
    print("All finite checks passed. Global noncore proof: noncore.md.")


if __name__ == "__main__":
    main()
