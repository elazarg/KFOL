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
    assert all(view(F(v)) == extension(tuple(map(view, v))) for v in V4)
    # Finite Boolean facts used by the analytic ownership proof, not a clone search.
    ownership = [
        (0b0101, 0b0011, 2, (3, 1, 2, 0)),
        (0b1010, 0b0011, 3, (1, 3, 0, 2)),
        (0b0011, 0b0101, 1, (3, 2, 1, 0)),
        (0b0011, 0b1010, 0, (2, 3, 0, 1)),
    ]
    for first, second, marked, cube in ownership:
        assert not (second >> marked & 1)
        assert not (first & ~(second | (1 << marked)))
        for endpoint in (second, second | (1 << marked)):
            assert all(x >= 2 or bool(endpoint >> j & 1) == bool(x)
                       for j, x in enumerate(cube))
        assert extension(cube) == 3
    for bits in product((False, True), repeat=4):
        assert (not phi([not x for x in bits])) == phi((bits[0], bits[1], bits[3], bits[2]))
    seven = json.loads(Path(__file__).with_name("seven-relation.json").read_text())
    rows = seven["rows"]
    assert rows == [[1, 1, 0, 0], [3, 1, 2, 0], [1, 3, 0, 2],
                    [3, 2, 1, 0], [2, 3, 0, 1], [3, 0, 1, 2], [0, 3, 2, 1]]
    reps = (B, C, ALL, N)
    assert [view(F(tuple(reps[x] for x in row))) for row in rows] == [1] + [3] * 6
    # These are all 168 monotone Boolean functions, not an enumeration of
    # term functions. Inessential marked sources give the five-function list.
    monotone = [truth for truth in range(1 << 16) if all(
        not (truth >> x & 1) or (truth >> (x | (1 << j)) & 1)
        for x in range(16) for j in range(4))]
    assert len(monotone) == 168
    def essential(truth, row, marked):
        lo = sum((x == 1) << j for j, x in enumerate(row))
        hi = sum((x != 0) << j for j, x in enumerate(row))
        return any(not (x >> marked & 1)
                   and ((truth >> x & 1) != (truth >> (x | (1 << marked)) & 1))
                   for x in range(16) if x & lo == lo and not (x & ~hi))
    matching = [truth for truth in monotone if all(
        not essential(truth, row, row.index(2)) for row in rows[1:])]
    p4_truth = sum(phi([(x >> j) & 1 for j in range(4)]) << x for x in range(16))
    assert set(matching) == {0, (1 << 16) - 1, 1 << 15, (1 << 16) - 2, p4_truth}
    lower, upper = (1, 2, 4, 8, 9, 12, 6), (3, 5, 10, 7, 13, 11, 14)
    for truth in matching:
        assert len({truth >> x & 1 for x in lower}) == 1
        assert len({truth >> x & 1 for x in upper}) == 1
    print("81 joint atomic rows, eight modified inputs, and full P4 scalar quotient: PASS")

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
    states = {tuple(x) for x in seven["states"]}
    target = (1,) + (3,) * 6
    assert len(rows) == 7 and len(states) == 231
    assert all(tuple(row[j] for row in rows) in states for j in range(4))
    assert {x for x in states if all(y != 2 for y in x[1:])} == {(0,) * 7, (1,) * 7}
    assert target not in states
    irank, srank = (0, 3, 1, 2), (0, 3, 2, 1)
    meet = [[x if irank[x] <= irank[y] else y for y in range(4)] for x in range(4)]
    join = [[x if srank[x] >= srank[y] else y for y in range(4)] for x in range(4)]
    for gate in (meet, join):
        for x in states:
            for y in states:
                assert tuple(gate[a][b] for a, b in zip(x, y)) in states
    print("168-function Boolean classification and 231-state seven-row pure certificate: PASS")
    print("All finite checks passed. Global noncore proof: noncore.md.")


if __name__ == "__main__":
    main()
