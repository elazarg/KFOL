#!/usr/bin/env python3
"""A five-state core algebra not separated by flat/common-fiber targets.

Standard library only. Hardcodes the stored seven-state native cover,
checks the universal obstruction equations, and audits all flat atomic
observers for the explicitly bounded owner counts3,4,5.
The arbitrary-target SP obstruction is the short equation argument in
verify_obstruction_equations, together with the image classification in
its docstring. No failure of core membership is claimed.
"""
from itertools import combinations, permutations, product
import json

JOIN = [
    [0, 1, 2, 3, 4], [1, 1, 4, 4, 4], [2, 4, 2, 4, 4],
    [3, 4, 4, 3, 4], [4, 4, 4, 4, 4],
]
F = [
    [0, 0, 0, 0, 0], [0, 1, 2, 3, 4], [0, 2, 2, 0, 2],
    [0, 3, 0, 3, 3], [0, 4, 2, 3, 4],
]
CHOICES = [JOIN, JOIN, F]
OPS = CHOICES + [JOIN]
QUOTIENT = [0, 3, 1, 2, 3]
SOURCE = [(2, 2), (2, 4), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)]
IMAGE = [0, 3, 1, 4, 2, 4, 4]


def verify_candidate():
    count = 0
    for h in OPS:
        for x in range(5):
            assert h[x][x] == x
            count += 1
        for x, y in product(range(5), repeat=2):
            assert h[x][y] == h[y][x]
            count += 1
        for x, y, z in product(range(5), repeat=3):
            assert h[x][h[y][z]] == h[h[x][y]][z]
            count += 1
    for h in CHOICES:
        for x, y, z in product(range(5), repeat=3):
            assert h[x][JOIN[y][z]] == JOIN[h[x][y]][h[x][z]]
            count += 1
    for h, k in combinations(CHOICES, 2):
        for x, y in product(range(5), repeat=2):
            assert JOIN[h[x][y]][k[x][y]] == JOIN[x][y]
            assert h[x][k[x][y]] == k[x][h[x][y]]
            count += 2
    for h, k, ell in permutations(CHOICES):
        for x, y in product(range(5), repeat=2):
            assert ell[h[x][y]][k[x][y]] == JOIN[x][y]
            count += 1
    for h, k in permutations(CHOICES, 2):
        for x, y, z in product(range(5), repeat=3):
            assert h[x][k[y][h[y][z]]] == h[x][k[y][h[x][h[y][z]]]]
            count += 1
    for c, x, y, z in product(range(5), repeat=4):
        value = JOIN[JOIN[CHOICES[0][c][x]][CHOICES[1][c][y]]][F[c][z]]
        assert JOIN[c][value] == value
        count += 1
    return count


def verify_native_cover():
    # Proper native observer {a_2,n,p}; other owners act as join.
    image = dict(zip(SOURCE, IMAGE))
    assert set(IMAGE) == set(range(5))
    count = 0
    for owner, h in enumerate(OPS):
        def scalar(x, y):
            return 2 if owner == 2 and 2 in (x, y) else max(x, y)
        for x, y in product(SOURCE, repeat=2):
            value = tuple(scalar(a, b) for a, b in zip(x, y))
            assert value in image
            assert image[value] == h[image[x]][image[y]]
            count += 1
    return count


def reset(c, x):
    value = JOIN[c][x]
    for h in CHOICES:
        value = h[x][value]
    return value


def verify_atomic_reflection():
    qops = [
        [[x | y for y in range(4)] for x in range(4)],
        [[x | y for y in range(4)] for x in range(4)],
        [[x & y for y in range(4)] for x in range(4)],
        [[x | y for y in range(4)] for x in range(4)],
    ]
    assert [reset(4, x) for x in range(5)] == [0, 4, 2, 3, 4]
    for c, x in product(range(5), repeat=2):
        assert QUOTIENT[reset(c, x)] == QUOTIENT[x]
        assert reset(c, x) == x or {reset(c, x), x} == {1, 4}
    for h, qh in zip(OPS, qops):
        for x, y in product(range(5), repeat=2):
            assert QUOTIENT[h[x][y]] == qh[QUOTIENT[x]][QUOTIENT[y]]
            if QUOTIENT[x] == QUOTIENT[y]:
                assert h[x][y] == JOIN[x][y]
    for c, x in product(range(4), repeat=2):
        value = c | x
        for h in qops[:3]:
            value = h[x][value]
        assert value == x
    return qops


def verify_obstruction_equations():
    """Universal argument for any homomorphism h:A->X in the flat-fiber class.

    The composite to the flat base factors through QUOTIENT, since reset
    at4 identifies1,4 in any atomic image. A nonconstant image can contain
    no foreign atom a_i, i!=2: source choice i equals join, while in the
    target it absorbs a_i. Thus its image is {a_2,n}. A lattice hom from
    Boolean4 to this chain sends exactly one Boolean atom with0 to a_2.
    Constant images also put0 and2 in the same fiber.

    With v=2 or3 in that fiber, common-fiber f=join gives h(0)=h(v).
    Joining with h(1) then gives h(1)=h(4), by the four entries below.
    Every such observer therefore identifies1,4, including arbitrary
    infinite flat/common-fiber targets. Products cannot separate them.
    """
    for v in (2, 3):
        assert F[0][v] == 0
        assert JOIN[0][v] == v
        assert JOIN[0][1] == 1
        assert JOIN[v][1] == 4


def congruence(pairs):
    parent = list(range(5))
    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x
    def merge(x, y):
        x, y = root(x), root(y)
        if x == y:
            return False
        parent[y] = x
        return True
    for x, y in pairs:
        merge(x, y)
    changed = True
    while changed:
        changed = False
        for x, y in combinations(range(5), 2):
            if root(x) != root(y):
                continue
            for h in OPS:
                for z in range(5):
                    changed = merge(h[x][z], h[y][z]) or changed
    blocks = {}
    for x in range(5):
        blocks.setdefault(root(x), []).append(x)
    return sorted(blocks.values())


def verify_flat_observers(qops):
    records = []
    neutral_kernels = []
    for owners in (3, 4, 5):
        size = owners + 1
        jn = [[x if x == y else owners for y in range(size)] for x in range(size)]
        target = [
            [[i if i in (x, y) else jn[x][y] for y in range(size)]
             for x in range(size)] for i in range(owners)
        ] + [jn]
        source = [qops[2] if i == 2 else qops[0] for i in range(owners)] + [qops[0]]
        maps = []
        for phi in product(range(size), repeat=4):
            if not all(phi[h[x][y]] == k[phi[x]][phi[y]]
                       for h, k in zip(source, target)
                       for x, y in product(range(4), repeat=2)):
                continue
            maps.append(phi)
            if len(set(phi)) > 1:
                assert set(phi) == {2, owners}
                assert phi[0] == 2 and phi[3] == owners
                assert (phi[1] == 2) != (phi[2] == 2)
            v = 2 if phi[QUOTIENT[0]] == phi[QUOTIENT[2]] else 3
            assert phi[QUOTIENT[0]] == phi[QUOTIENT[v]]
            if owners == 3 and phi[3] == owners:
                pairs = [(h[x][y], JOIN[x][y]) for h in CHOICES
                         for x, y in product(range(5), repeat=2)
                         if phi[QUOTIENT[x]] == phi[QUOTIENT[y]]]
                blocks = congruence(pairs)
                assert any(1 in b and 4 in b for b in blocks)
                neutral_kernels.append(blocks)
        assert len(maps) == owners + 3
        records.append({"owners": owners, "flat_atomic_maps": len(maps)})
    expected = sorted([
        [[0, 2], [1, 3, 4]], [[0, 3], [1, 2, 4]], [[0, 1, 2, 3, 4]],
    ])
    assert sorted(neutral_kernels) == expected
    surviving = [(x, y) for x, y in combinations(range(5), 2)
                 if all(any(x in b and y in b for b in blocks)
                        for blocks in neutral_kernels)]
    assert surviving == [(1, 4)]
    return records, neutral_kernels


def main():
    laws = verify_candidate()
    cover = verify_native_cover()
    qops = verify_atomic_reflection()
    verify_obstruction_equations()
    observers, kernels = verify_flat_observers(qops)
    print(json.dumps({
        "status": "PASS", "candidate_law_instances": laws,
        "native_cover_source_size": len(SOURCE), "native_cover_entries": cover,
        "atomic_quotient": QUOTIENT, "atomic_quotient_is_boolean_four": True,
        "flat_observers": observers, "top_neutral_kernel_blocks": kernels,
        "unseparated_pair": [1, 4],
        "scope": "Genuine core algebra; obstruction only to SP of the flat-fiber class.",
    }, indent=2))


if __name__ == "__main__":
    main()
