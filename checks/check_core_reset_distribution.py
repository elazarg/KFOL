"""Audit the atomic-quotient proof of reset distribution."""

from itertools import permutations, product

from check_core_owned_reset import test_models


def audit(add, operations):
    triples = 0
    for f, g in permutations(operations, 2):
        def R(a, z):
            return f[z][g[z][a]]

        for x, y, z in product(range(len(add)), repeat=3):
            u, v = f[x][y], f[x][z]
            p, q = f[x][g[y][z]], g[u][v]
            t = add[x][add[y][z]]
            assert f[x][q] == q
            assert f[q][y] == f[q][u]
            assert g[q][u] == q
            assert R(y, q) == g[q][f[q][u]] == f[q][g[q][u]] == q
            assert R(x, q) == R(z, q) == R(t, q) == q
            rx, ry, rz = (R(t, a) for a in (x, y, z))
            assert all(add[a][t] == t and R(t, a) == a for a in (rx, ry, rz))
            assert R(t, p) == f[rx][g[ry][rz]]
            assert R(t, q) == g[f[rx][ry]][f[rx][rz]]
            assert f[rx][g[ry][rz]] == g[f[rx][ry]][f[rx][rz]]
            assert R(x, p) == R(g[y][z], p) == p
            assert R(t, p) == R(add[y][z], p) == R(f[y][z], p) == q
            assert f[p][q] == g[p][q] == q
            triples += 1
    return triples


def check():
    models = test_models()
    triples = sum(audit(add, operations) for add, operations in models)
    print(f'Reset distribution: {triples} triples in {len(models)} models; '
          'image closure, operand resets, atomic distributivity, reset '
          'composition and both doubled-distribution conclusions passed. '
          'The universal result is proved by the written quotient argument.')


if __name__ == '__main__':
    check()
