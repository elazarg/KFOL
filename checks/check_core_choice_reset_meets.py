"""Audit partial reset meets inside a basic choice image.

The image-relative greatest-lower-bound claim is checked for every nonempty
owner subset. For two owners including the translating owner, the audit
also checks the greatest lower bound in the whole algebra. The compressed
maps used in the proof are checked separately on their full image filters.
"""

from check_core_owned_reset import test_models


def audit(add, operations):
    n = len(add)
    ideals = [sum(1 << x for x in range(n) if add[x][y] == y)
              for y in range(n)]
    subsets = [tuple(i for i in range(len(operations)) if mask >> i & 1)
               for mask in range(1, 1 << len(operations))]
    counts = [0] * 5
    for r, operation in enumerate(operations):
        for a in range(n):
            translate = operation[a]
            image = set(translate)
            image_mask = sum(1 << z for z in image)
            for x in range(n):
                maps = [[translate[f[x][z]] for z in range(n)]
                        for f in operations]
                cone = {z for z in image
                        if add[translate[x]][z] == z}
                for h in maps:
                    for z in cone:
                        assert h[z] in cone
                        assert add[h[z]][z] == z
                        assert h[h[z]] == h[z]
                        counts[0] += 1
                for i, h in enumerate(maps):
                    for k in range(i):
                        g = maps[k]
                        for z in cone:
                            assert h[g[z]] == g[h[z]]
                            assert add[h[z]][g[z]] == z
                            counts[1] += 1
                for u in range(n):
                    if add[x][u] != u:
                        continue
                    for i, f in enumerate(operations):
                        assert maps[i][translate[u]] == translate[f[x][u]]
                    for selected in subsets:
                        q, compressed = u, translate[u]
                        lower = (1 << n) - 1
                        for i in selected:
                            q = operations[i][x][q]
                            compressed = maps[i][compressed]
                            lower &= ideals[translate[operations[i][x][u]]]
                            counts[2] += 1
                        value = translate[q]
                        assert compressed == value
                        assert lower & image_mask == ideals[value] & image_mask
                        counts[3] += 1
                        if len(selected) == 2 and r in selected:
                            assert lower == ideals[value]
                            counts[4] += 1
    return counts


def check():
    models = test_models()
    totals = [0] * 5
    for add, operations in models:
        totals = [a + b for a, b in zip(totals, audit(add, operations))]
    print(f'Choice reset meets: {len(models)} models; '
          f'{totals[0]} contraction/idempotence checks, '
          f'{totals[1]} commutation/coverage checks, '
          f'{totals[2]} compressed-fold stages, '
          f'{totals[3]} image-relative greatest-lower-bound checks, and '
          f'{totals[4]} ambient two-owner greatest-lower-bound checks. '
          'The arbitrary-algebra argument uses Gamma_K and mixed absorption.')


if __name__ == '__main__':
    check()
