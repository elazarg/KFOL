"""Audit fixed-parameter endomorphisms and pairwise reset expansion.

The proofs apply to arbitrary algebras. This independent finite audit includes
intermediate inequalities, generated congruences, and the local quotients;
it does not infer a basis from the checked models.
"""

from collections import Counter
from functools import reduce
from itertools import combinations_with_replacement, product

from check_core_atomic_basis import operation_tables
from check_core_owned_reset import test_models
from probe_residual import merge_congruence, root


def check_model(join, operations):
    carrier = range(len(join))
    add, ops, reset = operation_tables(
        carrier, lambda x, y: join[x][y],
        lambda i, x, y: operations[i][x][y], len(operations))
    counts = Counter()
    for u in carrier:
        for i, f in enumerate(ops):
            image = sorted({f[u, x] for x in carrier})
            others = [k for k in range(len(ops)) if k != i]
            fixed = {x for x in image
                     if all(ops[k][u, x] == x for k in others)}
            h_map = {
                x: reduce(lambda v, k: ops[k][u, v], others, x)
                for x in image
            }
            assert set(h_map.values()) == fixed
            assert all(h_map[x] == reset[x, u] for x in image)
            assert all(add[u, h] == h for h in fixed)
            assert all(op[h, k] == add[h, k]
                       for op in [add] + ops for h, k in product(fixed, repeat=2))

            # Check the weaker hypothesis for preservation of just one owner.
            for h in image:
                if add[u, h] != h:
                    continue
                for k in others:
                    g = ops[k]
                    if g[u, h] != h:
                        continue
                    for x in image:
                        assert g[h, x] == add[h, g[u, x]]
                    for x, y in product(image, repeat=2):
                        v = f[h, g[x, y]]
                        w = g[f[h, x], f[h, y]]
                        assert add[v, w] == w
                        assert add[w, add[f[h, x], f[h, y]]] == add[f[h, x], f[h, y]]
                        assert add[w, add[h, v]] == add[h, v]
                        assert v == w
                        counts['partial_homomorphisms'] += 1

            index = {x: n for n, x in enumerate(image)}
            translations = [tuple(index[op[a, x]] for x in image)
                            for op in [add] + ops for a in image]
            top = reduce(lambda x, y: add[x, y], image)
            for j in others:
                m = ops[j][u, top]
                r = {x: f[m, x] for x in image}
                assert all(ops[j][m, x] == m for x in image)
                assert all(r[op[x, y]] == op[r[x], r[y]]
                           for op in [add] + ops for x, y in product(image, repeat=2))
                generated = merge_congruence(list(range(len(image))),
                                             index[u], index[m], translations)
                assert all((root(generated, index[x]) == root(generated, index[y]))
                           == (r[x] == r[y]) for x, y in product(image, repeat=2))
                assert all(add[x, r[x]] == r[x] and r[r[x]] == r[x]
                           and f[m, r[x]] == r[x] for x in image)
                counts['two_owner_quotients'] += 1
                for k in others:
                    if k == j:
                        continue
                    g = ops[k]
                    for x, y in product(image, repeat=2):
                        q, s = g[x, y], add[x, y]
                        assert add[s, add[m, q]] == add[m, q]
                        v, w = r[q], r[s]
                        assert add[q, v] == v
                        assert add[w, add[m, v]] == add[m, v]
                        assert v == w == add[r[x], r[y]] == g[r[x], r[y]]
                        counts['top_erasure_pairs'] += 1

            theta = list(range(len(image)))
            for h in fixed:
                r = {x: f[h, x] for x in image}
                assert all(r[x] == reset[h, x] and add[x, r[x]] == r[x]
                           and r[r[x]] == r[x] for x in image)
                assert all(r[op[x, y]] == op[r[x], r[y]]
                           for op in [add] + ops for x, y in product(image, repeat=2))
                generated = merge_congruence(list(range(len(image))),
                                             index[u], index[h], translations)
                assert all((root(generated, index[x]) == root(generated, index[y]))
                           == (r[x] == r[y]) for x, y in product(image, repeat=2))
                theta = merge_congruence(theta, index[u], index[h], translations)
                counts['principal_congruences'] += 1

                ideal = {x for x in image if add[h_map[x], h] == h}
                assert all(op[x, y] in ideal
                           for op in [add] + ops for x, y in product(ideal, repeat=2))
                assert all(x in ideal for y in ideal for x in image if add[x, y] == y)
                local = {r[x] for x in ideal}
                assert local <= ideal
                assert all(reset[y, h] == h and f[h, y] == y for y in local)
                assert all(r[x] == x for x in image if h_map[x] == h)
                counts['local_quotients'] += 1

                for k in fixed:
                    assert all(r[f[k, x]] == f[add[h, k], x] for x in image)
                    counts['compositions'] += 1

            greatest = reduce(lambda x, y: add[x, y], fixed)
            assert greatest in fixed
            assert all((root(theta, index[x]) == root(theta, index[y]))
                       == (f[greatest, x] == f[greatest, y])
                       for x, y in product(image, repeat=2))
            assert all(reset[f[greatest, x], greatest] == greatest for x in image)
            counts['choice_images'] += 1

            # Three inputs suffice to test the generating finite-join identity.
            for c in image:
                for x, y, z in combinations_with_replacement(image, 3):
                    total = add[x, add[y, z]]
                    pairs = add[reset[c, add[x, y]],
                                add[reset[c, add[x, z]], reset[c, add[y, z]]]]
                    assert reset[c, total] == pairs
                    counts['reset_triples'] += 1
    return counts


def check():
    models = test_models()
    totals = Counter()
    for join, operations in models:
        totals.update(check_model(join, operations))
    # The quotient family is not in general a subdirect representation.
    join = [[0, 1], [1, 1]]
    unit, top = 0, 1
    m = join[unit][top]
    assert join[m] == [1, 1]
    print(f'Owned-unit fixed parameters: {len(models)} models; '
          + ', '.join(f'{value} {key}' for key, value in sorted(totals.items()))
          + '. Intermediate bounds, fixed-point descriptions, full '
            'endomorphisms, generated principal congruences, directed unions, '
            'the right-reset laws on local quotients, and the two-owner '
            'quotient maps all passed. The two-element semilattice confirms '
            'that the last family need not separate elements.')


if __name__ == '__main__':
    check()
