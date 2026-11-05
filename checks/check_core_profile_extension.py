"""Audit selected-profile preservation and the finite two-image quotient.

The arbitrary-algebra proof is in the core-basis appendix. Finite image
counts do not bound the fibers or prove finiteness of the whole extension.
"""
from itertools import combinations, product
import json
from pathlib import Path

from check_core_owned_reset import test_models
from check_core_upper_bound_extension import close


def check():
    preservation = homomorphisms = extensions = 0
    for model, (join, choices) in enumerate(test_models()):
        if len(join) > 25:
            continue
        active = [h for h in choices if h != join]
        for top in range(len(join)):
            ideal = [a for a in range(len(join)) if join[a][top] == top]
            for f in choices:
                for y in ideal:
                    if f[y][top] != y:
                        continue
                    for g in choices:
                        if g is f:
                            continue
                        for a, b in product(ideal, repeat=2):
                            assert g[y][f[a][b]] == f[g[y][a]][g[y][b]], (
                                model, top, y, a, b)
                            preservation += 1
            if len(active) != 2:
                continue
            operations = [join] + active
            coefficient_sets = set()
            for arity in range(3):
                for generators in combinations(ideal, arity):
                    coefficient_sets.add(frozenset(close([top, *generators], operations)))
            for f, g in (active, active[::-1]):
                for y in ideal:
                    if f[y][top] != y:
                        continue
                    F = {a: f[y][a] for a in ideal}
                    G = {a: g[y][a] for a in ideal}
                    for h in operations:
                        for a, b in product(ideal, repeat=2):
                            assert F[h[a][b]] == h[F[a]][F[b]]
                            assert G[h[a][b]] == h[G[a]][G[b]]
                            homomorphisms += 2
                    assert all(F[G[a]] == G[F[a]] == y for a in ideal)
                    for coefficients in coefficient_sets:
                        if y in coefficients:
                            continue
                        generated = close([*coefficients, y], operations)
                        first = {F[c] for c in coefficients}
                        second = {G[c] for c in coefficients}
                        second_image = second | {y} | {join[y][d] for d in second}
                        assert {F[a] for a in generated} == first
                        assert {G[a] for a in generated} == second_image
                        assert len(second_image) <= 2 * len(second)
                        quotient = {(F[a], G[a]) for a in generated}
                        assert len(quotient) <= 2 * len(coefficients) ** 2
                        extensions += 1

    # The finite quotient can have nontrivial fibers in a genuine extension.
    data = json.loads((Path(__file__).parent / 'data' /
                       'core-owned-unit-observer-countermodel.json').read_text())
    join = data['join']
    g, f = data['operations'][:2]
    coefficients = {0, 3, 5, 8, 9}
    top, y = 5, 4
    assert close(coefficients, [join, f, g]) == coefficients
    assert all(join[c][top] == top for c in coefficients | {y})
    assert f[y][top] == y and y not in coefficients
    generated = close([*coefficients, y], [join, f, g])
    assert {7, 9} <= generated
    assert (f[y][7], g[y][7]) == (f[y][9], g[y][9]) == (4, 7)

    # In three active owners, preservation is specific to the selected choice.
    def add(a, b):
        return a if a == b else max(3, a, b)
    def choice(i, a, b):
        return i if i in (a, b) else add(a, b)
    assert choice(1, 0, choice(2, 2, 4)) == 3
    assert choice(2, choice(1, 0, 2), choice(1, 0, 4)) == 4
    print(f'Selected-profile preservation: {preservation} instances; '
          f'{homomorphisms} two-owner homomorphism entries; '
          f'{extensions} finite-image extension audits. '
          'Verified the nontrivial fiber and three-owner scope counterexamples.')


if __name__ == '__main__':
    check()
