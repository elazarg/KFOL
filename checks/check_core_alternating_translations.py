"""Audit the arbitrary-algebra proof of two-translation reduction.

The proof uses the derived join form of mixed absorption and two applications
of the mixed-meet theorem. Finite tables check every intermediate bound and
meet; they do not establish completeness of the proposed core basis.
"""

from itertools import permutations, product

from check_core_owned_reset import test_models


def partial_meets(add):
    """Compute actual greatest lower bounds, leaving absent meets as None."""
    carrier = range(len(add))
    lower = [{z for z in carrier if add[z][x] == x} for x in carrier]
    result = {}
    for x, y in product(carrier, repeat=2):
        common = lower[x] & lower[y]
        maxima = [z for z in common if common <= lower[z]]
        assert len(maxima) <= 1
        result[x, y] = maxima[0] if maxima else None
    return result


def compose(left, right):
    return tuple(left[value] for value in right)


def audit(add, operations):
    carrier = range(len(add))
    meets = partial_meets(add)
    triples = pairs = powers = 0
    for f, g in permutations(operations, 2):
        for x, y in product(carrier, repeat=2):
            F, G = tuple(f[x]), tuple(g[y])
            FG, GF = compose(F, G), compose(G, F)
            FGF, GFG = compose(FG, F), compose(GF, G)
            FGFG = compose(FGF, G)
            assert FGFG == FGF
            assert compose(GFG, F) == GFG
            assert compose(FGF, FGF) == FGF
            assert compose(GFG, GFG) == GFG
            forms = (F, G, FG, GF, FGF, GFG)
            # Closure checks the word reduction with arbitrary word length:
            # multiplying any normal form by either generator stays in the set.
            for P in forms:
                assert compose(P, F) in forms and compose(P, G) in forms
                square = compose(P, P)
                assert compose(square, P) == square
                powers += 1

            c, r = f[x][y], f[x][g[x][y]]
            assert add[x][r] == r
            for z in carrier:
                v, w = FGF[z], FGFG[z]
                assert add[x][g[x][F[z]]] == g[x][F[z]]
                assert FG[g[x][F[z]]] == g[x][v]
                assert add[r][g[x][v]] == g[x][v]
                assert add[g[x][v]][add[x][v]] == add[x][v]
                assert add[x][v] == add[r][v]
                assert add[x][w] == add[r][w]
                assert add[r][v] == add[r][w]
                assert add[x][v] == add[x][w]
                assert add[c][FG[z]] == add[c][v]

                # Both actual meet equalities are needed for cancellation.
                assert meets[add[c][FG[z]], add[x][w]] == w
                assert meets[add[c][v], add[x][v]] == w
                assert add[v][w] == w
                assert meets[add[c][F[z]], add[x][v]] == v
                assert add[v][add[c][F[z]]] == add[c][F[z]]
                assert add[add[c][v]][add[c][F[z]]] == add[c][F[z]]
                assert add[w][v] == v
                assert v == w
                triples += 1
            pairs += 1
    return triples, pairs, powers


def check():
    models = test_models()
    totals = [0, 0, 0]
    for add, operations in models:
        for index, count in enumerate(audit(add, operations)):
            totals[index] += count
    print(f'Alternating translations: {len(models)} models; '
          f'{totals[0]} proof triples, {totals[1]} ordered translation pairs, '
          f'{totals[2]} normal-form power checks. Both meet formulas, all '
          'intermediate bounds, the four-letter reductions, sandwich '
          'idempotence, and six-form closure passed. Completeness is not '
          'asserted.')


if __name__ == '__main__':
    check()
