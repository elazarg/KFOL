"""Independent soundness and path-certificate checks for the full finite basis.

The cardinality-independent equational completeness proof is written in
appendix-owner-basis.tex. Lean proves soundness and completeness for the thirty-six native identities.
"""

from itertools import product
from random import Random

from check_one_owner import arbitrary
from check_owner_synthesis import tables
from fragments import denote, h, reset, var
from one_owner import admissible, normal, synthesize
from owner_basis import (BASIS, FIVE_VARIABLE_BASIS, absorption_certificate, join_words, root,
                         variables, words)


def compare(left, right, arity):
    assert normal(left, 0, arity) == normal(right, 0, arity)
    base = root(left)
    assert base == root(right)
    first, second = words(left, base), words(right, base)
    absorption_certificate(first, second, base)
    absorption_certificate(second, first, base)



def canonical_identity(left, right):
    """Exact alpha/orientation key, with one variable map across both sides.

    First occurrence gives a canonical name to each actual variable. The
    fixed owner label is an operation parameter, never a renamable variable.
    Taking both orientations also identifies an equation with its reverse.
    """
    def oriented(first, second):
        names = {}

        def encode(term):
            if term.op == 'var':
                original = term.args[0]
                if original not in names:
                    names[original] = len(names)
                return ('var', names[original])
            if term.op == 'reset':
                return ('reset', *(encode(child) for child in term.args))
            assert term.op == 'h', term.op
            return ('h', term.args[0], *(encode(child) for child in term.args[1:]))

        return encode(first), encode(second)

    return min(oriented(left, right), oriented(right, left))


def check_four_variable_obstruction():
    """Check full laws on the six-element witness, then its local cover.

    This checks a finite certificate for the entire four-variable theory:
    completeness of BASIS turns its closed local models into full models.
    It does not enumerate terms to a fixed depth.
    """
    from itertools import combinations
    from check_owner_presentation import evaluate

    reset_table = [
        [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5],
        [5, 1, 2, 3, 4, 5], [5, 1, 2, 3, 4, 5],
        [4, 1, 4, 4, 4, 4], [5, 1, 2, 3, 4, 5],
    ]
    root_zero = [
        [0, 0, 5, 5, 4, 5], [0, 0, 5, 5, 5, 5],
        [5, 5, 5, 0, 4, 5], [5, 5, 0, 5, 4, 5],
        [4, 5, 4, 4, 4, 4], [5, 5, 5, 5, 4, 5],
    ]

    def guarded(x, y, z):
        if x == 0:
            return root_zero[y][z]
        if x in (1, 4):
            return x
        return 4 if (y == 4 or z == 4) and y != 1 and z != 1 else x

    guarded_table = [[[guarded(x, y, z) for z in range(6)]
                      for y in range(6)] for x in range(6)]
    local = [set(range(6)) - {e} for e in range(5)]
    for subset in local:
        assert all(reset_table[x][y] in subset for x, y in product(subset, repeat=2))
        assert all(guarded(x, y, z) in subset for x, y, z in product(subset, repeat=3))
    assert all(any(set(xs) <= subset for subset in local)
               for xs in combinations(range(6), 4))

    failures = []
    for name, left, right in BASIS:
        names = sorted(variables(left) | variables(right))
        for xs in product(range(6), repeat=len(names)):
            env = dict(zip(names, xs))
            lhs = evaluate(left, env, reset_table, guarded_table)
            rhs = evaluate(right, env, reset_table, guarded_table)
            if lhs != rhs:
                failures.append((name, xs, lhs, rhs))
                assert not any(set(xs) <= subset for subset in local)
    assert failures == [('F_band', (0, 0, 1, 2, 3, 4), 0, 5),
                        ('F_band', (0, 0, 1, 3, 2, 4), 0, 5)]
    print('Four-variable obstruction: five closed local models cover every '
          'four inputs; the only two basis failures are the action-band law.')


def check():
    check_four_variable_obstruction()
    assert len(BASIS) == 36
    assert len({(left, right) for _, left, right in BASIS}) == 36
    canonical = {}
    for name, left, right in BASIS:
        key = canonical_identity(left, right)
        assert key not in canonical, (canonical.get(key), name)
        canonical[key] = name
    assert len(canonical) == 36
    valuations = 0
    for name, left, right in BASIS:
        names = sorted(variables(left) | variables(right))
        assert len(names) <= 6
        assert normal(left, 0, 7) == normal(right, 0, 7), name
        for values in product((1, 2, 3, 7), repeat=len(names)):
            env = dict(zip(names, values))
            assert denote(left, env) == denote(right, env), (name, env)
            valuations += 1

    # Independently check the five-variable replacement, with one alpha map
    # shared by the two sides of each equation.
    assert len(FIVE_VARIABLE_BASIS) == 36
    assert len({canonical_identity(left, right)
                for _, left, right in FIVE_VARIABLE_BASIS}) == 36
    five_valuations = 0
    for name, left, right in FIVE_VARIABLE_BASIS:
        names = sorted(variables(left) | variables(right))
        assert len(names) <= 5
        assert normal(left, 0, 7) == normal(right, 0, 7), name
        for values in product((1, 2, 3, 7), repeat=len(names)):
            env = dict(zip(names, values))
            assert denote(left, env) == denote(right, env), (name, env)
            five_valuations += 1
    assert five_valuations == 7188
    print('Five-variable presentation: 36 distinct equations; exchange and '
          f'all retained laws passed on {five_valuations} native valuations.')

    # The weak-companion branch needs four distinct variables. Here the
    # source-2 witness has a prefix F_13, whose second index is the target
    # companion 3, outside N(G_1). This exercises PQ = PK_3 in the proof.
    prefix = ((1, 1),)
    upper = (prefix, ((1, 3), (2, 1)))
    target = (prefix + ((2, 3),),)
    compare(join_words(upper, 0), join_words(upper + target, 0), 4)
    certificate = absorption_certificate(upper, target, 0)
    assert certificate[-1][2] == (('pair', 2), ('source', 3))

    representatives = {}
    for base in range(3):
        for form in tables(3, base):
            if admissible(form):
                representatives[form] = synthesize(form)
    assert len(representatives) == 27
    terms = tuple(representatives.values())
    products = 0
    for left, right in product(terms, repeat=2):
        term = reset(left, right)
        compare(term, representatives[normal(term, 0, 3)], 3)
        products += 1
    for first, left, right in product(terms, repeat=3):
        term = h(0, first, left, right)
        compare(term, representatives[normal(term, 0, 3)], 3)
        products += 1

    rng = Random(406)
    sampled = 0
    for arity in (4, 6, 8):
        for _ in range(80):
            term = arbitrary(rng, arity, 0, 4)
            form = normal(term, 0, arity)
            compare(term, synthesize(form), arity)
            external = rng.randrange(arity)
            projected = reset(term, var(external))
            expanded = join_words(words(term, external), external)
            assert normal(projected, 0, arity) == normal(expanded, 0, arity)
            for _ in range(4):
                env = tuple(rng.choice((1, 2, 3, 7)) for _ in range(arity))
                assert denote(projected, env) == denote(expanded, env)
            sampled += 1

    print(f'Full one-owner basis: 36 equations, distinct up to variable renaming '
          f'and reversal, on {valuations} native valuations; '
          f'two-source certificates for all {products} products of the free '
          f'three-generated algebra and {sampled} larger sampled identities passed.')



if __name__ == '__main__':
    check()
