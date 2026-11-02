"""Explicit atomic basis and its finite uniform lifts to the core.

Completeness over arbitrary algebras is proved in appendix-core-basis.tex.
Union and reset are term abbreviations, not additional core operations.
"""

from functools import reduce
from itertools import combinations

from fragments import owned, reset, union, var


def variables(term):
    if term.op == 'var':
        return {term.args[0]}
    args = term.args[1:] if term.op == 'owned' else term.args
    return set().union(*(variables(t) for t in args))


def semilattice_laws(operation, name):
    x, y, z = map(var, range(3))
    return [
        (name + '_idempotent', operation(x, x), x),
        (name + '_commutative', operation(x, y), operation(y, x)),
        (name + '_associative', operation(operation(x, y), z),
         operation(x, operation(y, z))),
    ]


def atomic_basis(owners):
    assert owners >= 3
    x, y, z = map(var, range(3))
    operations = [union] + [lambda x, y, i=i: owned(i, x, y)
                            for i in range(owners)]
    result = []
    for i, operation in enumerate(operations):
        result += semilattice_laws(operation, f'semilattice_{i}')
    for i, outer in enumerate(operations):
        for j, inner in enumerate(operations):
            if i != j:
                result.append((f'distributive_{i}_{j}', outer(x, inner(y, z)),
                               inner(outer(x, y), outer(x, z))))
    for i, j in combinations(range(owners), 2):
        result.append((f'coverage_{i}_{j}',
                       union(owned(i, x, y), owned(j, x, y)), union(x, y)))
    result.append(('reset_projection', reset(x, y), y))
    return result


def bounded_lift(left, right):
    used = sorted(variables(left) | variables(right))
    bound = reduce(union, map(var, used), var(max(used) + 1))
    return reset(bound, left), reset(bound, right)


def lifting_basis(owners):
    x, y, z = map(var, range(3))
    result = semilattice_laws(union, 'join')
    for i in range(owners):
        result.append((f'upper_bound_{i}',
                       union(owned(i, x, y), union(x, y)), union(x, y)))
    bound = union(x, y)
    qx = reset(bound, x)
    result += [
        ('normalizer_extensive', union(x, qx), qx),
        ('normalizer_bounded', union(bound, qx), bound),
        ('normalizer_idempotent', reset(bound, qx), qx),
    ]
    bound = union(union(x, y), z)
    for i in range(owners):
        result.append((f'normalizer_compatible_{i}', reset(bound, owned(i, x, y)),
                       reset(bound, owned(i, reset(bound, x), reset(bound, y)))))
    for name, left, right in atomic_basis(owners):
        result.append(('lift_' + name, *bounded_lift(left, right)))
    return result


def expand_core(term, owners):
    """Eliminate both abbreviations, keeping identical subterms shared."""
    cache = {}

    def expand(t):
        if t in cache:
            return cache[t]
        if t.op == 'var':
            result = t
        elif t.op == 'owned':
            i, left, right = t.args
            result = owned(i, expand(left), expand(right))
        else:
            left, right = map(expand, t.args)
            result = owned(2, owned(0, left, right), owned(1, left, right))
            if t.op == 'reset':
                for i in range(owners):
                    result = owned(i, right, result)
            else:
                assert t.op == 'union'
        cache[t] = result
        return result

    return expand(term)
