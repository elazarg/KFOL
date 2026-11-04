"""Unitize a two-owner algebra and eliminate a named unit from equations.

The finite-basis transfer is proved in appendix-core-basis.tex. This module
implements that transfer; it does not supply a basis for the four-element
pointed algebra.
"""

from itertools import product

from core_atomic_basis import variables
from fragments import Term, owned, union


UNIT = Term('unit', ())


def unitize(tables):
    """Tables are ordered as join, first choice, second choice.

    Old elements are 0..n-1, barred elements n..2n-1, and the new unit 2n.
    The definition works for arbitrary binary tables, including noncommutative
    ones; the theorem subsequently characterizes membership in the variety.
    """
    add, first, second = tables
    n = len(add)
    unit = 2 * n

    def plus(x, y):
        if x == unit:
            return unit if y == unit else n + y % n
        if y == unit:
            return n + x % n
        return (n if x >= n or y >= n else 0) + add[x % n][y % n]

    def f(x, y):
        if x == unit:
            return y
        if y == unit:
            return x
        a, b = x % n, y % n
        if x >= n and y >= n:
            return n + add[a][b]
        if x >= n:
            return add[b][first[a][b]]
        if y >= n:
            return add[a][first[a][b]]
        return first[a][b]

    def g(x, y):
        if x == unit or y == unit:
            return unit
        return (n if x >= n or y >= n else 0) + second[x % n][y % n]

    carrier = range(unit + 1)
    return [[[op(x, y) for y in carrier] for x in carrier] for op in (plus, f, g)]


def tagged_term(term, forms):
    """Return (tag, payload): 0=old, 1=barred, 2=new unit (no payload)."""
    if term.op == 'unit':
        return 2, None
    if term.op == 'var':
        tag = forms[term.args[0]]
        return tag, None if tag == 2 else term
    if term.op == 'union':
        left, right = term.args
        owner = None
    elif term.op == 'owned':
        owner, left, right = term.args
        assert owner in (0, 1)
    else:
        raise ValueError(f'unsupported operation {term.op}')
    r, a = tagged_term(left, forms)
    s, b = tagged_term(right, forms)
    if owner == 0:
        if r == 2:
            return s, b
        if s == 2:
            return r, a
        if r == s == 1:
            return 1, union(a, b)
        value = owned(0, a, b)
        if r == 1:
            value = union(b, value)
        elif s == 1:
            value = union(a, value)
        return 0, value
    if owner == 1:
        return (2, None) if 2 in (r, s) else (max(r, s), owned(1, a, b))
    if r == s == 2:
        return 2, None
    if r == 2:
        return 1, b
    if s == 2:
        return 1, a
    return max(r, s), union(a, b)


def eliminate_unit(equations):
    """Translate (left, right) equations; incompatible tags reject the input.

    Equations valid in the pointed four-element generator always have matching
    tags, by its unitization embedding. No new variables or constants occur.
    """
    result = []
    for left, right in equations:
        used = sorted(variables(left) | variables(right))
        for assignment in product(range(3), repeat=len(used)):
            forms = dict(zip(used, assignment))
            ltag, lhs = tagged_term(left, forms)
            rtag, rhs = tagged_term(right, forms)
            if ltag != rtag:
                raise ValueError('the two sides have incompatible unitization tags')
            if ltag != 2:
                result.append((lhs, rhs))
    return result


def evaluate(term, values, tables, unit=None):
    if term.op == 'var':
        return values[term.args[0]]
    if term.op == 'unit':
        assert unit is not None
        return unit
    if term.op == 'union':
        operation, (left, right) = 0, term.args
    elif term.op == 'owned':
        owner, left, right = term.args
        operation = owner + 1
    else:
        raise ValueError(f'unsupported operation {term.op}')
    return tables[operation][evaluate(left, values, tables, unit)][
        evaluate(right, values, tables, unit)]
