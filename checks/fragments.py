"""Native reset/union and atom-preserving H reductions, without constants.

CNFs are tuples of clauses of (variable index, positive sign) literals.
The AST keeps native fragment operations, so size refers to the signature
being classified rather than an expansion into owned-choice syntax.
"""

from dataclasses import dataclass
from functools import reduce


@dataclass(frozen=True)
class Term:
    op: str
    args: tuple


def var(index):
    return Term('var', (index,))


def union(left, right):
    return Term('union', (left, right))


def reset(left, right):
    return Term('reset', (left, right))


def h(owner, root, left, right):
    return Term('h', (owner, root, left, right))


def denote(term, values):
    if term.op == 'var':
        return values[term.args[0]]
    if term.op == 'union':
        return denote(term.args[0], values) | denote(term.args[1], values)
    if term.op == 'reset':
        left, right = term.args
        value = denote(right, values)
        return value if value.bit_count() == 1 else denote(left, values) | value
    owner, root, left, right = term.args
    root = denote(root, values)
    if root.bit_count() == 1:
        return root
    left, right = denote(left, values), denote(right, values)
    choice = 1 << owner if left == 1 << owner or right == 1 << owner else left | right
    return root | choice


def right_comb(pieces, base, operation=reset):
    for piece in reversed(pieces):
        base = operation(piece, base)
    return base


def union_reduction(cnf, variables):
    assert variables >= 1
    t, z, c = (var(i) for i in range(2 * variables, 2 * variables + 3))
    rails = [var(i) for i in range(2 * variables)]
    base = right_comb(rails + [t], z)
    bad = [reset(reset(c, union(rails[2*i], t)), union(rails[2*i+1], t))
           for i in range(variables)]
    rhs = right_comb(bad, base)
    lhs = c
    for clause in cnf:
        guard = reduce(union, (rails[2*i + int(not sign)] for i, sign in clause), t)
        lhs = reset(lhs, guard)
    return reset(lhs, rhs), rhs


def h_reduction(cnf, variables, a=0, b=1):
    assert a != b
    z, c = var(variables), var(variables + 1)
    # x ◁ y = H_a(y,x,x): only the small left operand is duplicated.
    step = lambda left, right: h(a, right, left, left)
    base = right_comb([var(i) for i in range(variables)], z, step)
    branches = []
    for clause in cnf:
        branch = c
        for i, sign in reversed(clause):
            branch = h(a if sign else b, z, var(i), branch)
        branches.append(branch)
    rhs = right_comb(branches, base, step)
    return step(c, rhs), rhs


def colouring_identity(vertices):
    assert vertices >= 2
    xs = [var(i) for i in range(vertices)]
    z, c = var(vertices), var(vertices + 1)
    base = right_comb(xs, z)
    rhs = right_comb([reset(c, x) for x in xs], base)
    lhs = c
    for i in range(vertices):
        for j in range(i + 1, vertices):
            lhs = reset(lhs, union(xs[i], xs[j]))
    return reset(lhs, rhs), rhs


def size(term):
    if term.op == 'var':
        return 1
    return 1 + sum(size(t) for t in term.args if isinstance(t, Term))
