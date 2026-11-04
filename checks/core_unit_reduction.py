"""Finite equations for the reduction to a named left reset unit.

These equations follow from the three-variable laws Gamma_K, but are not
asserted to be a basis for the core. The derivation and basis-transfer
theorem are proved in appendix-core-basis.tex.
"""

from core_atomic_basis import semilattice_laws
from fragments import owned, reset, union, var


def unit_reduction_laws(owners):
    c, x, y = map(var, range(3))
    result = semilattice_laws(union, 'join')
    result += [
        ('reset_idempotent', reset(x, x), x),
        ('left_reset_extensive', union(x, reset(c, x)), reset(c, x)),
        ('left_reset_idempotent', reset(c, reset(c, x)), reset(c, x)),
    ]
    for i in range(owners):
        result.append((f'left_reset_nucleus_{i}', reset(c, owned(i, x, y)),
                       reset(c, owned(i, reset(c, x), reset(c, y)))))
    return result


def unit_lift(left, right, root):
    """Replace the named constant by root before calling this function."""
    return reset(root, left), reset(root, right)
