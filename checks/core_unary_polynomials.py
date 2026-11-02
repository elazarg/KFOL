"""Exact unary polynomial profiles of the core generator, with fixed parameters.

This is a semantic classification on C_K, not a derivation from the
candidate basis in arbitrary models. The generic proof is in the TR.
"""

from dataclasses import dataclass
from itertools import product

from fragments import owned, union, var


@dataclass(frozen=True)
class UnaryProfile:
    increment: int
    atomic: tuple


def subsets(mask):
    subset = mask
    while True:
        yield subset
        if not subset:
            return
        subset = (subset - 1) & mask


def profiles(owners):
    for increment in range(1 << owners):
        for atomic in product(*(subsets(increment & ~(1 << i)) for i in range(owners))):
            yield UnaryProfile(increment, atomic)


def value(profile, winner_set):
    if winner_set.bit_count() == 1:
        return winner_set | profile.atomic[winner_set.bit_length() - 1]
    return winner_set | profile.increment


def synthesize(profile):
    """Variable 0 is the input; variable j+1 is the fixed singleton {j}."""
    x = var(0)
    result = x
    for j in range(len(profile.atomic)):
        if not profile.increment & (1 << j):
            continue
        branch = union(x, var(j + 1))
        for i, extra in enumerate(profile.atomic):
            if i != j and not extra & (1 << j):
                branch = owned(i, x, branch)
        result = union(result, branch)
    return result
