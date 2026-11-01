"""Core basis constructions, without a claim of a complete finite basis.

The extra-marker algebra has one absorbing atom for every owner and two
unabsorbed levels. Its small generated subalgebras are quotients of the
winner-set algebra, but it fails the owner-exhaustion identity.
"""

from dataclasses import dataclass
from functools import reduce

from fragments import owned, union, var


def marker_join(count, left, right):
    if left == right:
        return left
    return max(count, left, right)


def marker_own(count, owner, left, right):
    if left == owner or right == owner:
        return owner
    return marker_join(count, left, right)


def deletion_quotient(count, omitted, value):
    """Omit high=count+1, or an atom; value is a nonempty winner bitmask."""
    if omitted < count and value & (1 << omitted):
        return count + 1
    if value.bit_count() == 1:
        return value.bit_length() - 1
    return count


def exhaustion_identity(count):
    """The K+1-variable identity c + sum_i(c *_i x_i) = sum_i(c *_i x_i)."""
    marker = var(count)
    cover = reduce(union, (owned(i, marker, var(i)) for i in range(count)))
    return union(marker, cover), cover


@dataclass(frozen=True)
class BinaryProfile:
    """Variable support, and singleton-winning owners for each input.

    Support bits 1 and 2 stand for x and y. For support 3, the two owner
    masks are either one-sided, or both the same singleton mask.
    """

    support: int
    left: int
    right: int


def binary_profiles(count):
    full = (1 << count) - 1
    return ([BinaryProfile(1, full, 0), BinaryProfile(2, 0, full),
             BinaryProfile(3, 0, 0)]
            + [BinaryProfile(3, a, 0) for a in range(1, full + 1)]
            + [BinaryProfile(3, 0, a) for a in range(1, full + 1)]
            + [BinaryProfile(3, 1 << i, 1 << i) for i in range(count)])


def binary_product(owner, left, right):
    bit = 1 << owner

    def combine(a, b):
        return (a & b) | ((a | b) & bit)

    return BinaryProfile(left.support | right.support,
                         combine(left.left, right.left),
                         combine(left.right, right.right))


def binary_value(profile, x, y):
    if profile.support == 1:
        return x
    if profile.support == 2:
        return y
    if x.bit_count() == 1 and profile.left & x:
        return x
    if y.bit_count() == 1 and profile.right & y:
        return y
    return x | y


def binary_term(count, profile):
    x, y = var(0), var(1)
    if profile.support == 1:
        return x
    if profile.support == 2:
        return y
    if profile.left and profile.right:
        assert profile.left == profile.right and profile.left.bit_count() == 1
        return owned(profile.left.bit_length() - 1, x, y)
    term = union(x, y)
    source, owners = (x, profile.left) if profile.left else (y, profile.right)
    for i in range(count):
        if owners & (1 << i):
            term = owned(i, source, term)
    return term
