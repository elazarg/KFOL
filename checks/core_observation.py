"""Doubled ladders with arbitrarily large reset-observation depth.

The arbitrary-length HSP and depth proofs are in appendix-core-basis.tex.
An element is (x, bit), with x coded as in core_ladders. The single
omitted element is (c_0, 0). Only owners 0 and 1 can differ from join.
"""

from core_ladders import ladder_join, ladder_own


def carrier(length):
    assert length >= 1
    return tuple((x, bit) for x in range(2 * length + 1) for bit in (0, 1)
                 if (x, bit) != (length, 0))


def doubled_join(length, x, y):
    if {x, y} == {(0, 1), (length, 1)}:
        return length + 1, 1
    return ladder_join(length, x[0], y[0]), max(x[1], y[1])


def doubled_own(length, owner, x, y):
    if owner >= 2:
        return doubled_join(length, x, y)
    if owner == 1 and {x, y} == {(0, 1), (length, 1)}:
        return length + 1, 1
    bit = min(x[1], y[1]) if owner == 0 else max(x[1], y[1])
    return ladder_own(length, owner, x[0], y[0]), bit


def tables(length):
    values = carrier(length)
    indices = {x: i for i, x in enumerate(values)}
    add = [[indices[doubled_join(length, x, y)] for y in values] for x in values]
    operations = [[[indices[doubled_own(length, i, x, y)] for y in values]
                   for x in values] for i in range(3)]
    return values, indices, add, operations


def step_certificate(length):
    """S <= A_length x B_(length mod 2), with its onto map to A_(length+1).

    The new three-element factor uses 0 for its atom, 1 for n, and 2 for p.
    S contains every (x,n), (x,p), and the two ((c_length,bit),atom).
    """
    mapping = {}
    for x, bit in carrier(length):
        # Preserve the names of old atoms and markers in the larger ladder.
        old_image = x if x < length else x + 1
        mapping[((x, bit), 1)] = old_image, bit
        mapping[((x, bit), 2)] = 2 * (length + 1), bit
    for bit in (0, 1):
        mapping[((2 * length, bit), 0)] = length, bit
    return mapping
