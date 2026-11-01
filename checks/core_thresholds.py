"""Explicit HSP witnesses for core atoms with a chain of marker values.

The arbitrary-size proof is in appendix-core-basis.tex. Owners are 0..K-1,
and markers n_0,...,n_l are K,...,K+l. These functions construct the stated
algebra and its source; they do not search for identities or certificates.
"""

from itertools import product


def threshold_join(owners, x, y):
    if x == y:
        return x
    return max(owners, x, y)


def threshold_own(thresholds, owner, x, y):
    owners = len(thresholds)
    if owner in (x, y):
        other = y if x == owner else x
        if other < owners or other - owners <= thresholds[owner]:
            return owner
    return threshold_join(owners, x, y)


def threshold_certificate(thresholds, levels):
    """Source in A_K^at times l copies of a single proper-owner factor.

    Coordinate zero is the atomic quotient. Each other coordinate is an
    observer factor, with n=K and p=K+1. A source state is determined by
    its atomic coordinate and its set of p coordinates.
    """
    owners = len(thresholds)
    assert owners >= 3 and min(thresholds) == 0
    assert all(0 <= t <= levels for t in thresholds)
    omitted = thresholds.index(0)
    source, images = [], []
    for base in range(owners + 1):
        for bits in product((False, True), repeat=levels):
            if base < owners and any(bits[h - 1] for h in range(1, thresholds[base] + 1)):
                continue
            coordinates = tuple(
                base if base < owners and h <= thresholds[base]
                else owners + int(bits[h - 1])
                for h in range(1, levels + 1))
            high = max((h for h in range(1, levels + 1) if bits[h - 1]), default=0)
            source.append((base,) + coordinates)
            images.append(owners + high if high else base)
    return omitted, tuple(source), tuple(images)
