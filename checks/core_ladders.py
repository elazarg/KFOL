"""Alternating ladders and their explicit product/quotient representation.

The arbitrary-length proof is in appendix-core-basis.tex. The ladder has
atoms a_0,...,a_(r-1), coded 0,...,r-1, and markers c_0,...,c_r, coded
r,...,2r. Only owners 0 and 1 differ from join.
"""

from itertools import product


def level(r, x):
    return x if x < r else x - r


def ladder_join(r, x, y):
    return x if x == y else r + max(level(r, x), level(r, y))


def ladder_own(r, owner, x, y):
    absorbers = [a for a, b in ((x, y), (y, x))
                 if a < r and a % 2 == owner and level(r, b) <= a + 1]
    return max(absorbers) if absorbers else ladder_join(r, x, y)


def ladder_certificate(r):
    """Subalgebra of r three-element core subalgebras, and its onto map.

    In coordinate j, 0 is the owner-(j mod 2) atom, 1 is n, and 2 is p.
    """
    assert r >= 1
    source, images = [], []
    for vector in product(range(3), repeat=r):
        if any(vector[j] == 0 and vector[j - 1] != 2 for j in range(1, r)):
            continue
        last = max((j for j, value in enumerate(vector) if value != 1), default=-1)
        target = r if last < 0 else last if vector[last] == 0 else r + last + 1
        source.append(vector)
        images.append(target)
    return tuple(source), tuple(images)
