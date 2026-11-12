#!/usr/bin/env python3
"""Check one-pass target-cut failure on genuine canonical source probes.

No clone enumeration, generated invariant relation, or external package is used.
The finite search below enumerates only the explicitly specified target cuts.
"""
from itertools import combinations

ROLES = range(3)
ROW_NAMES = ("q", "A", "B", "C", "D")
# Nonempty sets are represented by their three-bit membership masks.
ROWS = (
    (2, 5, 1, 5),  # observer 1, source X
    (1, 4, 3, 1),  # observer 2, source Y
    (1, 3, 4, 1),  # observer 2, source Z
    (1, 4, 4, 4),  # observer 0, source X
    (2, 2, 1, 4),  # observer 2, source W
)
OBSERVERS = (1, 2, 2, 0, 2)
SOURCES = (0, 1, 2, 0, 3)
COLUMNS = tuple(tuple(row[j] for row in ROWS) for j in range(4))
A, B, C, D = (1, 2), (2, 2), (3, 0), (4, 2)
HEAD = frozenset((A, B, C, D))
PREMISE = (0, 1)


def member(value, role):
    return bool(value & (1 << role))


def clause_holds(value, premise, head):
    return (premise is not None and not member(value[premise[0]], premise[1])) or any(
        member(value[i], r) for i, r in head
    )


def sound(premise, head):
    return all(clause_holds(column, premise, head) for column in COLUMNS)


def block_head(cut, row, owner):
    return cut | frozenset((row, s) for s in ROLES if s != owner)


def blockers_sound(owner, cut, exposed):
    head = block_head(cut, exposed[0], owner)
    if owner == PREMISE[1]:
        return sound(None, head)
    return all(sound((PREMISE[0], s), head) for s in ROLES if s != owner)


def choice(owner, left, right):
    atom = 1 << owner
    return tuple(atom if x == atom or y == atom else x | y for x, y in zip(left, right))


def check():
    # Exact canonical provenance: source atom, passive other atom or complement.
    for row, observer, source in zip(ROWS, OBSERVERS, SOURCES):
        assert row[source] == 1 << observer
        allowed = {1 << s for s in ROLES if s != observer} | {7 ^ (1 << observer)}
        assert all(value in allowed for j, value in enumerate(row) if j != source)
        assert all(0 < value < 8 for value in row)
    assert sound(PREMISE, HEAD)

    # Boundary conditions for the canonical column-sound support predicate.
    for i in range(len(ROWS)):
        assert sound(None, frozenset((i, r) for r in ROLES))
    # Pure weakening and tautologies hold by the definition of clause_holds.

    counts = []
    for owner in ROLES:
        count = 0
        initial = frozenset(a for a in HEAD if a[1] == owner)
        for size in range(len(HEAD)):
            for elements in combinations(sorted(HEAD), size):
                cut = frozenset(elements)
                if not initial <= cut:
                    continue
                count += 1
                if owner == 0:
                    exposed = D if D not in cut else next(a for a in (A, B) if a not in cut)
                elif owner == 1:
                    exposed = next((a for a in (A, B, C) if a not in cut), D)
                else:
                    exposed = C
                assert exposed in HEAD - cut
                assert blockers_sound(owner, cut, exposed), (owner, cut, exposed)
        counts.append(count)
    assert counts == [7, 15, 1]

    x, _, z, w = COLUMNS
    inner = choice(0, z, w)
    result = choice(2, x, inner)
    assert inner == (1, 1, 1, 4, 1)
    assert result == (3, 1, 1, 4, 3)
    assert not clause_holds(result, PREMISE, HEAD)

    # A mandatory column-sound auxiliary blocker already fails on the inner term.
    owner2_cut = frozenset((A, B, D))
    blocker = block_head(owner2_cut, C[0], 2)
    assert sound((0, 0), blocker)
    assert not clause_holds(inner, (0, 0), blocker)
    print("Checked 5 canonical source probes, all 23 target cuts, and the explicit two-choice counterterm.")


if __name__ == "__main__":
    check()
