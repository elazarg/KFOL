#!/usr/bin/env python3
"""Enumerate the five-input minimal obstructions certified by the root test."""

from itertools import permutations

VARIABLES = 5
FULL = (1 << VARIABLES) - 1


def subsets(mask):
    subset = mask
    while True:
        yield subset
        if subset == 0:
            return
        subset = (subset - 1) & mask


def bits(mask):
    return (1 << i for i in range(VARIABLES) if mask & (1 << i))


def antichains(available):
    if not available:
        yield ()
        return
    first, *rest = available
    yield from antichains(rest)
    incomparable = [other for other in rest if first & other not in (first, other)]
    for tail in antichains(incomparable):
        yield (first, *tail)


def truth_table(winners):
    return tuple(any(a & winner == winner for winner in winners) for a in range(FULL + 1))


def minimal_winners(table):
    return tuple(
        a for a in range(FULL + 1)
        if table[a] and all(not table[a ^ bit] for bit in bits(a))
    )


def dual(table):
    return tuple(not table[FULL ^ a] for a in range(FULL + 1))


def path_restriction(table):
    for fixed in bits(FULL):
        for value in (0, fixed):
            restricted = tuple(
                table[(a & ~fixed) | value] for a in range(FULL + 1)
            )
            edges = minimal_winners(restricted)
            if len(edges) != 3 or any(edge.bit_count() != 2 for edge in edges):
                continue
            degrees = sorted(
                sum(bool(edge & bit) for edge in edges)
                for bit in bits(FULL ^ fixed)
            )
            if degrees == [1, 1, 2, 2]:
                return True
    return False


def root_obstructed(table):
    winners = minimal_winners(table)
    successors = {}
    for coalition in range(FULL + 1):
        if not table[coalition]:
            continue
        next_coalitions = {coalition | bit for bit in bits(FULL ^ coalition)}
        for bit in bits(coalition):
            remainder = coalition ^ bit
            for loser in subsets(remainder):
                if table[loser | bit]:
                    continue
                if all(table[loser | extra] for extra in bits(remainder ^ loser)):
                    next_coalitions.add(remainder)
                    break
        successors[coalition] = next_coalitions

    for seed in winners:
        reached = {seed}
        pending = [seed]
        while pending:
            next_coalitions = successors[pending.pop()] - reached
            reached.update(next_coalitions)
            pending.extend(next_coalitions)
        if all(winner in reached for winner in winners):
            return True
    return False


def main():
    relabelings = [
        tuple(sum(1 << perm[i] for i in range(VARIABLES) if a & (1 << i))
              for a in range(FULL + 1))
        for perm in permutations(range(VARIABLES))
    ]
    seen = set()
    obstructions = []
    for winners in antichains(list(range(1, FULL + 1))):
        if not winners:
            continue
        table = truth_table(winners)
        if table in seen:
            continue
        other = dual(table)
        for profile in (table, other):
            seen.update(tuple(profile[a] for a in relabeling) for relabeling in relabelings)
        if not all(any(table[a] != table[a ^ bit] for a in range(FULL + 1))
                   for bit in bits(FULL)):
            continue
        if not path_restriction(table) and root_obstructed(table) and root_obstructed(other):
            obstructions.append(winners)

    expected = [
        (11, 12, 18, 21), (12, 19, 21, 22, 24),
        (13, 14, 18, 21, 24), (13, 14, 18, 21, 25),
        (13, 14, 19, 20, 24), (14, 17, 20, 24),
        (14, 19, 20, 24), (14, 21, 22, 24),
    ]
    assert sorted(obstructions) == expected, sorted(obstructions)
    print(f"{len(obstructions)} five-input obstruction classes")


if __name__ == "__main__":
    main()
