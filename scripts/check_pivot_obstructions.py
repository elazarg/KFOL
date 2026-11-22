#!/usr/bin/env python3
"""Classify nonconstant monotone profiles on five inputs by envelope realizability."""

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


def dropping_steps(table):
    steps = []
    for coalition in range(FULL + 1):
        if not table[coalition]:
            continue
        for bit in bits(coalition):
            remainder = coalition ^ bit
            for loser in subsets(remainder):
                if table[loser | bit]:
                    continue
                if all(table[loser | extra] for extra in bits(remainder ^ loser)):
                    steps.append((coalition, remainder))
                    break
    return steps


def root_obstructed(table, steps):
    winners = minimal_winners(table)
    successors = {
        coalition: {coalition | bit for bit in bits(FULL ^ coalition)}
        for coalition in range(FULL + 1)
        if table[coalition]
    }
    for start, end in steps:
        successors[start].add(end)

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


def table_mask(table):
    return sum(1 << a for a, win in enumerate(table) if win)


def constructible_profiles(tables, steps):
    """Close the projections under the sufficient disjunction and duality rules."""
    masks = {table_mask(table): table for table in tables}
    drops = {
        mask: [(1 << start, 1 << end) for start, end in steps[table]]
        for mask, table in masks.items()
    }
    dual_masks = {mask: table_mask(dual(table)) for mask, table in masks.items()}
    ordered = sorted(masks, key=int.bit_count)
    constructible = {table_mask(truth_table((bit,))) for bit in bits(FULL)}

    while True:
        before = len(constructible)
        for parent in ordered:
            if parent in constructible:
                continue
            covered = 0
            for child in constructible:
                if child & ~parent:
                    continue
                if any(child & start and not child & end for start, end in drops[parent]):
                    continue
                covered |= child
                if covered == parent:
                    break
            if covered == parent:
                constructible.update((parent, dual_masks[parent]))
        if len(constructible) == before:
            return {masks[mask] for mask in constructible}


def main():
    relabelings = [
        tuple(sum(1 << perm[i] for i in range(VARIABLES) if a & (1 << i))
              for a in range(FULL + 1))
        for perm in permutations(range(VARIABLES))
    ]
    tables = {
        truth_table(winners): winners
        for winners in antichains(list(range(1, FULL + 1)))
        if winners
    }
    steps = {table: dropping_steps(table) for table in tables}
    constructible = constructible_profiles(tables, steps)
    obstructed = set()
    seen = set()
    obstructions = []
    for table, winners in tables.items():
        if table in seen:
            continue
        other = dual(table)
        orbit = {
            tuple(profile[a] for a in relabeling)
            for profile in (table, other)
            for relabeling in relabelings
        }
        seen.update(orbit)
        if path_restriction(table):
            obstructed.update(orbit)
        elif all(any(table[a] != table[a ^ bit] for a in range(FULL + 1))
                 for bit in bits(FULL)):
            if root_obstructed(table, steps[table]) and root_obstructed(other, steps[other]):
                obstructed.update(orbit)
                obstructions.append(winners)

    assert not constructible & obstructed
    assert constructible | obstructed == set(tables)
    assert (len(constructible), len(obstructed)) == (4075, 3504)
    print(f"{len(constructible)} realizable and {len(obstructed)} obstructed profiles")

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
