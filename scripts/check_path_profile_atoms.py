#!/usr/bin/env python3
"""Compute minimal two-owner realizations of the four-input path profile."""

from itertools import combinations, product

NAMES = "xyzw"
SIZE = len(NAMES)
FULL = (1 << SIZE) - 1
RESTRICTIONS = [
    (
        sum(1 << i for i, value in enumerate(values) if value == 1),
        sum(1 << i for i, value in enumerate(values) if value != 0),
    )
    for values in product((-1, 0, 1), repeat=SIZE)
]


def profile(winners):
    return sum(
        1 << coalition
        for coalition in range(FULL + 1)
        if any(coalition & winner == winner for winner in winners)
    )


def insert(antichain, marks, word):
    if any(old & marks == old for old in antichain):
        return False
    for old in list(antichain):
        if old & marks == marks:
            del antichain[old]
    antichain[marks] = word
    return True


def signature(word):
    """Return the Boolean profile and marks on the two-owner restrictions."""
    if isinstance(word, str):
        bit = 1 << NAMES.index(word)
        marks = sum(
            bit << (SIZE * j)
            for j, (lower, upper) in enumerate(RESTRICTIONS)
            if (lower ^ upper) & bit
        )
        return profile((bit,)), marks
    operator, left, right = word
    left_profile, left_marks = signature(left)
    right_profile, right_marks = signature(right)
    result = left_profile | right_profile if operator == "|" else left_profile & right_profile
    return result, (left_marks | right_marks) & nonconstant_mask(result)


def nonconstant_mask(table):
    return sum(
        FULL << (SIZE * j)
        for j, (lower, upper) in enumerate(RESTRICTIONS)
        if not (table & (1 << lower)) and table & (1 << upper)
    )


def main():
    profiles = {}
    for width in range(1, 7):
        for winners in combinations(range(1, FULL + 1), width):
            if any(a & b in (a, b) for a, b in combinations(winners, 2)):
                continue
            profiles[profile(winners)] = {}
    assert len(profiles) == 166
    masks = {table: nonconstant_mask(table) for table in profiles}
    for name in NAMES:
        table, marks = signature(name)
        profiles[table][marks] = name

    profile_pairs = list(combinations(profiles, 2))
    while True:
        changed = False
        for left, right in profile_pairs:
            for operator, target in (("|", left | right), ("&", left & right)):
                # The equal-profile child already gives a smaller signature.
                if target in (left, right):
                    continue
                for left_marks, left_word in profiles[left].items():
                    for right_marks, right_word in profiles[right].items():
                        marks = (left_marks | right_marks) & masks[target]
                        if insert(profiles[target], marks, (operator, left_word, right_word)):
                            changed = True
        if not changed:
            break

    path = profile((0b0011, 0b0110, 0b1100))
    examples = [
        ("&", ("|", ("&", "w", "z"), "y"), ("|", "z", "x")),
        ("&", ("|", "z", ("&", "y", "x")), ("|", "w", "y")),
        ("&", ("|", "z", ("&", "y", "x")), ("|", ("&", "w", "z"), "y")),
        ("|", ("&", ("|", "z", "x"), "y"), ("&", "w", "z")),
        ("|", ("&", ("|", "w", "y"), "z"), ("&", "y", "x")),
    ]
    assert {(path, marks) for marks in profiles[path]} == {signature(word) for word in examples}
    assert len(profiles[path]) == 5
    print("5 minimal two-owner realizations of the four-input path profile")


if __name__ == "__main__":
    main()
