"""Check the four-input obstruction to compatible comparisons and joins."""

from itertools import product


OWNERS = range(3)
HOLE = -1
INPUT_COUNT = 4


def owned_choice(owner, left, right):
    atom = 1 << owner
    return atom if atom in (left, right) else left | right


def baseline(menus):
    u, x, v, z = menus
    left = owned_choice(0, u, x)
    right = owned_choice(2, x, v)
    return owned_choice(0, owned_choice(1, left, right), z)


def captured_inputs(coloring):
    observer = next(owner for owner in OWNERS if owner not in coloring)
    mark = 1 << observer
    neutral = ((1 << len(OWNERS)) - 1) ^ mark
    menus = [neutral if owner == HOLE else 1 << owner for owner in coloring]
    captured = set()
    for head, owner in enumerate(coloring):
        if owner == HOLE:
            probe = menus.copy()
            probe[head] = mark
            if not baseline(probe) & mark:
                captured.add(head)
    return captured


def compatible_comparison(lower, upper, captured):
    return all(
        color == HOLE or color == upper[index]
        or (upper[index] == HOLE and index in captured)
        for index, color in enumerate(lower)
    )


def check():
    colorings = [
        coloring for coloring in product((HOLE, *OWNERS), repeat=INPUT_COUNT)
        if any(owner not in coloring for owner in OWNERS)
    ]
    indices = {coloring: index for index, coloring in enumerate(colorings)}
    monochromatic = [
        {
            indices[tuple(color if color == owner else HOLE for color in coloring)]
            for owner in OWNERS
        }
        for coloring in colorings
    ]
    relation = []
    for upper in colorings:
        captured = captured_inputs(upper)
        relation.append({
            index for index, lower in enumerate(colorings)
            if compatible_comparison(lower, upper, captured)
        })

    while True:
        extended = []
        for predecessors in relation:
            closed = predecessors.union(*(relation[index] for index in predecessors))
            closed.update(
                index for index, blocks in enumerate(monochromatic)
                if blocks <= closed
            )
            extended.append(closed)
        if extended == relation:
            break
        relation = extended

    lower = indices[(HOLE, 1, HOLE, 1)]
    upper = indices[(0, 0, 0, 0)]
    assert len(colorings) == 196
    assert sum(map(len, relation)) == 13465
    assert lower not in relation[upper]
    print("Compatible comparisons and monochromatic joins omit the tested pair.")


if __name__ == "__main__":
    check()
