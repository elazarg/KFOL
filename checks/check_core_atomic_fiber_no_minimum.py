#!/usr/bin/env python3
"""Exact native-subpower obstruction to least atomic-fiber representatives.

Values are alpha=0, beta=1, n=2, p=3. The generated subalgebra includes
all four constant vectors, hence also absorbers for unused owners.
No search cutoff or external solver is used.
"""

from itertools import product

JOIN = ((0, 2, 2, 3), (2, 1, 2, 3), (2, 2, 2, 3), (3, 3, 3, 3))
F = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 2, 3), (0, 3, 3, 3))
G = ((0, 1, 2, 3), (1, 1, 1, 1), (2, 1, 2, 3), (3, 1, 3, 3))
COORDINATES = (
    (2, 1, 3, 0), (1, 2, 0, 3), (0, 1, 0, 0),
    (0, 1, 0, 1), (1, 0, 1, 0), (0, 0, 1, 1),
    (2, 0, 1, 3), (0, 2, 3, 1), (2, 3, 1, 0),
)


def sides(values):
    x, y, z, w = values
    return G[F[x][G[y][z]]][F[y][w]], G[F[y][G[x][w]]][F[x][z]]


def atomic(value):
    return min(value, 2)


def main():
    for values in product(range(4), repeat=4):
        left, right = sides(values)
        assert atomic(left) == atomic(right)

    left = bytes(sides(values)[0] for values in COORDINATES)
    right = bytes(sides(values)[1] for values in COORDINATES)
    allowed = [
        {v for v in range(4)
         if atomic(v) == atomic(a) and JOIN[v][a] == a and JOIN[v][b] == b}
        for a, b in zip(left, right)
    ]
    assert all(len(values) == 1 for values in allowed)
    required = bytes(next(iter(values)) for values in allowed)
    assert required == bytes((2, 2, 0, 1, 1, 0, 2, 2, 2))

    generators = [bytes(values[i] for values in COORDINATES) for i in range(4)]
    generators += [bytes([value] * len(COORDINATES)) for value in range(4)]
    states = list(dict.fromkeys(generators))
    seen = set(states)
    position = 0
    entries = 0
    while position < len(states):
        a = states[position]
        for b in states[:position + 1]:
            for table in (JOIN, F, G):
                value = bytes(table[x][y] for x, y in zip(a, b))
                entries += 1
                if value not in seen:
                    seen.add(value)
                    states.append(value)
        position += 1

    assert left in seen and right in seen
    assert required not in seen
    assert len(states) == 1853
    assert entries == 5153193
    print(
        "PASS: 256 native atomic-profile checks; 9 coordinates; "
        f"{len(states)} generated states; {entries} operation entries; "
        "no common lower in the atomic fiber, including all native constants."
    )


if __name__ == "__main__":
    main()
