"""Seeded search on broken overlapping copies of the four-input obstruction.

Run beside residual_certificate.py (or set PYTHONPATH to its directory).
The default checks 2,000 distinct labelled games, without isomorphism pruning.
"""
import argparse
from collections import Counter
from pathlib import Path
import random
import shutil

from residual_certificate import Instance, bitids

BASE = [(0, (12, 2, 0)), (1, (0, 12, 0)), (2, (10, 0, 1)),
        (3, (0, 5, 0)), (3, (3, 0, 4))]


def broken_copy(rng, n):
    vertices = [0, *rng.sample(range(1, n), 3)]
    owners = rng.sample(range(3), 3)
    rows = []
    for head, postings in BASE:
        renamed = tuple(sum(1 << vertices[j] for j in bitids(postings[r])) for r in owners)
        rows.append((vertices[head], renamed))
    for row in rng.sample(rows, rng.choice((1, 1, 2))):
        rows.remove(row)
    return rows


def candidate(rng):
    n = rng.choice((4, 5, 5, 6))
    rows = broken_copy(rng, n) + broken_copy(rng, n)
    if rng.random() < 0.7:
        head = rng.randrange(n)
        owners = rng.sample(range(3), 2)
        post = [0, 0, 0]
        for j in range(n):
            if j != head and rng.random() < 0.7:
                post[rng.choice(owners)] |= 1 << j
        rows.append((head, tuple(post)))
    positive = [0, 0, 0]
    if rng.random() < 0.5:
        owners = rng.sample(range(3), 2)
        for j in range(1, n):
            if rng.random() < 0.4:
                positive[rng.choice(owners)] |= 1 << j
    return n, tuple(sorted(set(rows))), tuple(positive)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=20261126)
    parser.add_argument('--count', type=int, default=2000)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    cadical = shutil.which('cadical') or str(max(Path.home().glob('.elan/toolchains/*/bin/cadical')))
    seen = set()
    counts = Counter()
    while len(seen) < args.count:
        key = candidate(rng)
        if key in seen:
            continue
        seen.add(key)
        n, rows, positive = key
        g = Instance(n, rows, 0, positive)
        if g.win(g.full, g.root):
            counts['feasible'] += 1
        elif g.positional(cadical, 1):
            counts['one_slot'] += 1
        elif g.positional(cadical, 2):
            counts['two_slots'] += 1
        else:
            print('More than two slots:', key, flush=True)
            counts['more_than_two'] += 1
    print(f'seed={args.seed}, cases={len(seen)}', dict(sorted(counts.items())))


if __name__ == '__main__':
    main()
