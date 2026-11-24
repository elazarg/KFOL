"""Measure changes of owner between consecutive *adopted* offers.

Rows are (head, blocks), where each entry of blocks is an owner-specific
bitset of input indices. The search uses coalitions occurring in an initial row, and each
offer must cover a remaining row. A run of adoptions at the same owner is free. A decline
does not change the owner used to charge the next adoption.

The bounded solver evaluates the last single-owner phase by a greatest
fixed point on inputs. The reference recursion explores both replies to
every offer and does not use a phase calculation or safe-offer saturation.
"""

import argparse
import itertools
import random
from collections import Counter
from functools import cache


class Game:
    def __init__(self, n, k, rows, query):
        self.n = n
        self.k = k
        self.full = (1 << n) - 1
        self.rows = tuple(rows)
        self.initial = (1 << len(rows)) - 1
        self.head, self.post = query
        self.blank = (0,) * k
        self.by_head = [0] * n
        self.offers = []
        blocks = sorted({(r, b) for _, row in rows for r, b in enumerate(row) if b})
        for i, (v, _) in enumerate(rows):
            self.by_head[v] |= 1 << i
        for r, a in blocks:
            covered = sum(1 << i for i, (_, row) in enumerate(rows) if a & row[r] == a)
            self.offers.append((r, a, covered))

    def eligible(self, reg):
        held = [(r, b) for r, b in enumerate(reg) if b]
        if not held:
            return 1 << self.head
        if len(held) == 1:
            r, b = held[0]
            return b & ~self.post[r]
        choices = self.full
        for _, b in held:
            choices &= b
        return choices

    def fits(self, s, reg):
        eligible = self.eligible(reg)
        return any(eligible & (1 << v) and not s & rows for v, rows in enumerate(self.by_head))

    def support(self, s, reg, r):
        """Largest possible support of a pure r fold consistent with inherited constraints."""
        fixed = [b for j, b in enumerate(reg) if j != r and b]
        support = self.full
        if fixed:
            for b in fixed:
                support &= b
        else:
            support &= ~self.post[r]
        while True:
            previous = support
            for i, (head, blocks) in enumerate(self.rows):
                if s >> i & 1 and not blocks[r] & support:
                    support &= ~(1 << head)
            if support == previous:
                return support

    def pure(self, s, reg, r):
        return bool(self.support(s, reg, r) & self.eligible(reg))

    def solver(self, reference=False):
        """Create a query-local cache. last=None charges no first adoption."""
        @cache
        def win(s, reg, last, limit):
            if self.fits(s, reg):
                return True
            if not self.eligible(reg):
                return False
            if not reference and last is not None and limit == 0:
                return self.pure(s, reg, last)
            if reference:
                for r, b, covered in self.offers:
                    if not s & covered:
                        continue
                    cost = int(last is not None and last != r)
                    if cost > limit:
                        continue
                    remaining = s & ~covered
                    adopted = reg[:r] + (b,) + reg[r + 1:]
                    if win(remaining, adopted, r, limit - cost) and win(remaining, reg, last, limit):
                        return True
                return False
            # More row deletions only help at a fixed state and depth.
            while True:
                for r, b, covered in self.offers:
                    if not s & covered:
                        continue
                    cost = int(last is not None and last != r)
                    if cost > limit:
                        continue
                    remaining = s & ~covered
                    adopted = reg[:r] + (b,) + reg[r + 1:]
                    if win(remaining, adopted, r, limit - cost):
                        s = remaining
                        break
                else:
                    return False
                if self.fits(s, reg):
                    return True
        return win


def low_depth(game, limit):
    win = game.solver()
    for d in range(limit + 1):
        if win(game.initial, game.blank, None, d):
            return d
    return 'higher' if win(game.initial, game.blank, None, len(game.rows)) else 'lose'


def all_rows(n, k):
    rows = []
    for v in range(n):
        others = [j for j in range(n) if j != v]
        for assignment in itertools.product(range(k + 1), repeat=n - 1):
            blocks = [0] * k
            for j, r in zip(others, assignment):
                if r < k:
                    blocks[r] |= 1 << j
            if not all(blocks):
                rows.append((v, tuple(blocks)))
    return rows


def antichain(rows):
    return tuple((v, b) for v, b in rows
                 if not any(v == w and b != c and all(x & y == x for x, y in zip(c, b))
                            for w, c in rows))


def verify_and_sample(n, k, trials, seed, max_rows, compare=True):
    rng = random.Random(seed)
    rows = all_rows(n, k)
    histogram = Counter()
    pure = mixed = 0
    for _ in range(trials):
        z = antichain(rng.sample(rows, rng.randrange(1, min(len(rows), max_rows) + 1)))
        game = Game(n, k, z, rng.choice(rows))
        reference = game.solver(reference=True)
        win = game.solver()
        for j in range(5 if compare else 0):
            s = rng.randrange(game.initial + 1)
            r = rng.randrange(k)
            reg = tuple(rng.randrange(1 << n) for _ in range(k))
            # The r-only calculation also applies to an inherited blank or gap.
            assert game.pure(s, reg, r) == reference(s, reg, r, 0), (z, s, reg, r)
            pure += 1
            d = j % 3
            last = None if j == 0 else r
            assert win(s, reg, last, d) == reference(s, reg, last, d)
            mixed += 1
        measure = low_depth(game, 3)
        histogram[measure] += 1
        if measure in (2, 3, 'higher') and histogram[measure] == 1:
            print('example', measure, 'query', (game.head, game.post), 'rows', z, flush=True)
    print('n', n, 'owners', k, 'trials', trials, 'seed', seed, 'max rows', max_rows)
    print('independent comparisons:', pure, 'pure and', mixed, 'mixed.')
    print('minimum adopted-owner changes:', dict(histogram))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=3)
    parser.add_argument('--owners', type=int, default=3)
    parser.add_argument('--trials', type=int, default=1000)
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--max-rows', type=int, default=10)
    parser.add_argument('--skip-comparison', action='store_true')
    args = parser.parse_args()
    verify_and_sample(args.n, args.owners, args.trials, args.seed, args.max_rows,
                      not args.skip_comparison)
