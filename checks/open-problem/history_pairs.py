"""Compare residual histories at one fixed positive query and register.

Offer histories are represented by the indices of remaining negative rows.
The oracle is the two-child recursion of the pointed-guard cut. A productive
offer covers at least one remaining row; skipping unproductive offers is exact
by that theorem. Safe-adoption histories are distinguished from unrestricted
decline histories, which also occur as hypothetical oracle queries.

Rows and coalitions are encoded as bit masks. The unlabelled bits in the
truth-table signature of a one-owner fold are ordered by support mask.
"""
from argparse import ArgumentParser
from collections import deque
from functools import lru_cache
from itertools import product
import random


def extend(register, offer):
    owner, coalition = offer
    return register[:owner] + (coalition,) + register[owner + 1:]


class Sample:
    def __init__(self, n, rows, q, owners=3):
        self.n, self.rows, self.q, self.owners = n, tuple(rows), q, owners
        self.full = (1 << len(self.rows)) - 1
        self.blank = (0,) * owners
        self.offers = {}
        for r in range(owners):
            for coalition in range(1, 1 << n):
                covered = sum(1 << j for j, (_, blocks) in enumerate(self.rows)
                              if coalition & blocks[r] == coalition)
                if covered:
                    self.offers[r, coalition] = covered

        self.heads = tuple(sum(1 << j for j, (v, _) in enumerate(self.rows) if v == h)
                           for h in range(n))
        self.fold_fail = tuple(tuple(
            sum(1 << j for j, (h, b) in enumerate(self.rows)
                if H >> h & 1 and not H & b[r])
            for H in range(1 << n)) for r in range(owners))

        # Bind memoization to the sample, so completed random samples are collectible.
        self.win = lru_cache(None)(self._win)
        self.supports = lru_cache(None)(self._supports)
        self.meeting_supports = lru_cache(None)(self._meeting_supports)
        self.fold_saturate = lru_cache(None)(self._fold_saturate)

    def eligible(self, a):
        domain = [r for r, A in enumerate(a) if A]
        if not domain:
            return 1 << self.q[0]
        if len(domain) == 1:
            r = domain[0]
            return a[r] & ~self.q[1][r]
        common = (1 << self.n) - 1
        for r in domain:
            common &= a[r]
        return common

    def free(self, S):
        return sum(1 << h for h in range(self.n) if not S & self.heads[h])

    def _win(self, S, a):
        L = self.eligible(a)
        if not L:
            return False
        if L & self.free(S):
            return True
        for e, covered in self.offers.items():
            if S & covered:
                child = S & ~covered
                if self.win(child, extend(a, e)) and self.win(child, a):
                    return True
        return False

    def _supports(self, S):
        return tuple(sum(1 << H for H in range(1, 1 << self.n) if not S & bad[H])
                     for bad in self.fold_fail)

    def fold_meets(self, H, owner, register):
        r_present = sum(bool(A) for A in register)
        for r, A in enumerate(register):
            if not A:
                continue
            if owner == r:
                if not H & A:
                    return False
            elif H & ~A:
                return False
        if r_present == 1:
            r = next(r for r, A in enumerate(register) if A)
            positive_posting = self.q[1][r]
            return not H & positive_posting if r == owner else bool(H & ~positive_posting)
        if r_present == 0:
            raise ValueError('Use the source-mark test for an empty register')
        return True

    def _meeting_supports(self, register):
        return tuple(sum(1 << H for H in range(1, 1 << self.n)
                         if self.fold_meets(H, owner, register))
                     for owner in range(self.owners))

    def _fold_saturate(self, S, register):
        """Delete every offer with an adopted child witnessed by any single-owner fold."""
        while True:
            residual = S
            fold_supports = self.supports(S)
            for e, covered in self.offers.items():
                if S & covered:
                    after = extend(register, e)
                    possible = any(left & right for left, right in
                                   zip(fold_supports, self.meeting_supports(after)))
                    if possible:
                        residual &= ~covered
            if residual == S:
                return S
            S = residual

    def root_histories(self):
        """All remaining budgets attainable by productive declines, shortest history first."""
        predecessors = {self.full: None}
        queue = deque([self.full])
        while queue:
            S = queue.popleft()
            for e, covered in self.offers.items():
                child = S & ~covered
                if child != S and child not in predecessors:
                    predecessors[child] = (S, e)
                    queue.append(child)
        return predecessors

    def safe_histories(self):
        """All productive, safe-only prefixes from the blank register, prior to stopping."""
        start = (self.full, self.blank)
        predecessors = {start: None}
        queue = deque([start])
        while queue:
            S, a = queue.popleft()
            for e, covered in self.offers.items():
                if not S & covered:
                    continue
                residual = S & ~covered
                adopt = extend(a, e)
                if not self.win(residual, adopt):
                    continue
                for register, adopted in ((a, False), (adopt, True)):
                    child = residual, register
                    if child not in predecessors:
                        predecessors[child] = ((S, a), e, adopted)
                        queue.append(child)
        return predecessors


def first_pair(sample, mode, comparable=False, same_counts=False, nonblank=False, fold_saturation=False, foreign=False):
    # Root-only mode probes full game outcomes at the fixed blank register.
    # Safe mode compares the *same fresh productive adoption* after safe prefixes.
    rooted = sample.root_histories() if mode == 'root' else sample.safe_histories()
    seen = {}
    states = [(S, sample.blank) for S in rooted] if mode == 'root' else list(rooted)
    for S, a in states:
        if nonblank and a == sample.blank:
            continue
        if fold_saturation:
            S = sample.fold_saturate(S, a)
        extra = tuple((S & heads).bit_count() for heads in sample.heads) if same_counts else ()
        key = a, sample.supports(S), extra
        if S in seen.get(key, ()):
            continue
        for T in seen.get(key, ()):
            if comparable and S & T not in (S, T):
                continue
            if mode == 'root':
                if sample.win(S, a) != sample.win(T, a):
                    return a, S, T, None
            else:
                for e, covered in sample.offers.items():
                    if foreign and a[e[0]]:
                        continue
                    if S & covered and T & covered:
                        extended = extend(a, e)
                        if sample.win(S & ~covered, extended) != sample.win(T & ~covered, extended):
                            return a, S, T, e
        seen.setdefault(key, set()).add(S)
    return None


def colors(n, h, K):
    others = [v for v in range(n) if v != h]
    result = []
    for values in product(range(K + 1), repeat=len(others)):
        blocks = [0] * K
        for v, r in zip(others, values):
            if r < K:
                blocks[r] |= 1 << v
        if any(blocks) and not all(blocks):
            result.append(tuple(blocks))
    return result


def minimal_rows(rows):
    return [(h, row) for h, row in sorted(set(rows))
            if not any(k == h and other != row and all(b & c == b for b, c in zip(other, row))
                       for k, other in rows)]


def search(args):
    rng = random.Random(args.seed)
    all_rows = [(h, blocks) for h in range(args.n) for blocks in colors(args.n, h, args.owners)]
    for trial in range(1, args.trials + 1):
        rows = minimal_rows(rng.sample(all_rows, args.rows))
        q = (rng.randrange(args.n), (0,) * args.owners)
        sample = Sample(args.n, rows, q, args.owners)
        example = first_pair(sample, args.mode, args.comparable, args.same_counts, args.nonblank, args.fold_saturation, args.foreign)
        if example:
            print('trial', trial, 'query', q, 'rows', rows, 'pair', example, flush=True)
            return
    print('No separation in', args.trials, 'samples')


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('--n', type=int, default=3)
    parser.add_argument('--owners', type=int, default=3)
    parser.add_argument('--rows', type=int, default=7)
    parser.add_argument('--seed', type=int, default=7)
    parser.add_argument('--trials', type=int, default=1000)
    parser.add_argument('--mode', choices=('root', 'safe'), default='root')
    parser.add_argument('--comparable', action='store_true')
    parser.add_argument('--same-counts', action='store_true')
    parser.add_argument('--nonblank', action='store_true')
    parser.add_argument('--fold-saturation', action='store_true')
    parser.add_argument('--foreign', action='store_true')
    search(parser.parse_args())
