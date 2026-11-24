"""A fixed register with exponentially many independent optimal adoption tests.

Run with no arguments for an exhaustive finite check of the four-data-input,
three-owner example. Menus are nonempty bit sets. Negative probes and the
constructive yes witnesses are evaluated directly in the winner-set algebra.
The no instances have a one-row obstruction, checked by exact term-signature
closure with the two prescribed singleton tests.
"""
from itertools import combinations, product
from math import comb

R, S, Q = 1, 2, 4
OWNERS = (R, S, Q)
UNIVERSE = R | S | Q


def choose(owner, left, right):
    return owner if owner in (left, right) else left | right


def fold(owner, menus):
    menus = iter(menus)
    result = next(menus)
    for value in menus:
        result = choose(owner, result, value)
    return result


def indices(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length() - 1
        bits ^= bit


def subsets_of_size(d, k):
    return tuple(sum(1 << j for j in group) for group in combinations(range(d), k))


class IndexInstance:
    def __init__(self, data=4, k=2):
        assert data >= 3 and 2 <= k < data
        self.data = data
        self.n = data + 5
        self.subsets = subsets_of_size(data, k)
        self.h = data
        self.dummy = data + 1
        self.anchors = (data + 2, data + 3, data + 4)
        self.anchor_mask = sum(1 << j for j in self.anchors)
        self.data_mask = (1 << data) - 1
        self.s_base = self.data_mask | self.anchor_mask | (1 << self.h)
        self.permanent = []
        for x in range(data):
            self.permanent.append((x, R, self.anchor_mask))
            self.permanent.append((x, S, self.data_mask ^ (1 << x)))
        u, v, w = self.anchors
        self.permanent.extend(((u, R, 1 << v), (u, S, 1 << w),
                               (v, R, 1 << u), (v, S, 1 << w),
                               (w, S, (1 << u) | (1 << v))))
        self.dummy_r = self.dummy, R, 1 << self.h
        self.dummy_s = tuple((self.dummy, S, self.s_base ^ t) for t in self.subsets)

    def rows(self, residual, before_adoption=False):
        return (self.permanent + [(self.h, R, t) for t in residual] +
                list(self.dummy_s) + ([self.dummy_r] if before_adoption else []))

    def probe(self, row, observer):
        h, owner, posting = row
        return tuple(observer if j == h else owner if posting >> j & 1
                     else UNIVERSE ^ observer for j in range(self.n))

    def profile_input(self, owner, coalition):
        return tuple(owner if coalition >> j & 1 else UNIVERSE ^ owner for j in range(self.n))

    def witness(self, residual, val):
        u, v, w = self.anchors
        guardian = choose(S, choose(R, val[u], val[v]), val[w])
        helpers = (fold(S, (val[j] for j in indices(t))) for t in residual)
        return fold(R, (val[self.h], guardian, *helpers))

    def verify_witness(self, residual, required_wins, rows):
        for owner, coalition in required_wins:
            assert self.witness(residual, self.profile_input(owner, coalition)) == owner
        for row in rows:
            for observer in OWNERS:
                if observer != row[1]:
                    assert not self.witness(residual, self.probe(row, observer)) & observer

    def fold_supports(self, rows):
        return tuple(tuple(H for H in range(1, 1 << self.n)
                           if all(not H >> h & 1 or r == owner and H & posting
                                  for h, r, posting in rows))
                     for owner in OWNERS)

    def one_row_signature_closure(self, t):
        b = self.s_base ^ t
        probe = self.probe((self.h, R, t), S)
        tuples = {(j == self.h, bool(b >> j & 1), probe[j]) for j in range(self.n)}
        while True:
            generated = {
                ((p or a) if gate == R else (p and a),
                 (q or b) if gate == S else (q and b),
                 choose(gate, x, y))
                for (p, q, x), (a, b, y), gate in product(tuples, tuples, OWNERS)
            }
            if generated <= tuples:
                return tuples
            tuples.update(generated)


def check():
    sample = IndexInstance()
    coalitions = sample.subsets
    count = len(coalitions)
    negative_signatures = [sample.one_row_signature_closure(t) for t in coalitions]
    assert all(not any(a and b and not x & S for a, b, x in states)
               for states in negative_signatures)

    # Every prefix reaches a winning state. A declined r:T is safe because
    # the adopted test is witnessed on its pre-offer rows already.
    for offered in range(1 << count):
        remaining = [t for i, t in enumerate(coalitions) if not offered >> i & 1]
        rows = sample.rows(remaining, before_adoption=True)
        for t in remaining:
            sample.verify_witness(remaining, ((R, t),), rows)
        sample.verify_witness(remaining, ((R, 1 << sample.h),), rows)

    patterns = set()
    tested = 0
    for removed in combinations(coalitions, count // 2):
        remaining = [t for t in coalitions if t not in removed]
        rows = sample.rows(remaining)
        assert sample.fold_supports(rows) == ((), (), ())
        answers = []
        for t, signatures in zip(coalitions, negative_signatures):
            if t in remaining:
                assert not any(a and b and not x & S for a, b, x in signatures)
                answers.append(False)
            else:
                sample.verify_witness(remaining, ((R, 1 << sample.h), (S, sample.s_base ^ t)), rows)
                answers.append(True)
            tested += 1
        patterns.add(tuple(answers))
    assert len(patterns) == comb(count, count // 2)
    print(f'{len(patterns)} equal-length histories, {tested} optimal adoption tests, '
          f'{len(patterns)} different answer vectors')
    print('One-row obstruction closure sizes:', [len(states) for states in negative_signatures])


if __name__ == '__main__':
    check()
