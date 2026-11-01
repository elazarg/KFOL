"""Check the explicit threshold-family HSP construction, not a core basis.

All pairs in each supplied source are checked against independent observer
tables. The written proof covers every number of levels and arbitrary K.
"""

from itertools import combinations_with_replacement, permutations, product

from core_basis import marker_own
from core_thresholds import threshold_certificate, threshold_join, threshold_own


def check():
    witnesses = failures = 0
    for owners in range(3, 7):
        for levels in range(5):
            # Every threshold assignment is an owner relabeling of a sorted one.
            for thresholds in combinations_with_replacement(range(levels + 1), owners):
                carrier = range(owners + levels + 1)
                own = lambda r, x, y: threshold_own(thresholds, r, x, y)
                add = lambda x, y: threshold_join(owners, x, y)
                for x, y in product(carrier, repeat=2):
                    assert own(2, own(0, x, y), own(1, x, y)) == add(x, y)
                if min(thresholds) > 0:
                    # Exhaustion fails at n_1 with each owner's atom as x_i.
                    cover = own(0, owners + 1, 0)
                    for i in range(1, owners):
                        cover = add(cover, own(i, owners + 1, i))
                    assert cover == owners and add(owners + 1, cover) != cover
                    failures += 1
                    continue
                omitted, source, images = threshold_certificate(thresholds, levels)
                assert len(set(source)) == len(source)
                assert set(images) == set(carrier)
                assert all(v[0] <= owners and
                           all(x != omitted and 0 <= x <= owners + 1 for x in v[1:])
                           for v in source)
                mapping = dict(zip(source, images))
                for owner, v, w in product(range(owners), source, source):
                    result = tuple(marker_own(owners, owner, x, y) for x, y in zip(v, w))
                    assert result in mapping, (thresholds, owner, v, w)
                    assert mapping[result] == own(owner, mapping[v], mapping[w])
                witnesses += 1
    # Thresholds need not be in owner order in the actual construction.
    for thresholds in permutations((0, 1, 2)):
        omitted, source, images = threshold_certificate(thresholds, 2)
        mapping = dict(zip(source, images))
        assert thresholds[omitted] == 0
        for owner, v, w in product(range(3), source, source):
            result = tuple(marker_own(3, owner, x, y) for x, y in zip(v, w))
            assert mapping[result] == threshold_own(thresholds, owner, mapping[v], mapping[w])
    print(f'Core threshold family: {witnesses} explicit product/quotient witnesses '
          f'and {failures} exhaustion failures, K=3..6 and zero to four marker steps; '
          'all source pairs verified, plus all owner orders for (0,1,2).')


if __name__ == '__main__':
    check()
