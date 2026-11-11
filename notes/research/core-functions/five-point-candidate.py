#!/usr/bin/env python3
"""Reproduce a five-point interpolable non-core function with a core minorant.

This is finite research evidence, not a Lean theorem. The assertions concern
exactly the seven nonempty subsets of {a,b,c}; the supplied expressions do not
yet give a uniform extra-role result. All six actual terms are evaluated on
all 16,807 inputs, then a direct, unpruned six-row subpower excludes every core
term representing their common operation. Only the standard library is used.

--maximal additionally recomputes the six greatest full functions obeying the
negative constraints (omitting none or one). The actual first patch need only
lie below its maximum; its ten missing source bits do not affect coherence.
"""
from collections import Counter
from itertools import product
import argparse
import json
from pathlib import Path
import time

from candidate_support import (
    NV, OWNERS, VALUES, OBS, choice, patch_value, coefficient_queries,
    coefficients, packed, subpower_closure, FullFiberClosure,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--maximal', action='store_true',
                        help='also recompute full maximal functions')
    args = parser.parse_args()
    start = time.monotonic()
    data = json.loads(Path(__file__).with_suffix('.json').read_text())
    positive, negative, patches = data['positive'], data['negatives'], data['patches']
    assert len(negative) == 5 and len(patches) == 6 and all(patches)
    critical = [OBS[q][2] for q in [positive] + negative]
    for a, b in product(VALUES, repeat=2):
        assert choice(2, choice(0, a, b), choice(1, a, b)) == a | b
    rows = list(product(VALUES, repeat=NV))
    row_index = {row: i for i, row in enumerate(rows)}
    tables = [[patch_value(patch, row) for row in rows] for patch in patches]
    coeffs = [coefficients(table, row_index) for table in tables]
    common = []
    for i, row in enumerate(rows):
        queries = coefficient_queries(row)
        values = [table[i] for table in tables]
        for bits, value in zip(coeffs, values):
            assert sum(1 << k for k in OWNERS if bits & queries[k]) == value
        value, count = Counter(values).most_common(1)[0]
        assert count >= 5 and value in VALUES
        common.append(value)
        contributions = list(row)
        x, y, z, w, v = row
        contexts = (x == y == 2 and v == 4,
                    y == 1 and z == w == v == 4,
                    x == w == 4 and z == v == 2,
                    x == 4 and w == 2,
                    x == 1 and y == w == 4)
        assert sum(contexts) <= 1
        for enabled, source, forbidden in zip(contexts, (3, 0, 1, 4, 2), (1, 2, 1, 1, 2)):
            if enabled:
                contributions[source] &= ~forbidden
        described = 0
        for contribution in contributions:
            described |= contribution
        assert described == value
        assert tables[0][i] & ~value == 0
    assert common[row_index[critical[0]]] & (1 << OBS[positive][0])
    for row, q in zip(critical[1:], negative):
        assert not common[row_index[row]] & (1 << OBS[q][0])
    # This boundary is intentional: current native expressions are K=3 witnesses.
    formal_bad = 0
    for statuses in product(range(4), repeat=NV):
        values = tuple(1 << (s if s < 3 else 3 + j)
                       for j, s in enumerate(statuses))
        outputs = [patch_value(patch, values) for patch in patches]
        formal_bad += Counter(outputs).most_common(1)[0][1] < 5
    print('Actual core terms: components', [len(patch) for patch in patches], flush=True)
    print('Five-of-six agreement checked on', len(rows), 'inputs.', flush=True)
    print('First actual term is a core minorant at every input.', flush=True)
    print('Common values at critical rows:',
          [common[row_index[row]] for row in critical], flush=True)
    print('Extra-role formal status failures:', formal_bad,
          '; no uniform extra-role claim.', flush=True)
    print('Computing the complete six-row subpower...', flush=True)
    states = subpower_closure(critical)
    bad = sum(1 << (3 * (i + 1) + OBS[q][0]) for i, q in enumerate(negative))
    good = 1 << OBS[positive][0]
    assert not any(state & good and not state & bad for state in states)
    assert any(not state & bad for state in states)
    for i, q in enumerate(negative):
        remaining = bad & ~(1 << (3 * (i + 1) + OBS[q][0]))
        assert any(state & good and not state & remaining for state in states)
    print('Complete six-row closure:', len(states),
          'tuples; positive observation incompatible with all five negatives.', flush=True)
    if args.maximal:
        closure = FullFiberClosure()
        for i, expected in enumerate(coeffs):
            omitted = None if i == 0 else i - 1
            result, size, updates = closure.maximum(omitted, critical[1:], negative)
            assert expected & ~result == 0
            if i:
                assert result == expected
            print('Maximal patch', i, ':', size, 'fibers,', updates,
                  'updates; extra bits over actual term:',
                  (result & ~expected).bit_count(), flush=True)
    print('Verified finite K=3 research result; no Lean theorem claimed.', flush=True)
    print('Elapsed seconds:', round(time.monotonic() - start, 3), flush=True)


if __name__ == '__main__':
    main()
