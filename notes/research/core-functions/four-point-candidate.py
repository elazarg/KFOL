#!/usr/bin/env python3
"""Independently check the Lean four-point counterexample and its discovery maxima.

This independently checks witnesses for the Lean four-point obstruction. Five actual core
terms agree at least four out of five at every input. Their common value has
no core minorant. The finite maximality calculation uses the seven nonempty subsets of {a,b,c}.
An additional formal-marker regression checks the five actual terms on all
1,024 named-atom/passive-input status cells. See four-point-candidate.md for
the scope and the interpretation of this symbolic calculation.

The small adjacent JSON gives each term as a union of components. Integers
0..4 are variables; [r,s,t] is owned choice when r<3 and union when r=3.
Union is independently checked against its three-owner core definition.

By default, also recompute the greatest full core functions satisfying each
four-row bound, using exact sampled-row fibers and source coefficients.
--quick skips that additional maximality computation; it still evaluates the
actual terms at all 16,807 inputs and computes the complete forbidden subpower.
Only Python's standard library is used.
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

NEGATIVE = (45, 486, 580, 250, 399)
CRITICAL = ((1, 2, 2, 6, 4), (1, 2, 1, 1, 1),
            (4, 4, 2, 4, 1), (4, 6, 2, 1, 2), (2, 4, 6, 6, 1))
assert tuple(OBS[q][2] for q in NEGATIVE) == CRITICAL


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='skip recomputing full maximal functions')
    args = parser.parse_args()
    started = time.monotonic()
    data = json.loads(Path(__file__).with_name('four-point-patches.json').read_text())
    patches = data['lean_family']
    assert len(patches) == 5 and all(patches)
    for a, b in product(VALUES, repeat=2):
        assert choice(2, choice(0, a, b), choice(1, a, b)) == a | b
    rows = list(product(VALUES, repeat=NV))
    row_index = {row: i for i, row in enumerate(rows)}
    tables = [[patch_value(patch, row) for row in rows] for patch in patches]
    coeffs = [coefficients(table, row_index) for table in tables]
    # Independent actual-term evaluation agrees with source reconstruction.
    common = []
    for i, row in enumerate(rows):
        queries = coefficient_queries(row)
        values = [table[i] for table in tables]
        for bits, value in zip(coeffs, values):
            reconstructed = sum(1 << k for k in OWNERS if bits & queries[k])
            assert reconstructed == value
        value, count = Counter(values).most_common(1)[0]
        assert count >= 4 and value in VALUES
        common.append(value)
    for i, q in enumerate(NEGATIVE):
        assert not common[row_index[CRITICAL[i]]] & (1 << OBS[q][0])
    formal_cells = 0
    for statuses in product(range(4), repeat=NV):
        # A separate marker represents each passive input. These markers are
        # distinct from all three named owners and from one another.
        values = tuple(1 << (s if s < 3 else 3 + j)
                       for j, s in enumerate(statuses))
        outputs = [patch_value(patch, values) for patch in patches]
        assert Counter(outputs).most_common(1)[0][1] >= 4
        formal_cells += 1
    print('Exact Lean family: components', [len(p) for p in patches], flush=True)
    print('Four-of-five formal-marker agreement checked on', formal_cells,
          'status cells.', flush=True)
    print('Four-of-five agreement checked on', len(rows), 'inputs.', flush=True)
    print('Common values at critical rows:',
          [common[row_index[row]] for row in CRITICAL], flush=True)
    states = subpower_closure(CRITICAL)
    forbidden = sum(1 << (3 * i + OBS[q][0]) for i, q in enumerate(NEGATIVE))
    assert all(state & forbidden for state in states)
    for j in range(NV):
        column = packed(row[j] for row in CRITICAL)
        assert column & forbidden == 1 << (3 * j + OBS[NEGATIVE[j]][0])
    size = len(states)
    print('Complete forbidden subpower:', size, 'tuples; no bounded tuple.', flush=True)
    if not args.quick:
        maximal = data['maximal_family']
        maximal_tables = [[patch_value(patch, row) for row in rows] for patch in maximal]
        maximal_coeffs = [coefficients(table, row_index) for table in maximal_tables]
        for i, row in enumerate(rows):
            queries = coefficient_queries(row)
            for bits, table in zip(maximal_coeffs, maximal_tables):
                assert sum(1 << k for k in OWNERS if bits & queries[k]) == table[i]
        print('Separate discovery-maximal family: components',
              [len(p) for p in maximal], flush=True)
        closure = FullFiberClosure()
        for i, expected in enumerate(maximal_coeffs):
            result, size, updates = closure.maximum(i, CRITICAL, NEGATIVE)
            assert result == expected
            print('Maximal patch', i, ':', size, 'fibers,', updates,
                  'updates; actual term matches.', flush=True)
    print('Independent regression passed for the formalized uniform four-point theorem.', flush=True)
    print('Elapsed seconds:', round(time.monotonic() - started, 3), flush=True)


if __name__ == '__main__':
    main()
