#!/usr/bin/env python3
"""Independently check the formalized uniform five-point obstruction.

The exact six Lean expressions agree five at a time on all 1,024 formal
named-atom/passive-marker cells and all 16,807 three-role inputs. Patch0 lies
below their common operation. A direct six-row subpower excludes every core
term representing that operation. Only the standard library is used.
"""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import time

from candidate_support import (
    NV, OWNERS, VALUES, OBS, choice, patch_value, coefficient_queries,
    coefficients, subpower_closure,
)


def common_value(outputs):
    value, count = Counter(outputs).most_common(1)[0]
    assert count >= 5
    assert outputs[0] & ~value == 0
    return value


def term_cost(term):
    return 0 if isinstance(term, int) else 1 + term_cost(term[1]) + term_cost(term[2])


def evaluate_family(patches, rows, row_index):
    assert len(patches) == 6 and all(patches)
    tables = [[patch_value(patch, row) for row in rows] for patch in patches]
    coeffs = [coefficients(table, row_index) for table in tables]
    common = []
    for i, row in enumerate(rows):
        queries = coefficient_queries(row)
        outputs = [table[i] for table in tables]
        for bits, value in zip(coeffs, outputs):
            assert sum(1 << k for k in OWNERS if bits & queries[k]) == value
        common.append(common_value(outputs))
    return tables, coeffs, common


def reset(left, right):
    result = right if right.bit_count() == 1 else left | right
    # Independently check the finite-owner core compilation of reset.
    compiled = left | right
    for owner in OWNERS:
        compiled = choice(owner, compiled, right)
    assert compiled == result
    return result


def main():
    start = time.monotonic()
    data = json.loads(Path(__file__).with_suffix('.json').read_text())
    positive, negative = data['positive'], data['negatives']
    patches = data['lean_family']
    assert len(negative) == 5
    critical = [OBS[q][2] for q in [positive] + negative]
    expected = [7, 6, 5, 6, 6, 5]
    for a, b in product(VALUES, repeat=2):
        assert choice(2, choice(0, a, b), choice(1, a, b)) == a | b
    rows = list(product(VALUES, repeat=NV))
    row_index = {row: i for i, row in enumerate(rows)}
    tables, _, common = evaluate_family(patches, rows, row_index)
    assert [common[row_index[row]] for row in critical] == expected
    formal_cells = 0
    for statuses in product(range(4), repeat=NV):
        values = tuple(1 << (s if s < 3 else 3 + j)
                       for j, s in enumerate(statuses))
        common_value([patch_value(patch, values) for patch in patches])
        formal_cells += 1
    clipped = [[reset(value, tables[0][i]) for i, value in enumerate(table)]
               for table in tables]
    clipped_common = []
    for i in range(len(rows)):
        outputs = [table[i] for table in clipped]
        clipped_common.append(common_value(outputs))
        for value in outputs:
            for role in OWNERS:
                assert (value == 1 << role) == (tables[0][i] == 1 << role)
    assert [clipped_common[row_index[row]] for row in critical] == expected
    print('Exact Lean family: logical operations',
          sum(sum(term_cost(t) + 1 for t in patch) - 1 for patch in patches),
          '; components', [len(patch) for patch in patches], flush=True)
    print('Five-of-six agreement and patch0 inclusion checked on', formal_cells,
          'formal-marker cells and', len(rows), 'three-role inputs.', flush=True)
    print('Common values at critical rows:', expected, flush=True)
    print('Three-role clipped family: coherence, patch0 singleton profiles,',
          'and critical separation checked.', flush=True)
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
    print('Independent regression passed for Core.exists_five_local_noncore',
          '(FivePointInterpolation; arbitrary role types with three distinct roles).', flush=True)
    print('Elapsed seconds:', round(time.monotonic() - start, 3), flush=True)


if __name__ == '__main__':
    main()
