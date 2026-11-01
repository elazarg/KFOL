"""Exhaustive six-element completeness of the strengthened core candidate.

Run: python3 checks/probe_core_six_models.py

This slower enumeration is outside make check. The 17 HSP certificates
are independently checked in make check; this script verifies that they,
conservative completeness, and adjoining a common absorbing element cover
every subdirectly irreducible six-element candidate. No term-size cutoff
or conjectured unrestricted basis is used.
"""

from collections import Counter
from itertools import product

from check_core_small_models import certify_members, is_subdirectly_irreducible, key
from probe_core_basis import candidate_models, exhaustion_holds, mixed_absorption_holds


def membership_reason(add, ops, known):
    size = len(add)
    if all(t[x][y] in (x, y) for t in (add, *ops)
           for x, y in product(range(size), repeat=2)):
        return 'conservative'
    for z in range(size):
        rest = [x for x in range(size) if x != z]
        if (all(t[z][x] == z for t in ops for x in range(size)) and
                all(t[x][y] != z for t in ops for x, y in product(rest, repeat=2))):
            # The complement is a <=5-element subalgebra of the original
            # candidate, so the proved five-element result applies. Core
            # identities are regular, hence adjoining a common absorber
            # preserves every identity, at every arity.
            return 'absorbing extension'
    assert key(add, ops) in known, (add, ops)
    return 'HSP certificate'


def check():
    known, certificates, maximum = certify_members('core-six-models.json')
    counts, reasons = Counter(), Counter()
    for add, ops in candidate_models(6):
        counts['original'] += 1
        if not exhaustion_holds(add, ops):
            continue
        counts['exhaustion'] += 1
        if not mixed_absorption_holds(add, ops):
            continue
        counts['mixed'] += 1
        if is_subdirectly_irreducible(ops):
            counts['SI'] += 1
            reasons[membership_reason(add, ops, known)] += 1
    print(f'Six-element exhaustive counts: {dict(counts)}; '
          f'irreducible membership: {dict(reasons)}; '
          f'{certificates} checked HSP certificates, maximum source {maximum}. '
          'Every strengthened candidate through six elements is a core model; '
          'unrestricted completeness remains unproved.', flush=True)


if __name__ == '__main__':
    check()
