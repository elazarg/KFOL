"""Exhaustive completeness of the original candidate through five elements.

This is a finite result, not an unrestricted finite-basis proof. The six-state
countermodel in check_core_mixed.py proves the size threshold is sharp.
Membership certificates are small subalgebras of products of observer
quotients, with onto homomorphisms. Their discovery need not be rerun.
"""

import json
from itertools import combinations, permutations, product
from pathlib import Path

from core_basis import marker_own
from probe_core_basis import candidate_models, exhaustion_holds, relabel
from probe_residual import merge_congruence, root
from semilattice_shapes import automorphisms


def key(add, ops):
    # Permuting owner names preserves the core variety, as does carrier relabeling.
    return tuple(map(tuple, add)), tuple(sorted(tuple(map(tuple, t)) for t in ops))


def certify_members(filename='core-small-models.json', *, include_relabelings=True, fix_join=False):
    path = Path(__file__).with_name('data') / filename
    certificates = json.loads(path.read_text())
    known = set()
    for certificate in certificates:
        add, ops = certificate['join'], certificate['operations']
        observers = certificate['observers']
        source = tuple(map(tuple, certificate['source']))
        images = certificate['map']
        assert len(source) == len(set(source)) == len(images)
        assert set(images) == set(range(len(add)))
        assert observers and all(j in range(3) for j in observers)
        assert all(len(v) == len(observers) and
                   all(x in range(5) and x != observer for x, observer in zip(v, observers))
                   for v in source)
        mapping = dict(zip(source, images))
        for r, x, y in product(range(3), source, source):
            z = tuple(marker_own(3, r, a, b) for a, b in zip(x, y))
            assert z in mapping
            assert mapping[z] == ops[r][mapping[x]][mapping[y]]
        for x, y in product(range(len(add)), repeat=2):
            assert ops[2][ops[0][x][y]][ops[1][x][y]] == add[x][y]
        if include_relabelings:
            renamings = automorphisms(add) if fix_join else permutations(range(len(add)))
            for p in renamings:
                renamed = relabel(add, p)
                known.add(key(renamed, [relabel(t, p) for t in ops]))
    return known, len(certificates), max(len(c['source']) for c in certificates)


def is_subdirectly_irreducible(ops):
    size = len(ops[0])
    pairs = tuple(combinations(range(size), 2))
    translations = [tuple(t[x][y] for x in range(size)) for t in ops for y in range(size)]
    intersection = set(pairs)
    for x, y in pairs:
        congruence = merge_congruence(list(range(size)), x, y, translations)
        intersection = {(a, b) for a, b in intersection if root(congruence, a) == root(congruence, b)}
        if not intersection:
            return False
    return bool(intersection)


def check():
    known, certificates, maximum = certify_members()
    _, six_certificates, six_maximum = certify_members('core-six-models.json')
    _, seven_certificates, seven_maximum = certify_members(
        'core-seven-models.json', include_relabelings=False)
    _, eight_certificates, eight_maximum = certify_members(
        'core-eight-models.json', include_relabelings=False)
    counts = []
    for size in range(1, 6):
        candidates = irreducibles = 0
        for add, ops in candidate_models(size):
            if not exhaustion_holds(add, ops):
                continue
            candidates += 1
            if size <= 2:
                # Conservative completeness already covers these carriers.
                assert all(t[x][y] in (x, y) for t in ops
                           for x, y in product(range(size), repeat=2))
                irreducibles += size == 2
                continue
            if is_subdirectly_irreducible(ops):
                irreducibles += 1
                assert key(add, ops) in known, (size, add, ops)
        counts.append((candidates, irreducibles))
    print(f'Core candidate through five elements: (models, SI models) = {counts}; '
          f'{certificates} independently verified HSP certificates, '
          f'each with at most {maximum} source elements. '
          'All smaller candidate models belong to the core variety; '
          'the six-state obstruction is smallest possible.')
    print(f'Six-element strengthened candidate: {six_certificates} HSP certificates '
          f'verified, with at most {six_maximum} source elements. '
          'Exhaustive six-element coverage is checked separately by '
          'probe_core_six_models.py.')
    print(f'Seven-element strengthened candidate: {seven_certificates} HSP certificates '
          f'verified, with at most {seven_maximum} source elements. '
          'Exhaustive coverage is checked separately by probe_core_seven_models.py.')
    print(f'Eight-element strengthened candidate: {eight_certificates} HSP certificates '
          f'verified, with at most {eight_maximum} source elements. '
          'Exhaustive coverage is checked by probe_core_seven_models.py --size 8.')


if __name__ == '__main__':
    check()
