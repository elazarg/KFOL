"""Exhaustive completeness through seven or eight elements of the core candidate.

Run: python3 checks/probe_core_seven_models.py [--size 8] [--audit-six]

Requires a C++17 compiler (g++ by default, or set CXX). Compilation and
temporary enumeration files stay in a temporary directory. The default
Python checks verify every HSP certificate without needing a compiler.
The optional audit compares the new enumeration to the independent older
Python enumeration on six elements, including the complete labeled
semilattice sets, model/SI counts, and irreducible coverage.
"""

import argparse
import json
import os
from itertools import permutations, product
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from check_core_small_models import certify_members, is_subdirectly_irreducible, key
from probe_core_basis import (candidate_models, exhaustion_holds,
                              mixed_absorption_holds, relabel, semilattices)
from semilattice_shapes import shapes


def run_enumeration(size, binary, directory):
    source = directory / f'shapes-{size}.txt'
    output = directory / f'models-{size}.jsonl'
    tables = shapes(size)
    for table in tables:
        assert all(table[x][x] == x for x in range(size))
        assert all(table[x][y] == table[y][x] for x, y in product(range(size), repeat=2))
        assert all(table[x][table[y][z]] == table[table[x][y]][z]
                   for x, y, z in product(range(size), repeat=3))
    source.write_text(''.join(''.join(str(x) for row in table for x in row) + '\n'
                              for table in tables))
    result = subprocess.run([str(binary), str(size), str(source), str(output)],
                            check=True, capture_output=True, text=True)
    return json.loads(result.stdout), [json.loads(line) for line in output.read_text().splitlines()]


def validate_candidate(add, ops):
    size = len(add)
    for table in (add, *ops):
        assert all(table[x][x] == x for x in range(size))
        assert all(table[x][y] == table[y][x] for x, y in product(range(size), repeat=2))
        assert all(table[x][table[y][z]] == table[table[x][y]][z]
                   for x, y, z in product(range(size), repeat=3))
    for x, y, z in product(range(size), repeat=3):
        assert all(t[x][add[y][z]] == add[t[x][y]][t[x][z]] for t in ops)
    for a, b, c in permutations(range(3)):
        for x, y in product(range(size), repeat=2):
            assert add[ops[a][x][y]][ops[b][x][y]] == add[x][y]
            assert ops[a][x][ops[b][x][y]] == ops[b][x][ops[a][x][y]]
            assert ops[c][ops[a][x][y]][ops[b][x][y]] == add[x][y]
    assert exhaustion_holds(add, ops) and mixed_absorption_holds(add, ops)
    assert is_subdirectly_irreducible(ops)


def absorbing_extension(ops):
    size = len(ops[0])
    return any(all(t[z][x] == z for t in ops for x in range(size)) and
               all(t[x][y] != z for t in ops for x, y in product(range(size), repeat=2)
                   if x != z and y != z) for z in range(size))


def audit_six(binary, directory):
    labeled = {relabel(table, p) for table in shapes(6) for p in permutations(range(6))}
    assert labeled == set(semilattices(6))
    report, models = run_enumeration(6, binary, directory)
    covered = {key(relabel(add, p), [relabel(t, p) for t in ops])
               for add, ops in models for p in permutations(range(6))}
    candidates, irreducibles = set(), set()
    for add, ops in candidate_models(6):
        if not exhaustion_holds(add, ops) or not mixed_absorption_holds(add, ops):
            continue
        candidates.add(key(add, ops))
        if is_subdirectly_irreducible(ops):
            irreducibles.add(key(add, ops))
            if sum(t != add for t in ops) > 1 and not absorbing_extension(ops):
                assert key(add, ops) in covered
    assert len(candidates) == report['models'] == 3165
    assert len(irreducibles) == report['irreducibles'] == 37
    assert len(labeled) == report['tables'] == 22566
    for add, ops in models:
        validate_candidate(add, ops)
    print('Independent six-element audit passed: all labeled semilattices, '
          'candidate/SI counts, and irreducible coverage.', flush=True)


def check(audit=False, size=7):
    with TemporaryDirectory(prefix='kfol-core-tables-') as temporary:
        directory = Path(temporary)
        binary = directory / 'probe'
        subprocess.run([os.environ.get('CXX', 'g++'), '-std=c++17', '-O3',
                        str(Path(__file__).with_name('probe_core_tables.cpp')),
                        '-o', str(binary)], check=True)
        if audit:
            audit_six(binary, directory)
        report, models = run_enumeration(7, binary, directory)
        known, certificates, maximum = certify_members('core-seven-models.json', fix_join=True)
        assert report == {'size': 7, 'shapes': 222, 'tables': 674611, 'models': 29439,
                          'irreducibles': 102, 'hard': 70, 'one_owner': 8,
                          'conservative': 0, 'absorbing_extensions': 24}
        assert len(models) == report['hard']
        for add, ops in models:
            validate_candidate(add, ops)
            assert key(add, ops) in known, (add, ops)
        print(f'Seven-element exhaustive verification: {report}; '
              f'{certificates} verified HSP certificates, source size at most {maximum}. '
              'The other irreducibles are one-owner expansions or absorbing extensions '
              'of closed six-element subalgebras. Unrestricted completeness is unproved.')
        if size == 8:
            report, models = run_enumeration(8, binary, directory)
            known, certificates, maximum = certify_members('core-eight-models.json', fix_join=True)
            assert report == {'size': 8, 'shapes': 1078, 'tables': 27019896, 'models': 299013,
                              'irreducibles': 315, 'hard': 235, 'one_owner': 10,
                              'conservative': 0, 'absorbing_extensions': 70}
            assert len(models) == report['hard']
            for add, ops in models:
                validate_candidate(add, ops)
                assert key(add, ops) in known, (add, ops)
            print(f'Eight-element exhaustive verification: {report}; '
                  f'{certificates} verified HSP certificates, source size at most {maximum}. '
                  'The other irreducibles are one-owner expansions or absorbing extensions '
                  'of closed seven-element subalgebras. Unrestricted completeness is unproved.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-six', action='store_true')
    parser.add_argument('--size', type=int, choices=(7, 8), default=7)
    args = parser.parse_args()
    check(args.audit_six, args.size)
