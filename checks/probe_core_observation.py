"""Probe bounded observation depth; this is not a finite-basis certificate.

For a fixed root r, start with the kernel of x |-> x delta r and refine it
by all basic translations. The stable relation is its largest contained
congruence. The one-refinement conjecture fails in the nine-element core
model in core-observation-countermodel.json. This probe found its larger
precursor; it can also search for examples requiring greater depth.

The default run covers the stored HSP-certified models and the ladders.
Optional deterministic samples also check subalgebras of observer products
and their homomorphic images. Passing these tests does not prove a
uniform depth bound, or completeness of any proposed basis. The doubled
ladders in core_observation.py now refute every uniform depth bound.
"""

import argparse
import json
from itertools import combinations
from pathlib import Path
from random import Random

from core_basis import MIXED_JOIN, MIXED_OPERATIONS, marker_join, marker_own
from core_ladders import ladder_join, ladder_own
from probe_residual import merge_congruence, root


def reset_observation(add, operations, r):
    values = []
    for x in range(len(add)):
        value = add[x][r]
        for table in operations:
            value = table[r][value]
        values.append(value)
    return values


def refine(partition, operations):
    signatures = [(partition[x],) + tuple(partition[table[x][z]]
                  for table in operations for z in range(len(partition)))
                  for x in range(len(partition))]
    classes = {}
    return [classes.setdefault(signature, len(classes)) for signature in signatures]


def canonical(partition):
    classes = {}
    return [classes.setdefault(value, len(classes)) for value in partition]


def observation_depth(add, operations):
    """Exact stabilization depth, maximizing over every possible root."""
    maximum, witness = 0, None
    for r in range(len(add)):
        partition = canonical(reset_observation(add, operations, r))
        depth = 0
        while True:
            refined = refine(partition, operations)
            if refined == partition:
                break
            depth += 1
            partition = refined
        if depth > maximum:
            maximum, witness = depth, r
    return maximum, witness


def failure_witness(add, operations):
    """An explicit pair invisible at depth one but visible at depth two."""
    size = len(add)
    for r in range(size):
        observation = reset_observation(add, operations, r)
        first = refine(observation, operations)
        second = refine(first, operations)
        for x, y in combinations(range(size), 2):
            if first[x] != first[y] or second[x] == second[y]:
                continue
            for i, inner in enumerate(operations):
                for a in range(size):
                    u, v = inner[x][a], inner[y][a]
                    for j, outer in enumerate(operations):
                        for b in range(size):
                            left, right = observation[outer[u][b]], observation[outer[v][b]]
                            if left != right:
                                return dict(root=r, pair=[x, y], inner=[i, a],
                                            outer=[j, b], outputs=[left, right])
            raise AssertionError('A second refinement must supply a two-step witness.')
    return None


def sample_source(rng, maximum):
    """A subalgebra of a product of full three-owner observer algebras."""
    dimension = rng.randrange(2, 5)
    observers = [rng.randrange(3) for _ in range(dimension)]
    carriers = [[x for x in range(5) if x != j] for j in observers]
    source = {tuple(rng.choice(carrier) for carrier in carriers)
              for _ in range(rng.randrange(2, 5))}
    pending = list(source)
    while pending:
        x = pending.pop()
        for y in tuple(source):
            for i in range(3):
                value = tuple(marker_own(3, i, a, b) for a, b in zip(x, y))
                if value not in source:
                    source.add(value)
                    pending.append(value)
            if len(source) > maximum:
                return None
    source = sorted(source)
    indices = {value: i for i, value in enumerate(source)}
    operations = [[[indices[tuple(marker_own(3, i, a, b) for a, b in zip(x, y))]
                    for y in source] for x in source] for i in range(3)]
    add = [[indices[tuple(marker_join(3, a, b) for a, b in zip(x, y))]
            for y in source] for x in source]
    return dict(join=add, operations=operations, observers=observers,
                source=source, map=list(range(len(source))))


def sample_quotient(certificate, rng):
    add, operations = certificate['join'], certificate['operations']
    size = len(add)
    translations = [table[x] for table in operations for x in range(size)]
    partition = list(range(size))
    for _ in range(rng.randrange(1, 4)):
        x, y = rng.sample(range(size), 2)
        partition = merge_congruence(partition, x, y, translations)
    representatives = sorted({root(partition, x) for x in range(size)})
    indices = {value: i for i, value in enumerate(representatives)}
    image = [indices[root(partition, x)] for x in range(size)]
    quotient_add = [[image[add[x][y]] for y in representatives] for x in representatives]
    quotient_operations = [[[image[table[x][y]] for y in representatives]
                            for x in representatives] for table in operations]
    # Independently verify the homomorphism, not only its union-find construction.
    for i, table in enumerate(operations):
        for x in range(size):
            for y in range(size):
                assert image[table[x][y]] == quotient_operations[i][image[x]][image[y]]
    return {**certificate, 'join': quotient_add, 'operations': quotient_operations,
            'map': image}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=0,
                        help='Number of source attempts; oversized sources are skipped.')
    parser.add_argument('--seed', type=int, default=8127)
    parser.add_argument('--max-source', type=int, default=60)
    parser.add_argument('--ladders', type=int, default=15)
    parser.add_argument('--min-depth', type=int, default=2,
                        help='Minimum exact observation depth sought in samples (at least 2).')
    parser.add_argument('--counterexample', type=Path,
                        help='Write a sampled counterexample and its HSP certificate here.')
    args = parser.parse_args()
    if args.min_depth < 2:
        parser.error('--min-depth must be at least 2')

    depth, _ = observation_depth(MIXED_JOIN, MIXED_OPERATIONS)
    assert depth == 2
    print('Original countermodel:', failure_witness(MIXED_JOIN, MIXED_OPERATIONS))
    checked = 0
    for name in ('core-small-models', 'core-six-models',
                 'core-seven-models', 'core-eight-models'):
        path = Path(__file__).with_name('data') / (name + '.json')
        for model in json.loads(path.read_text()):
            assert observation_depth(model['join'], model['operations'])[0] <= 1
            checked += 1
    for length in range(1, args.ladders + 1):
        carrier = range(2 * length + 1)
        add = [[ladder_join(length, x, y) for y in carrier] for x in carrier]
        operations = [[[ladder_own(length, i, x, y) for y in carrier]
                       for x in carrier] for i in range(3)]
        assert observation_depth(add, operations)[0] == 1
    print(f'One refinement suffices on {checked} stored models and '
          f'{args.ladders} ladders. This is finite evidence only.')
    path = Path(__file__).with_name('data') / 'core-observation-countermodel.json'
    countermodel = json.loads(path.read_text())
    assert observation_depth(countermodel['join'], countermodel['operations'])[0] == 2
    print('Certified nine-element core counterexample:',
          failure_witness(countermodel['join'], countermodel['operations']))

    rng = Random(args.seed)
    sources = quotients = 0
    for _ in range(args.samples):
        source = sample_source(rng, args.max_source)
        if source is None or len(source['join']) < 4:
            continue
        quotient = sample_quotient(source, rng)
        for model in (source, quotient):
            witness = failure_witness(model['join'], model['operations'])
            if witness is not None:
                depth, r = observation_depth(model['join'], model['operations'])
                if depth < args.min_depth:
                    continue
                model['observation_witness'] = witness
                model['observation_depth'] = {'depth': depth, 'root': r}
                if args.counterexample:
                    args.counterexample.write_text(json.dumps(model, indent=2) + '\n')
                print('Sampled counterexample:', json.dumps(model))
                return
        sources += 1
        quotients += 1
    if args.samples:
        print(f'No sample of depth {args.min_depth} or greater in {sources} '
              f'sources and {quotients} quotients '
              f'(seed {args.seed}; {args.samples} attempts).')


if __name__ == '__main__':
    main()
