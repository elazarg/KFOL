#!/usr/bin/env python3
"""Independently validate the finite row-peeling recognition equations.

The Peeling recognizer uses only input columns, set membership, rainbow
subsets of atomic demands, and strict deletion of bounded rows. It never
calls direct_subpower, which is a separate unpruned semantic oracle.

Default: boundary cases, small random matrices, and the six-row obstruction.
--full: exhaust all raw upper tuples and positive queries for the small
matrices, checking exact tuple realizability as well. --owners accepts 3 or 4.
Only Python's standard library is used. This is an independent regression,
not a replacement for the Lean soundness and completeness proofs.
"""
import argparse
from functools import lru_cache
from itertools import product
from random import Random
import time


class Peeling:
    """Finite recognizer, independent of term generation or closure.

    Sets of roles are integer masks. A demand (i,r) requires the exact atom
    {r} at row i. A positive query (q,k) requires k at row q. Bounds may be
    empty, and demands may conflict or refer to rows outside the bounded set.
    """
    def __init__(self, owners, columns, bounds):
        self.owners = owners
        self.columns = tuple(map(tuple, columns))
        self.bounds = tuple(bounds)
        self.rows = len(bounds)
        self.full = (1 << owners) - 1
        assert owners >= 3
        assert all(0 <= bound <= self.full for bound in self.bounds)
        assert all(len(col) == self.rows and
                   all(0 < value <= self.full for value in col)
                   for col in self.columns)
        self.generator = lru_cache(None)(self._generator)
        self.feasible = lru_cache(None)(self._feasible)

    @staticmethod
    def demands(atoms):
        # Repetitions do not change a conjunction; conflicting atoms remain.
        return tuple(sorted(set(atoms)))

    def _generator(self, bounded, demands, positive):
        for col in self.columns:
            if any(col[i] & ~self.bounds[i]
                   for i in range(self.rows) if bounded >> i & 1):
                continue
            if any(col[i] != 1 << role for i, role in demands):
                continue
            if positive is not None and not col[positive[0]] >> positive[1] & 1:
                continue
            return True
        for i in range(self.rows):
            if bounded >> i & 1:
                for role in range(self.owners):
                    if self.bounds[i] >> role & 1:
                        enlarged = self.demands((*demands, (i, role)))
                        if self.feasible(bounded ^ (1 << i), enlarged, positive):
                            return True
        return False

    def _feasible(self, bounded, demands, positive):
        # A rainbow selection includes at most one demand per owner. The
        # empty selection is essential when there are no generators.
        groups = [[atom for atom in demands if atom[1] == role]
                  for role in range(self.owners)]
        for selected in product(*([None] + group for group in groups)):
            rainbow = self.demands(atom for atom in selected if atom is not None)
            if not self.generator(bounded, rainbow, None):
                return False
        if positive is None:
            return True
        if not self.generator(bounded, (), positive):
            return False
        query, winner = positive
        for row, role in demands:
            if role != winner and not any(
                    self.generator(bounded, ((row, role),), (query, other))
                    for other in range(self.owners) if other != role):
                return False
        return True

    def query(self, bounded=None, demands=(), positive=None):
        if bounded is None:
            bounded = (1 << self.rows) - 1
        demands = self.demands(demands)
        assert 0 <= bounded < 1 << self.rows
        assert all(0 <= i < self.rows and 0 <= r < self.owners for i, r in demands)
        assert positive is None or (0 <= positive[0] < self.rows and
                                    0 <= positive[1] < self.owners)
        return self.feasible(bounded, demands, positive)


def direct_subpower(owners, columns, rows):
    """Unpruned coordinatewise-choice closure, used only by the test oracle.

    Every unordered pair is processed when its later member is reached.
    Packed atom masks accelerate ordinary set choice; no source coefficients,
    profiles, peeling queries or pruning rules enter this enumeration.
    """
    full = (1 << owners) - 1
    spread = [sum(1 << (owners * i) for i in range(rows) if mask >> i & 1)
              for mask in range(1 << rows)]
    cleared = [~sum(value << role for role in range(owners)) for value in spread]
    inserted = [[value << role for value in spread] for role in range(owners)]
    states, atoms, known = [], [], set()

    def add(value):
        if value in known:
            return
        known.add(value)
        states.append(value)
        masks = [0] * owners
        for i in range(rows):
            coordinate = value >> (owners * i) & full
            if coordinate and coordinate & (coordinate - 1) == 0:
                masks[coordinate.bit_length() - 1] |= 1 << i
        atoms.append(masks)

    for col in columns:
        add(sum(value << (owners * i) for i, value in enumerate(col)))
    head = 0
    while head < len(states):
        left, left_atoms = states[head], atoms[head]
        for tail in range(head + 1):
            right, right_atoms = states[tail], atoms[tail]
            union = left | right
            for role in range(owners):
                absorbed = left_atoms[role] | right_atoms[role]
                add((union & cleared[absorbed]) | inserted[role][absorbed])
        head += 1
    return [tuple(value >> (owners * i) & full for i in range(rows))
            for value in states]


def oracle(relation, bounds, bounded, demands, positive):
    return any(
        all(not value[i] & ~bounds[i]
            for i in range(len(bounds)) if bounded >> i & 1)
        and all(value[i] == 1 << role for i, role in demands)
        and (positive is None or value[positive[0]] >> positive[1] & 1)
        for value in relation)


def check_query(recognizer, relation, bounded, demands=(), positive=None):
    got = recognizer.query(bounded, demands, positive)
    expected = oracle(relation, recognizer.bounds, bounded, demands, positive)
    assert got == expected, dict(
        columns=recognizer.columns, bounds=recognizer.bounds, bounded=bounded,
        demands=demands, positive=positive, got=got, expected=expected)


def boundary_tests(owners):
    checks = 0
    for variables in range(4):
        columns = [()] * variables
        relation = direct_subpower(owners, columns, 0)
        assert relation == ([()] if variables else [])
        assert Peeling(owners, columns, ()).query() == (variables > 0)
        checks += 1
    for rows in range(1, 4):
        bounds = ((1 << owners) - 1,) * rows
        empty = Peeling(owners, [], bounds)
        for demands in [(), ((0, 0),), ((0, 0), (0, 1)), ((0, 0), (0, 0))]:
            for positive in [None, (0, 2)]:
                check_query(empty, [], (1 << rows) - 1, demands, positive)
                checks += 1
    # Explicit contradictions with existing generators, not only empty Var.
    columns = [(1, 7), (2, 4)]
    relation = direct_subpower(owners, columns, 2)
    for bounds in [(0, 7), (7, 0), (7, 7)]:
        recognizer = Peeling(owners, columns, bounds)
        for bounded in range(4):
            for demands in [(), ((0, 0), (0, 1)), ((1, 2), (1, 2))]:
                for positive in [None, (0, 1), (1, 0)]:
                    check_query(recognizer, relation, bounded, demands, positive)
                    checks += 1
    return checks


def random_tests(owners, full_suite, rng):
    full = (1 << owners) - 1
    checks = 0
    trials = (30 if owners == 3 else 12) if full_suite else 8
    for trial in range(trials):
        rows, variables = trial % 3 + 1, rng.randrange(5)
        columns = [tuple(rng.randrange(1, full + 1) for _ in range(rows))
                   for _ in range(variables)]
        relation = direct_subpower(owners, columns, rows)
        bounds_to_test = (product(range(full + 1), repeat=rows) if full_suite else
                          [tuple(rng.randrange(full + 1) for _ in range(rows))
                           for _ in range(30)])
        for bounds in bounds_to_test:
            recognizer = Peeling(owners, columns, bounds)
            bounded_values = [value for value in relation
                              if all(not a & ~b for a, b in zip(value, bounds))]
            feasible = recognizer.query()
            assert feasible == bool(bounded_values)
            checks += 1
            if full_suite:
                maximum = [0] * rows
                for value in bounded_values:
                    for i, item in enumerate(value):
                        maximum[i] |= item
                all_members = True
                for i in range(rows):
                    for role in range(owners):
                        possible = recognizer.query(positive=(i, role))
                        assert possible == bool(maximum[i] >> role & 1)
                        if bounds[i] >> role & 1:
                            all_members &= possible
                        checks += 1
                # Union is core-definable: witnesses for every required
                # membership combine to one exact tuple.
                assert (feasible and all_members) == (bounds in relation)
                checks += 1
        for _ in range(200 if full_suite else 50):
            bounds = tuple(rng.randrange(full + 1) for _ in range(rows))
            bounded = rng.randrange(1 << rows)
            demands = tuple((rng.randrange(rows), rng.randrange(owners))
                            for _ in range(rng.randrange(rows + 3)))
            positive = (None if rng.randrange(4) == 0 else
                        (rng.randrange(rows), rng.randrange(owners)))
            check_query(Peeling(owners, columns, bounds), relation,
                        bounded, demands, positive)
            checks += 1
    print('Small matrices:', trials, '; comparisons:', checks, flush=True)
    return checks


def critical_tests(owners, full_suite, rng):
    # Extra owners act as union on this matrix, so the three-owner closure
    # remains a valid independent oracle also when --owners=4 is requested.
    rows = [(4, 2, 4, 1, 2), (2, 2, 6, 1, 4), (2, 1, 4, 4, 4),
            (4, 1, 2, 4, 2), (4, 6, 6, 2, 1), (1, 4, 2, 4, 5)]
    columns = tuple(zip(*rows))
    relation = direct_subpower(3, columns, 6)
    assert len(relation) == 7260
    bounds = (7, 6, 5, 6, 6, 5)
    recognizer = Peeling(owners, columns, bounds)
    negative_rows = 62  # Q is a query row, not an upper-bound row.
    assert recognizer.query(negative_rows)
    assert not recognizer.query(negative_rows, positive=(0, 0))
    for row in range(1, 6):
        assert recognizer.query(negative_rows ^ (1 << row), positive=(0, 0))
    checks = 7
    for _ in range(1000 if full_suite else 100):
        bounded = rng.randrange(64)
        demands = tuple((rng.randrange(6), rng.randrange(owners))
                        for _ in range(rng.randrange(6)))
        positive = None if rng.randrange(4) == 0 else (rng.randrange(6), rng.randrange(owners))
        check_query(recognizer, relation, bounded, demands, positive)
        checks += 1
    print('Six-row closure:', len(relation), '; comparisons:', checks,
          '; critical exclusion and all five deletions passed.', flush=True)
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='exhaust small target tuples')
    parser.add_argument('--owners', type=int, choices=(3, 4), default=3)
    args = parser.parse_args()
    started = time.monotonic()
    rng = Random(9928481)
    checks = boundary_tests(args.owners)
    checks += random_tests(args.owners, args.full, rng)
    checks += critical_tests(args.owners, args.full, rng)
    print('Passed', checks, 'comparisons with', args.owners,
          'owners in the small suite; elapsed seconds:',
          round(time.monotonic() - started, 3), flush=True)


if __name__ == '__main__':
    main()
