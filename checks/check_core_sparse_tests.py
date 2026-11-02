"""Independent checks of marker linearity and the sparse observer domain.

The finite samples check the generic proof's recurrence, not completeness
of a finite basis. Full tables are evaluated independently of their
reconstruction from one-bit, one-marker observations.
"""

from itertools import product
from random import Random

from core_basis import marker_own
from core_sparse_tests import observer_tests


def check():
    rng = Random(291743)
    comparisons = functions = 0
    for owners in (3, 4, 5):
        for arity in range(1, 5):
            omitted = owners - 1
            carrier = tuple(range(owners - 1)) + (owners, owners + 1)
            full = tuple(product(carrier, repeat=arity))
            index = {v: i for i, v in enumerate(full)}
            sparse = tuple(observer_tests(owners, arity, omitted))
            assert len(sparse) == len(set(sparse)) == arity * owners**(arity - 1)
            probes = [index[v] for v in sparse]
            probe_set = set(probes)
            # Prepare a reconstruction recipe for every full valuation.
            recipes = []
            for v in full:
                base = tuple(owners if x == owners + 1 else x for x in v)
                atom_tests = []
                for atom in range(owners - 1):
                    atomic_base = tuple(atom if x == atom else owners for x in v)
                    atom_tests.append(tuple(index[atomic_base[:j] + (owners + 1,)
                                                        + atomic_base[j + 1:]]
                                            for j, x in enumerate(v) if x != atom))
                marker_tests = tuple(index[base[:j] + (owners + 1,) + base[j + 1:]]
                                     for j, x in enumerate(v) if x == owners + 1)
                recipes.append((atom_tests, marker_tests))
            assert all(all(p in probe_set for row in atoms for p in row)
                       and all(p in probe_set for p in marks) for atoms, marks in recipes)
            terms = [tuple(v[j] for v in full) for j in range(arity)]
            for _ in range(250):
                owner = rng.randrange(owners)
                left, right = rng.choice(terms), rng.choice(terms)
                terms.append(tuple(marker_own(owners, owner, x, y) for x, y in zip(left, right)))
            seen = {}
            for f in terms:
                # The decoder receives only p bits, never the original atom
                # or n values on the sparse domain.
                recorded = {j: f[j] == owners + 1 for j in probes}
                signature = tuple(recorded[j] for j in probes)
                assert signature not in seen or seen[signature] == f
                seen[signature] = f
                for actual, (atoms, markers) in zip(f, recipes):
                    flags = [i for i, row in enumerate(atoms)
                             if not any(recorded[p] for p in row)]
                    assert len(flags) <= 1
                    reconstructed = (flags[0] if flags else
                                     owners + int(any(recorded[p] for p in markers)))
                    assert reconstructed == actual
                    comparisons += 1
                functions += 1
    print(f'Sparse core tests: {functions} term tables reconstructed in full from '
          f'one-bit, one-marker evaluations; {comparisons} comparisons, '
          'K=3..5, arity 1..4. The all-arity theorem has a written proof.')


if __name__ == '__main__':
    check()
