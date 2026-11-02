"""Independent checks of marker linearity and the sparse observer domain.

The finite samples check the generic proof's recurrence, not completeness
of a finite basis. Full tables are evaluated independently of their
reconstruction from atom-only and one-marker observations.
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
            assert len(sparse) == len(set(sparse)) == (owners - 1)**arity + arity * owners**(arity - 1)
            probes = [index[v] for v in sparse]
            # Prepare a reconstruction recipe for every full valuation.
            recipes = []
            for v in full:
                base = tuple(owners if x == owners + 1 else x for x in v)
                nonatomic = [j for j, x in enumerate(base) if x == owners]
                if not nonatomic:
                    recipes.append((index[v], ()))
                else:
                    j = nonatomic[0]
                    atom_test = index[base[:j] + (owners + 1,) + base[j + 1:]]
                    marker_tests = tuple(index[base[:j] + (owners + 1,) + base[j + 1:]]
                                         for j, x in enumerate(v) if x == owners + 1)
                    recipes.append((atom_test, marker_tests))
            assert all(atom in probes and all(p in probes for p in marks) for atom, marks in recipes)
            terms = [tuple(v[j] for v in full) for j in range(arity)]
            for _ in range(250):
                owner = rng.randrange(owners)
                left, right = rng.choice(terms), rng.choice(terms)
                terms.append(tuple(marker_own(owners, owner, x, y) for x, y in zip(left, right)))
            seen = {}
            for f in terms:
                signature = tuple(f[j] for j in probes)
                assert signature not in seen or seen[signature] == f
                seen[signature] = f
                for actual, (atom, markers) in zip(f, recipes):
                    reconstructed = (f[atom] if f[atom] < owners else
                                     owners + int(any(f[p] == owners + 1 for p in markers)))
                    assert reconstructed == actual
                    comparisons += 1
                functions += 1
    print(f'Sparse core tests: {functions} term tables reconstructed in full from '
          f'atom-only and one-marker evaluations; {comparisons} comparisons, '
          'K=3..5, arity 1..4. The all-arity theorem has a written proof.')


if __name__ == '__main__':
    check()
