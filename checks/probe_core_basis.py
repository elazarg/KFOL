"""Optional search around a tentative three-owner basis; NOT a completeness proof.

Use: python checks/probe_core_basis.py --size 5

The candidate has semilattice laws for + and each *_i, distribution of
each *_i over +, pairwise Birkhoff laws, pairwise union coverage, and the
three-owner definition of +. All these laws use at most three variables,
so the five-element extra-marker algebra must satisfy them. We separately
test the four-variable owner-exhaustion law, which excludes that algebra.
The candidate even with exhaustion is refuted by the six-state certificate
in check_core_mixed.py. We also count models satisfying the missing mixed
absorption law; completeness of this further extension remains unproved.

Enumerates finite operation tables, up to isomorphism of their + reduct,
and tests their ENTIRE two-variable core theory via its finite free table.
It does not test their full core theory or impose a bound on irreducibles.
The search is outside make check and uses only the Python standard library.
"""

import argparse
from itertools import combinations, permutations, product

from core_basis import binary_product, binary_profiles, binary_term


def relabel(table, permutation):
    size = len(table)
    result = [[0] * size for _ in range(size)]
    for a, b in product(range(size), repeat=2):
        result[permutation[a]][permutation[b]] = permutation[table[a][b]]
    return tuple(tuple(row) for row in result)


def semilattices(size):
    """Every finite join order has a linear extension, so this is exhaustive."""
    pairs = tuple(combinations(range(size), 2))
    relabellings = tuple(permutations(range(size)))
    seen = set()
    for mask in range(1 << len(pairs)):
        upper = [1 << i for i in range(size)]
        for bit, (a, b) in enumerate(pairs):
            if mask & (1 << bit):
                upper[a] |= 1 << b
        if any(upper[b] & ~upper[a] for a, b in pairs if upper[a] & (1 << b)):
            continue  # not transitive
        table = [[a if a == b else 0 for b in range(size)] for a in range(size)]
        for a, b in pairs:
            common = upper[a] & upper[b]
            if not common:
                break
            least = (common & -common).bit_length() - 1
            if common & ~upper[least]:
                break
            table[a][b] = table[b][a] = least
        else:
            table = tuple(tuple(row) for row in table)
            if table in seen:
                continue
            for permutation in relabellings:
                renamed = relabel(table, permutation)
                if renamed not in seen:
                    seen.add(renamed)
                    yield renamed


def evaluate(term, values, add, operations):
    if term.op == 'var':
        return values[term.args[0]]
    if term.op == 'union':
        a, b = (evaluate(t, values, add, operations) for t in term.args)
        return add[a][b]
    owner, left, right = term.args
    return operations[owner][evaluate(left, values, add, operations)][
        evaluate(right, values, add, operations)]


PROFILES = binary_profiles(3)
TERMS = [binary_term(3, p) for p in PROFILES]
INDEX = {p: i for i, p in enumerate(PROFILES)}
PRODUCTS = [(i, a, b, INDEX[binary_product(i, p, q)])
            for i in range(3) for a, p in enumerate(PROFILES)
            for b, q in enumerate(PROFILES)]


def binary_failure(add, operations):
    for x, y in product(range(len(add)), repeat=2):
        values = [evaluate(t, (x, y), add, operations) for t in TERMS]
        for i, a, b, result in PRODUCTS:
            if operations[i][values[a]][values[b]] != values[result]:
                return i, a, b, result, x, y
    return None


def exhaustion_holds(add, operations):
    size = len(add)
    for marker in range(size):
        choices = [set(table[marker]) for table in operations]
        for x, y, z in product(*choices):
            cover = add[x][add[y][z]]
            if add[marker][cover] != cover:
                return False
    return True


def mixed_absorption_holds(add, operations):
    for a, b in combinations(range(len(operations)), 2):
        for first, second in ((a, b), (b, a)):
            m, p = operations[first], operations[second]
            for x, y, z in product(range(len(add)), repeat=3):
                yz = m[y][z]
                if m[x][p[y][yz]] != m[x][p[y][m[x][yz]]]:
                    return False
    return True


def candidate_models(size):
    """All models of the original candidate, up to isomorphism of join."""
    tables = list(semilattices(size))
    relabellings = tuple(permutations(range(size)))
    elements = range(size)
    seen = set()
    for add in tables:
        if add in seen:
            continue
        seen.update(relabel(add, p) for p in relabellings)
        compatible = [t for t in tables
                      if all(t[x][add[y][z]] == add[t[x][y]][t[x][z]]
                             for x, y, z in product(elements, repeat=3))]
        for ops in product(compatible, repeat=3):
            if not all(add[ops[i][x][y]][ops[j][x][y]] == add[x][y]
                       and ops[i][x][ops[j][x][y]] == ops[j][x][ops[i][x][y]]
                       for i, j in combinations(range(3), 2)
                       for x, y in product(elements, repeat=2)):
                continue
            if not all(ops[c][ops[a][x][y]][ops[b][x][y]] == add[x][y]
                       for a, b, c in permutations(range(3))
                       for x, y in product(elements, repeat=2)):
                continue
            yield add, ops


def search(size):
    count = exhausted = mixed = 0
    for add, ops in candidate_models(size):
        count += 1
        failure = binary_failure(add, ops)
        if failure is not None:
            raise AssertionError(('binary identity missing from candidate', add, ops, failure))
        if exhaustion_holds(add, ops):
            exhausted += 1
            mixed += mixed_absorption_holds(add, ops)
    print(f'size={size}: {count} candidate '
          f'models pass every binary identity; {exhausted} also satisfy exhaustion; '
          f'{mixed} satisfy exhaustion and mixed absorption.',
          flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--size', type=int, choices=range(2, 7), default=4)
    args = parser.parse_args()
    for size in range(2, args.size + 1):
        search(size)
