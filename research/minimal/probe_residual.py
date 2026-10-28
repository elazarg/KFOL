"""Exploratory SI-quotient search in a small subpower of the full algebra.

This is not a residual-bound algorithm. It samples maximal congruences
avoiding a protected pair in the 79-element subalgebra of A_3^3 generated
by the tuple ({a},{b},{a,b}) and the diagonal constants. Maximality and
compatibility are checked independently before reporting a quotient.
"""

from collections import deque
from itertools import permutations, product
from random import Random

from symmetric import move, own


def generated_subalgebra(seed):
    count = len(seed)
    values = {(i,) * count for i in (1, 2, 4)} | {seed}
    queue = deque(values)
    while queue:
        first = queue.popleft()
        extensions = [tuple(move(p, x) for x in first) for p in permutations(range(3))]
        extensions += [tuple(own(r, x, y) for x, y in zip(first, second))
                       for second in list(values) for r in range(3)]
        for value in extensions:
            if value not in values:
                values.add(value)
                queue.append(value)
    return sorted(values)


def root(partition, element):
    while partition[element] != element:
        element = partition[element]
    return element


def merge_congruence(partition, first, second, operations):
    result = partition.copy()
    pending = [(first, second)]
    while pending:
        a, b = pending.pop()
        a, b = root(result, a), root(result, b)
        if a != b:
            result[b] = a
            pending.extend((operation[a], operation[b]) for operation in operations)
    return result


def main():
    values = generated_subalgebra((1, 2, 3))
    assert len(values) == 79
    indices = {value: i for i, value in enumerate(values)}
    operations = [tuple(indices[tuple(move(p, x) for x in value)] for value in values)
                  for p in permutations(range(3))]
    operations += [tuple(indices[tuple(own(r, x, y) for x, y in zip(a, b))] for a in values)
                   for r in range(3) for b in values]
    rng = Random(49)
    sizes = []
    for trial in range(8):
        first, second = rng.sample(range(len(values)), 2)
        partition = list(range(len(values)))
        pairs = list(product(range(len(values)), repeat=2))
        rng.shuffle(pairs)
        for a, b in pairs:
            if a < b and root(partition, a) != root(partition, b):
                candidate = merge_congruence(partition, a, b, operations)
                if root(candidate, first) != root(candidate, second):
                    partition = candidate
        classes = {root(partition, a) for a in range(len(values))}
        # Every fundamental unary translation preserves the partition.
        for operation in operations:
            table = {}
            for a in range(len(values)):
                source, target = root(partition, a), root(partition, operation[a])
                assert source not in table or table[source] == target
                table[source] = target
        # Every strict extension identifies the protected pair: SI certificate.
        assert all(root((candidate := merge_congruence(partition, a, b, operations)), first)
                   == root(candidate, second) for a, b in product(classes, repeat=2) if a < b)
        sizes.append(len(classes))
        print(f"Trial {trial}: certified SI quotient of size {len(classes)}.")
    print(f"Observed sizes: {sorted(set(sizes))}. No residual bound is inferred.")


if __name__ == "__main__":
    main()
