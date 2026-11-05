"""Audit the witnesses in the unbounded branching-rank proof.

The proof covers every height. This check independently evaluates the first
three heights, including every four-valued input and every Boolean edge used
in the factorization lemma. It does not enumerate terms or prove a finite
basis. ZERO and ONE are beta and alpha in the paper's four-element observer.
"""

from collections import Counter
from itertools import product

ZERO, ONE, N, P = range(4)


def operation(owner, x, y):
    if owner in (ZERO, ONE) and owner in (x, y):
        return owner
    return x if x == y else (P if P in (x, y) else N)


def tree(height, owner=ONE, first=0):
    if not height:
        return first
    width = 2 ** (height - 1)
    return (owner, tree(height - 1, 1 - owner, first),
            tree(height - 1, 1 - owner, first + width))


def support(t):
    if isinstance(t, int):
        return (t,)
    return support(t[1]) + support(t[2])


def evaluate(t, values):
    if isinstance(t, int):
        return values[t]
    return operation(t[0], evaluate(t[1], values), evaluate(t[2], values))


def marked_value(values, truth):
    """Least possible marker output for the given Boolean function."""
    base = sum(1 << i for i, x in enumerate(values) if x == ONE)
    completions = [base]
    marked = []
    for i, x in enumerate(values):
        if x in (N, P):
            completions += [v | (1 << i) for v in completions]
        if x == P:
            marked.append(i)
    outputs = {truth[v] for v in completions}
    if len(outputs) == 1:
        return outputs.pop()
    for i in marked:
        if any(truth[v] != truth[v | (1 << i)]
               for v in completions if not v & (1 << i)):
            return P
    return N


def edge_witness(t, side, values, variable):
    """Expose an edge within a child fiber at a target value of N."""
    child, other = t[1 + side], t[2 - side]
    endpoint = evaluate(child, values)
    witness = list(values)
    witness[variable] = P
    for i in support(other):
        witness[i] = N
    if endpoint == t[0]:
        # The child has the opposite root: free its sibling branch.
        assert not isinstance(child, int)
        sibling = child[2] if variable in support(child[1]) else child[1]
        for i in support(sibling):
            witness[i] = N
    return witness


def audit(height, owner):
    t = tree(height, owner)
    arity = 2 ** height
    rows = [tuple((v >> i) & 1 for i in range(arity))
            for v in range(2 ** arity)]
    truth = [evaluate(t, row) for row in rows]
    counts = Counter()
    for values in product(range(4), repeat=arity):
        assert evaluate(t, values) == marked_value(values, truth)
        counts['marker_profiles'] += 1

    parent = list(range(len(rows)))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for side in (0, 1):
        child = t[1 + side]
        for v, values in enumerate(rows):
            for i in support(child):
                if v & (1 << i):
                    continue
                w = v | (1 << i)
                if evaluate(child, values) != evaluate(child, rows[w]):
                    continue
                witness = edge_witness(t, side, values, i)
                assert evaluate(t, witness) == N
                assert witness[i] == P
                assert all(x in (N, P) or x == y
                           for x, y in zip(witness, values))
                parent[root(v)] = root(w)
                counts['fiber_edges'] += 1
    # The exposed edges identify exactly the four pairs of child values.
    classes = {}
    for v, values in enumerate(rows):
        pair = evaluate(t[1], values), evaluate(t[2], values)
        classes.setdefault(pair, set()).add(root(v))
    assert len(classes) == 4
    assert all(len(c) == 1 for c in classes.values())
    assert len({root(v) for v in range(len(rows))}) == 4
    counts['factorizations'] += 1
    return counts


def main():
    # Independently check the observer used to transfer the result to the core.
    observe = {1: ONE, 2: ZERO, 3: N, 4: P, 5: P, 6: P, 7: P}
    for x, y in product(range(1, 8), repeat=2):
        assert observe[x | y] == operation(None, observe[x], observe[y])
        for owner, tag in ((0, ONE), (1, ZERO), (2, None)):
            atom = 1 << owner
            value = atom if atom in (x, y) else x | y
            assert observe[value] == operation(
                tag, observe[x], observe[y])
    total = Counter()
    for height in (1, 2, 3):
        for owner in (ZERO, ONE):
            total.update(audit(height, owner))
    print('PASS branching-rank proof audit:', dict(total))


if __name__ == '__main__':
    main()
