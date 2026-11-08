"""Independent finite checks of one common source in the full signature.

Enumerate actual leaf paths and the switches on each path, then evaluate the
leaf by applying those switches from the leaf outward. For two valuations we
check every disjoint pair of outputs. For three roles, three disjoint nonempty
outputs must be the three atoms, so their fibers enumerate all such triples up
to reindexing. Using the output sets as regions gives the strongest constraints.
The generic proof, including arbitrary index types, is in Lean.
"""

from itertools import combinations, permutations, product
from random import Random

from structure import Choice, Var, Win
from symmetric import Rename, evaluate, move


def leaf_paths(term):
    pending = [(term, (), ())]
    leaves = []
    while pending:
        node, path, actions = pending.pop()
        if isinstance(node, (Win, Var)):
            leaves.append((path, node, actions))
        elif isinstance(node, Rename):
            pending.append((node.child, path + ("switch",), actions + (node.permutation,)))
        else:
            pending.append((node.right, path + ("right",), actions))
            pending.append((node.left, path + ("left",), actions))
    return leaves


def source_value(leaf, actions, inputs):
    value = (1 << leaf.role) if isinstance(leaf, Win) else inputs[leaf.index]
    for action in reversed(actions):
        value = move(action, value)
    return value


def main():
    rng = Random(20261109)
    roles, arity = 3, 2
    ps = tuple(permutations(range(roles)))
    base = [Var(i) for i in range(arity)] + [Win(r) for r in range(roles)]
    terms = base + [Choice(r, a, b) for r in range(roles) for a, b in product(base, repeat=2)]
    terms += [Rename(p, a) for p, a in product(ps, base)]

    def random_term(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return rng.choice(base)
        if rng.randrange(3) == 0:
            return Rename(rng.choice(ps), random_term(depth - 1))
        return Choice(rng.randrange(roles), random_term(depth - 1), random_term(depth - 1))

    terms += [random_term(5) for _ in range(100)]
    valuations = tuple(product(range(1, 1 << roles), repeat=arity))
    pairs = triples = atomic_triples = 0
    for term in terms:
        leaves = leaf_paths(term)
        input_mask = sum(1 << j for j, (_, leaf, _) in enumerate(leaves) if isinstance(leaf, Var))
        outputs = tuple(evaluate(term, v) for v in valuations)
        candidates = tuple(sum(1 << j for j, (_, leaf, actions) in enumerate(leaves)
                               if source_value(leaf, actions, v) & ~out == 0)
                           for v, out in zip(valuations, outputs))
        assert all(candidates), "Even one region needs a source."
        for i, j in combinations(range(len(valuations)), 2):
            if outputs[i] & outputs[j] == 0:
                common = candidates[i] & candidates[j]
                assert common and common & ~input_mask == 0
                pairs += 1
        fibers = [[i for i, out in enumerate(outputs) if out == 1 << r] for r in range(roles)]
        for indices in product(*fibers):
            common = candidates[indices[0]] & candidates[indices[1]] & candidates[indices[2]]
            assert common and common & ~input_mask == 0
            triples += 1
            rows = tuple(valuations[i] for i in indices)
            if all(value.bit_count() == 1 for row in rows for value in row):
                assert any(len({row[x] for row in rows}) == 3 for x in range(arity))
                atomic_triples += 1
    print(f"Common source: {len(terms)} full-language terms; {pairs} disjoint output pairs; "
          f"{triples} disjoint triples; {atomic_triples} atomic triples satisfy the repeat obstruction.")


if __name__ == "__main__":
    main()
