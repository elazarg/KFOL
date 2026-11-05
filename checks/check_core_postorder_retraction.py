"""Audit candidate postorder retractions and each frontier contraction.

The proof applies to arbitrary algebras. This independent table audit
checks every three-variable valuation for five term shapes in the stored
models, and every element of the generated subalgebra as context input.
"""
from functools import reduce
from itertools import product
import json

from check_core_owned_reset import test_models
from check_core_upper_bound_extension import close


def check():
    valuations = contractions = inputs = models = 0
    for join, choices in test_models():
        size = len(join)
        if size > 25:
            continue
        models += 1
        plus = len(choices)
        operations = choices + [join]
        shapes = [
            (0, (0, 0, 1), 2),
            (plus, (0, 0, 1), (1, 1, 2)),
            (0, (1, 0, 1), (1, 2, (0, 0, 2))),
            (0, (1, 0, 1), (2, 1, 2)),
            (0, (plus, 0, 1), (1, 1, 2)),
        ]
        compiled = []
        for shape in shapes:
            nodes = []

            def compile_tree(tree):
                if isinstance(tree, int):
                    nodes.append((None, tree, None))
                else:
                    op, left, right = tree
                    a, b = compile_tree(left), compile_tree(right)
                    nodes.append((op, a, b))
                return len(nodes) - 1

            compile_tree(shape)
            compiled.append(nodes)
        generated_cache = {}
        for values in product(range(size), repeat=3):
            key = frozenset(values)
            if key not in generated_cache:
                generated_cache[key] = close(values, [join] + choices)
            generated = generated_cache[key]
            upper = reduce(lambda a, b: join[a][b], values)
            for nodes in compiled:
                node_values = []
                frontier = set()
                for index, (op, a, b) in enumerate(nodes):
                    if op is None:
                        node_values.append(values[a])
                        frontier.add(index)
                    else:
                        node_values.append(operations[op][node_values[a]][node_values[b]])
                running = upper
                for index, (op, a, b) in enumerate(nodes):
                    if op is None:
                        continue
                    assert {a, b} <= frontier
                    coefficient = node_values[index]
                    running = operations[op][coefficient][running]
                    frontier.difference_update((a, b))
                    frontier.add(index)
                    bound = reduce(lambda x, y: join[x][y],
                                   (node_values[x] for x in frontier))
                    assert join[running][bound] == bound
                    contractions += 1
                target = node_values[-1]
                assert running == target
                for start in generated:
                    result = start
                    for index, (op, _, _) in enumerate(nodes):
                        if op is not None:
                            result = operations[op][node_values[index]][result]
                    assert result == target
                    inputs += 1
                valuations += 1
    print(json.dumps({'status': 'all assertions passed', 'models': models,
                      'term_valuations': valuations,
                      'frontier_contractions': contractions,
                      'generated_subalgebra_inputs': inputs}, indent=2))


if __name__ == '__main__':
    check()
