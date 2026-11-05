"""Exact native audit of the frontier proof of relative exhaustion completeness.

The all-K proof is written in the core-basis appendix. Here bit profiles
evaluate every assignment, including every possible n/p defect consistent
with all owner-deleted evaluations. The synthetic upper profiles need not
be terms: the scalar refinement argument applies to this larger test set.
No finite audit alone establishes the relative theorem or finite basability.
"""
from itertools import permutations, product
from random import Random
import json


class Profiles:
    def __init__(self, owners, arity):
        self.k = owners
        self.valuations = list(product(range(owners + 2), repeat=arity))
        self.mask = (1 << len(self.valuations)) - 1
        self.variables = [tuple(
            sum(1 << j for j, v in enumerate(self.valuations) if v[a] == x)
            for x in (*range(owners), owners + 1)) for a in range(arity)]
        lookup = {v: j for j, v in enumerate(self.valuations)}
        self.deleted = [tuple(
            lookup[tuple(owners if x == i else x for x in v)]
            for i in range(owners)) for v in self.valuations]
        self.top = (0,) * owners + (self.mask,)

    def app(self, operation, a, b):
        atoms = tuple(a[i] & b[i] for i in range(self.k))
        if operation == self.k:
            return atoms + (a[-1] | b[-1],)
        absorb = a[operation] | b[operation]
        atoms = tuple(absorb if i == operation else atoms[i]
                      for i in range(self.k))
        return atoms + ((a[-1] | b[-1]) & (self.mask ^ absorb),)

    def fold(self, operation, values):
        result = values[0]
        for value in values[1:]:
            result = self.app(operation, result, value)
        return result

    def below(self, a, b):
        assert not (a[-1] & ~b[-1])
        assert all(not (b[i] & ~a[i]) for i in range(self.k))

    def shadow(self, value):
        markers = self.mask
        for bitset in value:
            markers &= ~bitset
        defects = 0
        while markers:
            bit = markers & -markers
            index = bit.bit_length() - 1
            markers ^= bit
            if all(value[-1] >> j & 1 for j in self.deleted[index]):
                defects |= bit
        return value[:-1] + (value[-1] | defects,), defects

    def audit(self, tree):
        nodes = []

        def flatten(term):
            if isinstance(term, int):
                nodes.append((None, None, None, self.variables[term]))
            else:
                op, left, right = term
                a, b = flatten(left), flatten(right)
                nodes.append((op, a, b, self.app(op, nodes[a][3], nodes[b][3])))
            return len(nodes) - 1

        root = flatten(tree)
        source = nodes[root][3]
        target, defects = self.shadow(source)

        def frontiers(node):
            op, a, b, _ = nodes[node]
            if op is None:
                return [(node,)]
            return [(node,)] + [left + right
                               for left in frontiers(a) for right in frontiers(b)]

        data = {}
        for frontier in frontiers(root):
            cuts = set(frontier)
            word = []

            def visit(node):
                if node in cuts:
                    return
                _, a, b, _ = nodes[node]
                visit(a)
                visit(b)
                word.append(node)

            visit(root)

            def context(value):
                for node in word:
                    op, _, _, coefficient = nodes[node]
                    value = self.app(op, coefficient, value)
                return value

            coefficients = [nodes[node][3] for node in frontier]
            bound = self.fold(self.k, coefficients)
            assert context(source) == source
            assert context(bound) == source
            active = 0
            for node in word:
                op, _, _, coefficient = nodes[node]
                if op != self.k:
                    active |= coefficient[op]
            is_n = self.mask
            for bitset in source:
                is_n &= ~bitset
            top_image = context(self.top)
            assert not ((top_image[-1] ^ ~active) & is_n)
            assert all(not (bits & is_n) for bits in top_image[:-1])

            folds = [self.fold(i, coefficients) for i in range(self.k)]
            lower = self.fold(self.k, [self.app(i, target, folds[i])
                                       for i in range(self.k)])
            data[frontier] = (context(lower),
                              context(self.app(self.k, target, lower)))

        for frontier, (lower, upper) in data.items():
            rhs = source
            self.below(lower, upper)
            self.below(upper, target)
            for node in frontier:
                op, a, b, _ = nodes[node]
                if op is None:
                    continue
                refined = tuple(sorted([x for x in frontier if x != node] + [a, b]))
                rhs = self.app(self.k, rhs, data[refined][1])
            self.below(lower, rhs)
        assert data[(root,)][1] == target
        full = tuple(i for i, node in enumerate(nodes) if node[0] is None)
        self.below(data[full][0], source)
        return len(data), defects.bit_count()


def samples(owners):
    rng = Random(2903)
    if owners == 3:
        for order in permutations(range(3)):
            a, b, c = [(i, 3, i) for i in order]
            for op, other in product(range(4), repeat=2):
                yield op, a, (other, b, c)
        trials = 240
    else:
        atoms = [(i, owners, i) for i in range(owners)]
        for op, other in product(range(owners + 1), repeat=2):
            yield op, (other, atoms[0], atoms[1]), (owners, atoms[2], atoms[3])
        trials = 80
    for trial in range(trials):
        count = owners + 1 + trial % 4
        nodes = [(i % owners, owners + (i + trial) % 2, i % owners)
                 for i in range(count)]
        rng.shuffle(nodes)
        while len(nodes) > 1:
            a = nodes.pop(rng.randrange(len(nodes)))
            b = nodes.pop(rng.randrange(len(nodes)))
            nodes.append((rng.randrange(owners + 1), a, b))
        yield nodes[0]


def check():
    results = []
    for owners in (3, 4):
        profiles = Profiles(owners, owners + 2)
        terms = frontiers = nontrivial = defects = 0
        for tree in samples(owners):
            count, failures = profiles.audit(tree)
            terms += 1
            frontiers += count
            nontrivial += failures > 0
            defects += failures
        assert nontrivial and defects
        results.append({'owners': owners, 'variables': owners + 2,
                        'assignments_per_term': len(profiles.valuations),
                        'terms': terms, 'frontiers': frontiers,
                        'nontrivial_shadow_terms': nontrivial,
                        'defect_term_valuation_pairs': defects})
    print(json.dumps({'status': 'all assertions passed', 'cases': results,
                      'cutoffs': 0}, indent=2))


if __name__ == '__main__':
    check()
