"""Independent exhaustive bit-parallel checks of the small hard fragments.

Each bit denotes one valuation over *all* nonempty winner sets. This is
native set evaluation, not the proposed reduction's Boolean abstraction.
Scalar evaluation independently checks the extracted witnesses and samples.
"""
from itertools import combinations, product
from random import Random

from fragments import colouring_identity, denote, h_reduction, size, union_reduction


def repeat_bits(pattern, width, count):
    result = offset = 0
    while count:
        if count & 1:
            result |= pattern << offset
            offset += width
        count >>= 1
        if count:
            pattern |= pattern << width
            width *= 2
    return result


class Valuations:
    def __init__(self, roles, arity):
        self.roles, self.arity = roles, arity
        self.base = (1 << roles) - 1
        self.count = self.base ** arity
        self.rows = []
        for i in range(arity):
            block = self.base ** (arity - i - 1)
            unit = (1 << block) - 1
            self.rows.append(tuple(repeat_bits(
                sum(unit << (j * block) for j in range(self.base) if (j+1) & (1 << r)),
                block * self.base, self.base ** i) for r in range(roles)))
        rng = Random(901 + arity + roles)
        for index in [0, self.count - 1] + [rng.randrange(self.count) for _ in range(40)]:
            values = self.decode(index)
            assert all(((self.rows[i][r] >> index) & 1) == bool(values[i] & (1 << r))
                       for i in range(arity) for r in range(roles))

    def decode(self, index):
        values = []
        for _ in range(self.arity):
            values.append(index % self.base + 1)
            index //= self.base
        return tuple(reversed(values))

    @staticmethod
    def multiple(rows):
        result = 0
        for first, second in combinations(rows, 2):
            result |= first & second
        return result

    def evaluate(self, term, cache):
        if term in cache:
            return cache[term]
        if term.op == 'var':
            result = self.rows[term.args[0]]
        elif term.op == 'union':
            a, b = (self.evaluate(t, cache) for t in term.args)
            result = tuple(x | y for x, y in zip(a, b))
        elif term.op == 'reset':
            a, b = (self.evaluate(t, cache) for t in term.args)
            ambiguous = self.multiple(b)
            result = tuple(y | (ambiguous & x) for x, y in zip(a, b))
        else:
            owner, root, left, right = term.args
            root, left, right = (self.evaluate(t, cache) for t in (root, left, right))
            def singleton(rows):
                others = 0
                for i, row in enumerate(rows):
                    if i != owner:
                        others |= row
                return rows[owner] & ~others
            collapse = singleton(left) | singleton(right)
            ambiguous = self.multiple(root)
            result = tuple(z | (ambiguous & ((collapse if i == owner else 0)
                                  | ((x | y) & ~collapse)))
                           for i, (z, x, y) in enumerate(zip(root, left, right)))
        cache[term] = result
        return result

    def check(self, pair, valid):
        cache = {}
        left, right = (self.evaluate(t, cache) for t in pair)
        difference = 0
        for x, y in zip(left, right):
            difference |= x ^ y
        assert (difference == 0) == valid
        rng = Random(size(pair[0]))
        indices = [rng.randrange(self.count) for _ in range(2)]
        if difference:
            indices.append((difference & -difference).bit_length() - 1)
        for index in indices:
            values = self.decode(index)
            for term, rows in zip(pair, (left, right)):
                actual = sum(((row >> index) & 1) << r for r, row in enumerate(rows))
                assert actual == denote(term, values)
            if (difference >> index) & 1:
                assert denote(pair[0], values) != denote(pair[1], values)


def cnfs(n):
    # All sets of non-tautological clauses, including an empty clause.
    clauses = []
    for statuses in product((-1, 0, 1), repeat=n):
        clauses.append(tuple((i, sign == 1) for i, sign in enumerate(statuses) if sign))
    result = {tuple(clauses[i] for i in range(len(clauses)) if mask & (1 << i))
              for mask in range(1 << len(clauses))}
    # Also include all pairs of arbitrary nonempty clauses (tautologies allowed).
    literals = tuple(product(range(n), (False, True)))
    arbitrary = [tuple(literals[i] for i in range(len(literals)) if mask & (1 << i))
                 for mask in range(1, 1 << len(literals))]
    result.update(tuple(sorted(set(pair))) for pair in product(arbitrary, repeat=2))
    return sorted(result)


def satisfiable(cnf, n):
    return any(all(any(bits[i] == sign for i, sign in clause) for clause in cnf)
               for bits in product((False, True), repeat=n))


def check_reductions():
    for n in (1, 2):
        examples = cnfs(n)
        owner_free, atom_preserving = Valuations(3, 2*n+3), Valuations(3, n+2)
        for cnf in examples:
            sat = satisfiable(cnf, n)
            owner_free.check(union_reduction(cnf, n), not sat)
            atom_preserving.check(h_reduction(cnf, n), not sat)
        print(f"K=3: {len(examples)} CNFs on {n} variables; reset/union checked on all "
              f"{owner_free.count} valuations each; H_a/H_b on all {atom_preserving.count}", flush=True)
    # A separate larger carrier, with all mixed valuations.
    vals = Valuations(4, 5)
    for cnf in cnfs(1):
        vals.check(union_reduction(cnf, 1), not satisfiable(cnf, 1))
    print(f"K=4: one-variable reset/union reductions, all {vals.count} valuations each", flush=True)


def check_colouring():
    for k in (3, 4):
        vals = Valuations(k, k+2)
        vals.check(colouring_identity(k), True)
        # The same identity fails with one extra role, uniformly in k.
        inputs = tuple(1 << i for i in range(k)) + (3, 1 << k)
        left, right = colouring_identity(k)
        assert denote(left, inputs) != denote(right, inputs)
        print(f"Colouring identity: valid at K={k} on all {vals.count} valuations; "
              f"explicit counterexample at K={k+1}", flush=True)


if __name__ == '__main__':
    check_reductions()
    check_colouring()
