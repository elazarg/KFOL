"""Finite checks for the relative one-owner presentation.

The theorem for arbitrary conservative carriers has a written proof. These
checks compare the equations with the passing-relation criterion on every
forest-based candidate through size four, and test guard thresholds. The
nonconservative quotient is checked with the native winner-set evaluator.
"""

from itertools import combinations, product
from random import Random

from forest import forest_tables
from fragments import denote, h, reset, var
from one_owner import normal


def equations():
    x, y, z, u = map(var, range(4))
    return (
        ('R1', reset(x, x), x),
        ('R2', reset(reset(x, y), x), reset(y, x)),
        ('R3', reset(reset(x, y), y), reset(x, y)),
        ('R4', reset(x, reset(reset(x, y), z)), reset(x, reset(y, z))),
        ('R5', reset(reset(reset(x, y), z), y), reset(reset(x, z), y)),
        ('R6', reset(x, reset(y, z)), reset(y, reset(x, z))),
        ('H1', h(0, x, y, z), h(0, x, z, y)),
        ('H2', h(0, x, y, y), reset(y, x)),
        ('H3', h(0, x, x, y), reset(y, x)),
        ('H4', reset(h(0, x, y, z), x), h(0, x, y, z)),
        ('H5', reset(x, h(0, x, y, z)), h(0, x, y, z)),
        ('H6', h(0, x, reset(y, x), reset(z, x)),
         reset(reset(y, x), reset(z, x))),
        ('H7', h(0, x, reset(reset(z, y), x), y), reset(reset(z, y), x)),
        ('H8', h(0, reset(u, x), y, z), reset(reset(u, x), h(0, x, y, z))),
        ('H9', h(0, x, reset(u, x), reset(y, z)),
         reset(h(0, x, reset(u, x), z), reset(reset(y, z), x))),
        ('H10', h(0, x, reset(reset(u, x), reset(y, x)), z),
         reset(h(0, x, reset(u, x), z), h(0, x, reset(y, x), z))),
        ('H11', reset(h(0, y, u, z), x), reset(reset(h(0, x, u, z), y), x)),
    )


def variables(term):
    if term.op == 'var':
        return {term.args[0]}
    children = term.args if term.op == 'reset' else term.args[1:]
    return set().union(*(variables(child) for child in children))


def evaluate(term, inputs, r, hh):
    if term.op == 'var':
        return inputs[term.args[0]]
    if term.op == 'reset':
        return r[evaluate(term.args[0], inputs, r, hh)][
            evaluate(term.args[1], inputs, r, hh)]
    return hh[evaluate(term.args[1], inputs, r, hh)][
        evaluate(term.args[2], inputs, r, hh)][evaluate(term.args[3], inputs, r, hh)]


def satisfies(r, hh, laws):
    for _, left, right in laws:
        names = sorted(variables(left) | variables(right))
        for values in product(range(len(r)), repeat=len(names)):
            inputs = dict(zip(names, values))
            if evaluate(left, inputs, r, hh) != evaluate(right, inputs, r, hh):
                return False
    return True


def candidates(size):
    """All choices left open by the three-element forest classification."""
    for r in forest_tables(size):
        hh = [[[r[r[y][x]][r[z][x]] for z in range(size)]
               for y in range(size)] for x in range(size)]
        slots = []
        for triple in combinations(range(size), 3):
            edges = [(x, y) for x, y in product(triple, repeat=2)
                     if x != y and r[x][y] == r[y][x] == y]
            if len(edges) == 1:
                x, y = edges[0]
                slots.append((x, y, next(z for z in triple if z not in (x, y))))
        for bits in product((False, True), repeat=len(slots)):
            for (x, y, z), blocked in zip(slots, bits):
                hh[x][y][z] = hh[x][z][y] = x if blocked else y
            yield r, hh


def coherent(r, hh):
    """The passing relation, independently of equation evaluation."""
    size = len(r)
    le = lambda x, y: r[x][y] == r[y][x] == y
    inc = lambda x, y: not le(x, y) and not le(y, x)
    passing = {}
    for b, z in product(range(size), repeat=2):
        lowers = [x for x in range(size) if x != b and le(x, b)]
        if not lowers or not inc(b, z):
            continue
        values = {hh[x][b][z] == b for x in lowers}
        if len(values) != 1:
            return None
        passing[b, z] = values.pop()
    for (b, z), passed in passing.items():
        for c in range(size):
            if le(b, c) and inc(c, z) and passed and not passing[c, z]:
                return None
            if le(z, c) and inc(b, c) and passing[b, c] != passed:
                return None
    return passing


def check_thresholds(r, hh, passing, rng):
    size = len(r)
    le = lambda x, y: r[x][y] == r[y][x] == y
    terms = [var(i) for i in range(size)]
    for _ in range(35):
        children = rng.choices(terms, k=3)
        terms.append(reset(*children[:2]) if rng.randrange(2) else h(0, *children))
    for term in terms:
        form = normal(term, 0, size)
        for _ in range(8):
            inputs = tuple(rng.randrange(size) for _ in range(size))
            value = evaluate(term, inputs, r, hh)
            assert le(inputs[form.root], value)
            for b in range(size):
                if not any(x != b and le(x, b) for x in range(size)):
                    continue
                m = sum(1 << j for j, x in enumerate(inputs) if le(x, b))
                n = sum(1 << j for j, x in enumerate(inputs)
                        if le(x, b) or le(b, x) or passing.get((b, x), False))
                fitting = any(x == b and any(a & m == a and c & n == c
                              for a, c in form.other[j]) for j, x in enumerate(inputs))
                assert value != b or fitting
                assert not fitting or le(b, value)


def check_quotient():
    # 0,p,q,1 are numbered 0,1,2,3. Native A,N,P winner sets are 1,3,7.
    r = tuple(tuple(3 if y == 0 and x != 0 else y for y in range(4))
              for x in range(4))
    hh = tuple(tuple(tuple(x if x != 0 else
                           (0 if (y, z) in ((0, 0), (1, 2), (2, 1)) else 3)
                           for z in range(4)) for y in range(4)) for x in range(4))
    quotient = {(3, 3): 0, (7, 1): 1, (1, 7): 2,
                (7, 3): 3, (3, 7): 3, (7, 7): 3}
    x, y, z = map(var, range(3))
    for a, b in product(quotient, repeat=2):
        result = tuple(denote(reset(x, y), (a[i], b[i])) for i in range(2))
        assert result in quotient
        assert quotient[result] == r[quotient[a]][quotient[b]]
    for a, b, c in product(quotient, repeat=3):
        result = tuple(denote(h(0, x, y, z), (a[i], b[i], c[i])) for i in range(2))
        assert result in quotient
        assert quotient[result] == hh[quotient[a]][quotient[b]][quotient[c]]
    assert r[1][0] not in (1, 0)
    collapse = (0, 1, 2, 0)
    for a, b, c in product(range(4), repeat=3):
        assert collapse[r[a][b]] == collapse[b]
        assert collapse[hh[a][b][c]] == collapse[a]
    contexts = (tuple(range(4)), tuple(r[a][0] for a in range(4)),
                tuple(hh[0][a][1] for a in range(4)),
                tuple(hh[0][a][2] for a in range(4)))
    for a, b in combinations(range(4), 2):
        assert any({f[a], f[b]} == {0, 3} for f in contexts)


def check_relative_obstruction(laws):
    # Greatest element 0 above the three incomparable elements 1,2,3.
    r = tuple(tuple(x if x == y else 0 for y in range(4)) for x in range(4))
    hh = tuple(tuple(tuple(3 if x == 3 and {y, z} == {1, 2} else r[r[x][y]][z]
                           for z in range(4)) for y in range(4)) for x in range(4))
    assert satisfies(r, hh, laws)
    x, y, z = map(var, range(3))
    insertion = (h(0, x, y, z), h(0, x, reset(x, y), z))
    assert normal(insertion[0], 0, 3) == normal(insertion[1], 0, 3)
    for inputs in product((1, 2, 3, 7), repeat=3):
        assert denote(insertion[0], inputs) == denote(insertion[1], inputs)
    assert evaluate(insertion[0], (3, 1, 2), r, hh) == 3
    assert evaluate(insertion[1], (3, 1, 2), r, hh) == 0


def check():
    laws = equations()
    for name, left, right in laws:
        assert normal(left, 0, 4) == normal(right, 0, 4), name
        names = sorted(variables(left) | variables(right))
        for values in product((1, 2, 3, 7), repeat=len(names)):
            inputs = dict(zip(names, values))
            assert denote(left, inputs) == denote(right, inputs), name
    rng = Random(1705)
    counts = []
    # Larger laws first reject invalid candidates without repeating small laws.
    ordered = laws[13:] + laws[:13]
    for size in range(1, 5):
        total = accepted = 0
        for r, hh in candidates(size):
            total += 1
            relation = coherent(r, hh)
            valid = satisfies(r, hh, ordered)
            assert valid == (relation is not None)
            if valid:
                accepted += 1
                check_thresholds(r, hh, relation, rng)
        counts.append((total, accepted))
    assert counts == [(1, 1), (3, 3), (22, 22), (569, 281)], counts
    check_relative_obstruction(laws)
    check_quotient()
    print('Owner presentation: all 17 identities, passing-relation agreement '
          f'{counts}, sampled guard thresholds, the relative-presentation '
          'counterexample, and nonconservative irreducible quotient passed.')


if __name__ == '__main__':
    check()
