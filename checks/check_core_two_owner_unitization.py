"""Check the unitization embedding and the executable constant elimination."""

from itertools import product
from random import Random

from core_atomic_basis import semilattice_laws, variables
from core_basis import marker_join, marker_own, mixed_absorption
from core_two_owner_unitization import UNIT, eliminate_unit, evaluate, tagged_term, unitize
from fragments import owned, union, var


def check():
    carrier = range(4)
    d = [[[op(x, y) for y in carrier] for x in carrier] for op in (
        lambda x, y: marker_join(2, x, y),
        lambda x, y: marker_own(2, 0, x, y),
        lambda x, y: marker_own(2, 1, x, y))]
    extended = unitize(d)
    embedding = [
        (0, 0, 0), (0, 1, 3), (0, 2, 3), (0, 3, 3),
        (2, 2, 2), (2, 1, 3), (2, 2, 3), (2, 3, 3), (1, 1, 1),
    ]
    assert len(set(embedding)) == 9
    comparisons = 0
    for source, target in zip(extended, d):
        for x, y in product(range(9), repeat=2):
            assert embedding[source[x][y]] == tuple(target[a][b]
                                                   for a, b in zip(embedding[x], embedding[y]))
            comparisons += 3
    assert all(extended[1][8][x] == x and extended[2][8][x] == 8 for x in range(9))

    # Check the natural embedding U(D x D) into U(D) x U(D).
    square = [[[4 * op[x // 4][y // 4] + op[x % 4][y % 4]
                for y in range(16)] for x in range(16)] for op in d]
    product_extension = unitize(square)
    natural = [(x // 4, x % 4) for x in range(16)]
    natural += [(4 + x // 4, 4 + x % 4) for x in range(16)] + [(8, 8)]
    assert len(set(natural)) == 33
    for source, target in zip(product_extension, extended):
        for x, y in product(range(33), repeat=2):
            assert natural[source[x][y]] == tuple(target[a][b]
                                                 for a, b in zip(natural[x], natural[y]))

    # These are test identities, not a claimed basis for D or (D,b).
    x, y, z = map(var, range(3))
    laws = semilattice_laws(union, 'join')
    for i in (0, 1):
        operation = lambda a, b, i=i: owned(i, a, b)
        laws += semilattice_laws(operation, str(i))
        laws.append(('distribution', operation(x, union(y, z)),
                     union(operation(x, y), operation(x, z))))
        laws.append(('mixed', *mixed_absorption(i, 1 - i)))
    laws += [('coverage', union(owned(0, x, y), owned(1, x, y)), union(x, y)),
             ('birkhoff', owned(0, x, owned(1, x, y)), owned(1, x, owned(0, x, y))),
             ('unit', owned(0, UNIT, x), x), ('absorber', owned(1, UNIT, x), UNIT)]
    equations = [(left, right) for _, left, right in laws]
    translated = eliminate_unit(equations)
    assert len(translated) <= sum(3 ** len(variables(a) | variables(b)) for a, b in equations)
    for left, right in translated:
        used = sorted(variables(left) | variables(right))
        assert set(used) <= {0, 1, 2}
        for values in product(carrier, repeat=len(used)):
            valuation = dict(zip(used, values))
            assert evaluate(left, valuation, d) == evaluate(right, valuation, d)
    try:
        eliminate_unit([(UNIT, x)])
    except ValueError:
        pass
    else:
        raise AssertionError('accepted incompatible tags')

    # The reduction is valid for arbitrary base algebras, not only for models
    # of the core laws. Use noncommutative random tables to audit every case.
    rng = Random(40159)
    terms = [UNIT, x, y, z] + [side for pair in equations for side in pair]
    reductions = 0
    for size in (2, 3, 4):
        arbitrary = [[[rng.randrange(size) for _ in range(size)]
                      for _ in range(size)] for _ in range(3)]
        lifted = unitize(arbitrary)
        for term in terms:
            used = sorted(variables(term))
            for values in product(range(2 * size + 1), repeat=len(used)):
                valuation = dict(zip(used, values))
                forms = {i: 2 if value == 2 * size else value // size
                         for i, value in valuation.items()}
                payloads = {i: value % size for i, value in valuation.items()}
                tag, payload = tagged_term(term, forms)
                expected = (2 * size if tag == 2 else
                            tag * size + evaluate(payload, payloads, arbitrary))
                assert evaluate(term, valuation, lifted, 2 * size) == expected
                reductions += 1
    print(f'Two-owner unitization: nine-element pointed embedding, {comparisons} '
          'coordinate checks; the 33-element product unitization embeds '
          f'naturally; {len(equations)} sample pointed identities give '
          f'{len(translated)} valid constant-free identities, and {reductions} '
          'tag reductions pass on arbitrary noncommutative tables. '
          'Incompatible tags are rejected. No complete basis is asserted.')


if __name__ == '__main__':
    check()
