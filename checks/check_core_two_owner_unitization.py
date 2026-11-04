"""Check the unitization embedding and the executable constant elimination."""

from itertools import product
from random import Random

from core_atomic_basis import semilattice_laws, variables
from core_basis import marker_join, marker_own, mixed_absorption
from core_two_owner_unitization import (
    OPPOSITE_UNIT, UNIT, double_tagged_term, eliminate_unit, eliminate_units,
    evaluate, tagged_term, unitize,
)
from fragments import owned, union, var


def function_closure(tables, arity, constants=()):
    valuations = list(product(range(len(tables[0])), repeat=arity))
    functions = [tuple(values[i] for values in valuations) for i in range(arity)]
    functions += [tuple(c for _ in valuations) for c in constants]
    functions = list(dict.fromkeys(functions))
    seen = set(functions)
    for left in functions:
        for right in list(functions):
            for table in tables:
                result = tuple(table[a][b] for a, b in zip(left, right))
                if result not in seen:
                    functions.append(result)
                    seen.add(result)
    return functions


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

    # Swap the choices and atoms to adjoin the opposite unit. The old first
    # unit b must be preserved by each of the three coordinates.
    swap = [1, 0, 2, 3]
    opposite_embedding = [tuple(swap[c] for c in embedding[swap[x]]) for x in carrier]
    opposite_embedding += [tuple(swap[c] for c in embedding[4 + swap[x]])
                           for x in carrier] + [(0, 0, 0)]
    assert opposite_embedding[1] == (1, 1, 1)
    opposite = unitize(d, 1)
    for source, target in zip(opposite, d):
        for x, y in product(range(9), repeat=2):
            assert opposite_embedding[source[x][y]] == tuple(
                target[a][b] for a, b in zip(opposite_embedding[x], opposite_embedding[y]))

    # Applying both constructions embeds the nineteen-element extension
    # into the ninth power with both endpoints named.
    double = unitize(extended, 1)
    double_embedding = []
    for x in range(19):
        coordinates = [8] * 3 if x == 18 else [c + (4 if x >= 9 else 0)
                                              for c in embedding[x % 9]]
        double_embedding.append(tuple(c for y in coordinates for c in opposite_embedding[y]))
    assert len(set(double_embedding)) == 19
    assert double_embedding[8] == (1,) * 9
    assert double_embedding[18] == (0,) * 9
    double_comparisons = 0
    for source, target in zip(double, d):
        for x, y in product(range(19), repeat=2):
            assert double_embedding[source[x][y]] == tuple(
                target[a][b] for a, b in zip(double_embedding[x], double_embedding[y]))
            double_comparisons += 9
    assert all(double[1][8][x] == x and double[2][8][x] == 8
               and double[1][18][x] == 18 and double[2][18][x] == x
               for x in range(19))

    # Independently enumerate every binary term function, with and without
    # constants. The explicit double unitization must give the whole free
    # pointed algebra, including its operations, not only its cardinality.
    free = function_closure(d, 2)
    assert len(free) == 11
    free_index = {column: i for i, column in enumerate(free)}
    free_tables = [[[free_index[tuple(table[a][b] for a, b in zip(left, right))]
                    for right in free] for left in free] for table in d]
    free_double = unitize(unitize(free_tables), 1)
    free_columns = free + [tuple(d[0][1][a] for a in column) for column in free]
    free_columns += [(1,) * 16]
    free_columns += [tuple(d[0][0][a] for a in column) for column in list(free_columns)]
    free_columns += [(0,) * 16]
    pointed_free = function_closure(d, 2, (0, 1))
    assert len(set(free_columns)) == len(pointed_free) == 47
    assert set(free_columns) == set(pointed_free)
    for source, target in zip(free_double, d):
        for x, y in product(range(47), repeat=2):
            assert free_columns[source[x][y]] == tuple(
                target[a][b] for a, b in zip(free_columns[x], free_columns[y]))
    assert len(function_closure(d, 1, (0, 1))) == 7

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

    double_equations = equations + [
        (owned(0, OPPOSITE_UNIT, x), OPPOSITE_UNIT),
        (owned(1, OPPOSITE_UNIT, x), x),
    ]
    middle = union(UNIT, OPPOSITE_UNIT)
    recovered_join = owned(0, owned(1, x, y), owned(1, middle, owned(0, x, y)))
    double_equations.append((union(x, y), recovered_join))
    double_translated = eliminate_units(double_equations)
    first_translation = eliminate_unit(double_equations, 1, OPPOSITE_UNIT)
    sequential_translation = eliminate_unit(first_translation)
    assert len(double_translated) <= sum(7 ** len(variables(a) | variables(b))
                                         for a, b in double_equations)
    for collection, tables, units in (
        (double_translated + sequential_translation, d, {}),
        (first_translation, d, {'unit': 1}),
        (double_equations, double, {'unit': 8, 'opposite_unit': 18}),
    ):
        for left, right in collection:
            used = sorted(variables(left) | variables(right))
            for values in product(range(len(tables[0])), repeat=len(used)):
                valuation = dict(zip(used, values))
                assert evaluate(left, valuation, tables, **units) == evaluate(
                    right, valuation, tables, **units)
    try:
        eliminate_units([(UNIT, OPPOSITE_UNIT)])
    except ValueError:
        pass
    else:
        raise AssertionError('identified the two adjoined units')

    # The reduction is valid for arbitrary base algebras, not only for models
    # of the core laws. Use noncommutative random tables to audit every case.
    rng = Random(40159)
    terms = [UNIT, x, y, z] + [side for pair in equations for side in pair]
    reductions = 0
    double_reductions = 0
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
        twice = unitize(lifted, 1)
        offsets = [0, size, 2 * size, 2 * size + 1, 3 * size + 1,
                   4 * size + 1, 4 * size + 2]
        tags = [tag for tag in range(7)
                for _ in range(1 if tag in (2, 5, 6) else size)]
        double_terms = [OPPOSITE_UNIT] + terms
        double_terms += [side for pair in double_equations[-3:] for side in pair]
        for term in double_terms:
            used = sorted(variables(term))
            for values in product(range(4 * size + 3), repeat=len(used)):
                valuation = dict(zip(used, values))
                forms = {i: tags[value] for i, value in valuation.items()}
                payloads = {i: value - offsets[forms[i]] for i, value in valuation.items()}
                tag, payload = double_tagged_term(term, forms)
                expected = offsets[tag]
                if tag not in (2, 5, 6):
                    expected += evaluate(payload, payloads, arbitrary)
                assert evaluate(term, valuation, twice, 2 * size, 4 * size + 2) == expected
                double_reductions += 1
    print(f'Two-owner unitization: nine-element pointed embedding, {comparisons} '
          'coordinate checks; the 33-element product unitization embeds '
          f'naturally; {len(equations)} sample pointed identities give '
          f'{len(translated)} valid constant-free identities, and {reductions} '
          'tag reductions pass on arbitrary noncommutative tables. '
          f'The nineteen-element double unitization passes {double_comparisons} '
          f'coordinate checks; {len(double_equations)} sample identities with '
          f'both endpoints give {len(double_translated)} constant-free identities '
          f'and {double_reductions} arbitrary-table double tag reductions. '
          'Both endpoints survive, union is recovered from the choices and their '
          'join, and incompatible tags are rejected. Complete term-function '
          'closure gives free pointed algebras of sizes 7 and 47 in arities '
          'one and two; the latter is the double unitization of the '
          '11-element unpointed free algebra, with all operations checked. '
          'No complete basis is asserted.')


if __name__ == '__main__':
    check()
