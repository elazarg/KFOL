"""Finite certificate for two-point quadratic interpolation in C_3.

The written proof reduces all arities and term sizes to this exact finite
statement: every subset of a two-observer product generates its subalgebra
using only joins of original generators and their basic binary products.
There are two product types, according as the omitted owners coincide.
All nonempty subsets are inspected; no bound on term size or generator
count is assumed. A separate audit checks the four-element obstruction
to extending the quadratic meet formula to the core variety.
"""

from itertools import product


def observer(omitted):
    atoms = [i for i in range(3) if i != omitted]
    values = atoms + [3, 4]
    indices = {x: i for i, x in enumerate(values)}

    def join(x, y):
        return x if x == y else max(3, x, y)

    add = [[indices[join(x, y)] for y in values] for x in values]
    choices = [[[indices[i if i in (x, y) else join(x, y)]
                 for y in values] for x in values] for i in range(3)]
    return [add] + choices


def product_tables(first, second):
    return [[[4 * f[x // 4][y // 4] + g[x % 4][y % 4]
              for y in range(16)] for x in range(16)]
            for f, g in zip(first, second)]


def elements(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def quadratic_join_closure(generators, operations, product_masks):
    """One basic product of original generators per summand, then joins."""
    result = generators
    coefficients = tuple(elements(generators))
    for x, y in product(coefficients, repeat=2):
        result |= product_masks[x][y]
    queue = list(elements(result))
    for x in queue:
        outputs = 0
        for y in queue:
            outputs |= 1 << operations[0][x][y]
        extra = outputs & ~result
        result |= extra
        queue.extend(elements(extra))
    return result


def audit(first_omitted, second_omitted):
    operations = product_tables(observer(first_omitted),
                                observer(second_omitted))
    product_masks = [[sum(1 << z for z in {f[x][y] for f in operations})
                      for y in range(16)] for x in range(16)]
    closures = set()
    proper_closures = 0
    for generators in range(1, 1 << 16):
        quadratic = quadratic_join_closure(generators, operations, product_masks)
        assert generators & ~quadratic == 0
        # Closure under the full operations proves equality with the full
        # generated subalgebra: every construction step was already a term.
        if quadratic != (1 << 16) - 1:
            values = tuple(elements(quadratic))
            assert all(product_masks[x][y] & ~quadratic == 0
                       for x, y in product(values, repeat=2)), (
                           first_omitted, second_omitted, generators, quadratic)
            proper_closures += 1
        closures.add(quadratic)
    return len(closures), proper_closures


def check_quotient_obstruction():
    """Audit the written two-evaluation obstruction for all quadratic joins."""
    from core_ladders import ladder_join, ladder_own

    values = (0, 1, 3, 4)  # a_0, a_1, c_1, c_2 in L_2
    indices = {v: i for i, v in enumerate(values)}
    add = [[indices[ladder_join(2, x, y)] for y in values] for x in values]
    choices = [[[indices[ladder_own(2, r, x, y)] for y in values]
                for x in values] for r in range(3)]
    actual = [indices[v] for v in (1, 0, 4)]
    native = observer(2)  # local indices: a_0, a_1, n, p
    rows = tuple(product(range(4), repeat=3))
    profiles = [tuple(row[i] for row in rows) for i in range(3)]
    outputs = list(actual)
    for owner in (0, 1):
        for i in range(3):
            for j in range(i + 1, 3):
                profiles.append(tuple(native[owner + 1][row[i]][row[j]]
                                      for row in rows))
                outputs.append(choices[owner][actual[i]][actual[j]])
    target = tuple(native[1][row[1]][native[2][row[0]][row[2]]]
                   for row in rows)
    q = choices[0][actual[1]][choices[1][actual[0]][actual[2]]]
    w = indices[3]
    assert values[q] == 0 and q != w and add[q][w] == w
    witnesses = [rows.index(row) for row in ((2, 2, 3), (1, 3, 2))]
    assert all(target[row] == 3 for row in witnesses)
    valid = 0
    witness_compatible = 0
    upper_values = set()
    for mask in range(1, 1 << len(profiles)):
        summands = tuple(elements(mask))
        profile = list(profiles[summands[0]])
        value = outputs[summands[0]]
        for i in summands[1:]:
            profile = [native[0][a][b]
                       for a, b in zip(profile, profiles[i])]
            value = add[value][outputs[i]]
        if all(profile[row] == 3 for row in witnesses):
            witness_compatible += 1
            assert add[w][value] == value
        if all(native[0][a][b] == b for a, b in zip(target, profile)):
            valid += 1
            upper_values.add(value)
            assert add[w][value] == value
    assert valid == 312
    assert {values[v] for v in upper_values} == {3, 4}
    assert all(add[z][w] == w for z in range(len(values))
               if all(add[z][u] == u for u in upper_values))
    print(f'Quadratic quotient obstruction: 511 nonempty joins audited; '
          f'{valid} valid upper bounds on all 64 native assignments; '
          f'the two written assignments alone force {witness_compatible} '
          'joins above c_1 in the four-element subalgebra of L_2, whereas '
          'the target is a_0. The full family of valid quadratic upper '
          'bounds has meet c_1.')


def check():
    same = audit(2, 2)
    different = audit(2, 0)
    assert same[0] == 941 and different[0] == 740
    print('Quadratic interpolation certificate: every nonempty subset of both '
          '16-element observer products inspected (131070 subsets); '
          f'{same[0]} and {different[0]} distinct generated subalgebras, '
          f'{same[1]} and {different[1]} subsets with proper closures. '
          'Joins of original generators and their basic binary products '
          'always give the full subalgebra. The interpolation consequence '
          'applies to arbitrary arity and term size in the three-owner core.')


if __name__ == '__main__':
    check()
    check_quotient_obstruction()
