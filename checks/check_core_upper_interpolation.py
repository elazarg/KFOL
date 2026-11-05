"""Finite certificate for arbitrary-arity upper interpolation in C_3.

The written proof reduces all arities and term sizes to this exact finite
statement: every subset of a two-observer product generates its subalgebra
using only translations by the original generators and joins. There are
two product types, according as the omitted owners coincide. All nonempty
subsets are inspected; no bound on term size or generator count is assumed.
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


def word_join_closure(generators, operations, product_masks):
    """Only original-generator translations and joins of previous values."""
    result = generators
    coefficients = tuple(elements(generators))
    queue = list(coefficients)
    for x in queue:
        outputs = 0
        for y in coefficients:
            outputs |= product_masks[x][y]
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
        linear = word_join_closure(generators, operations, product_masks)
        assert generators & ~linear == 0
        # Closure under the full operations proves equality with the full
        # generated subalgebra: every construction step was already a term.
        if linear != (1 << 16) - 1:
            values = tuple(elements(linear))
            assert all(product_masks[x][y] & ~linear == 0
                       for x, y in product(values, repeat=2)), (
                           first_omitted, second_omitted, generators, linear)
            proper_closures += 1
        closures.add(linear)
    return len(closures), proper_closures


def check():
    same = audit(2, 2)
    different = audit(2, 0)
    assert same[0] == 941 and different[0] == 740
    print('Upper interpolation certificate: every nonempty subset of both '
          '16-element observer products inspected (131070 subsets); '
          f'{same[0]} and {different[0]} distinct generated subalgebras, '
          f'{same[1]} and {different[1]} subsets with proper closures. '
          'Original-generator translations and joins always generate '
          'the full subalgebra. The written interpolation argument applies '
          'to arbitrary arity and term size in the three-owner core.')


if __name__ == '__main__':
    check()
