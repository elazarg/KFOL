"""Audit the absorber-pointed generator and the complete unary normal forms.

Quotient maps are checked at K=3,4,5. At K=3,4 all column forms are
evaluated and separated; an independent full closure is computed at K=3.
The six-state model that fails mixed absorption is separately checked as
a homomorphic image of the native unary algebra, so the audit does not
silently assume the strengthened candidate.
"""

from functools import reduce
from itertools import product
import json

from core_basis import MIXED_JOIN, MIXED_OPERATIONS
from check_core_mixed import check_mixed_countermodel


def generator(k):
    size = k + (1 << k)

    def join(x, y):
        if x == y:
            return x
        a = 1 << x if x < k else x - k
        b = 1 << y if y < k else y - k
        return k + (a | b)

    add = tuple(tuple(join(x, y) for y in range(size)) for x in range(size))
    ops = [tuple(tuple(i if i in (x, y) else add[x][y]
                       for y in range(size)) for x in range(size))
           for i in range(k)]
    return add, ops


def apply(table, a, b):
    return tuple(table[x][y] for x, y in zip(a, b))


def normal_forms(add, ops, constants):
    """Yield the same syntactic forms for any pointed algebra."""
    k, size = len(ops), len(add)
    identity = tuple(range(size))
    atoms = [(a,) * size for a in constants]
    entries = {}
    for j, i in product(range(k), repeat=2):
        value = apply(add, identity, atoms[i])
        for h in range(k):
            if h != j:
                value = apply(ops[h], identity, value)
        entries[j, i] = value
    columns = []
    for i in range(k):
        rows = [j for j in range(k) if j != i]
        options = [identity, entries[i, i]]
        for mask in range(1, 1 << (k - 1)):
            options.append(reduce(lambda a, b: apply(add, a, b),
                                  (entries[j, i] for bit, j in enumerate(rows)
                                   if mask >> bit & 1), identity))
        columns.append(options)
    for selection in product(*columns):
        yield reduce(lambda a, b: apply(add, a, b), selection, identity)
    for mask in range(1, 1 << k):
        yield reduce(lambda a, b: apply(add, a, b),
                     (atoms[i] for i in range(k) if mask >> i & 1))


def closure(seed, tables):
    values = list(dict.fromkeys(seed))
    seen = set(values)
    previous = 0
    while previous < len(values):
        end = len(values)
        for a in range(end):
            for b in range(max(a, previous), end):
                for table in tables:
                    value = apply(table, values[a], values[b])
                    if value not in seen:
                        seen.add(value)
                        values.append(value)
        previous = end
    return seen


def quotient_audit(k, add, ops):
    size = len(add)
    maps, entries = [], 0
    for support in range((1 << k) - 1):
        def q(x):
            if x < k:
                return x if support >> x & 1 else k + 1
            return k if (x - k) & ~support == 0 else k + 1

        image = tuple(q(x) for x in range(size))
        assert set(image) == {k, k + 1} | {
            i for i in range(k) if support >> i & 1}
        maps.append(image)
        for x, y in product(range(size), repeat=2):
            a, b = image[x], image[y]
            joined = a if a == b else k + 1 if k + 1 in (a, b) else k
            assert image[add[x][y]] == joined
            entries += 1
            for i, table in enumerate(ops):
                expected = i if support >> i & 1 and i in (a, b) else joined
                assert image[table[x][y]] == expected
                entries += 1
    assert len(set(zip(*maps))) == size
    assert len(closure([(i,) for i in range(k)], [add] + ops)) == (1 << k) - 1
    assert len(closure([(i,) for i in range(k + 1)], [add] + ops)) == size
    return entries


def check():
    report = []
    for k in (3, 4, 5):
        add, ops = generator(k)
        row = {'K': k, 'size': len(add),
               'quotient_operation_entries': quotient_audit(k, add, ops)}
        if k <= 4:
            forms = list(normal_forms(add, ops, range(k)))
            extensive_count = (1 + (1 << (k - 1))) ** k
            extensive = set(forms[:extensive_count])
            constants = set(forms[extensive_count:])
            assert len(extensive) == extensive_count
            assert len(constants) == (1 << k) - 1
            assert len(extensive & constants) == 1
            normal = extensive | constants
            assert len(normal) == extensive_count + (1 << k) - 2
            core = [x for x in range(len(add))
                    if x < k or (x - k).bit_count() >= 2]
            assert len({tuple(t[x] for x in core) for t in normal}) == len(normal)
            row['unary_functions'] = len(normal)
            row['core_restrictions_distinct'] = True
            if k == 3:
                seed = [tuple(range(len(add)))] + [(i,) * len(add) for i in range(k)]
                assert closure(seed, [add] + ops) == normal
                native_forms, native_tables = forms, [add] + ops
        report.append(row)

    check_mixed_countermodel()
    add, ops = MIXED_JOIN, MIXED_OPERATIONS
    absorbers = [reduce(lambda a, b: table[a][b], range(len(add))) for table in ops]
    assert all(all(table[a][x] == a for x in range(len(add)))
               for table, a in zip(ops, absorbers))
    images = {}
    for native, value in zip(native_forms, normal_forms(add, ops, absorbers)):
        if native in images:
            assert images[native] == value
        images[native] = value
    entries = 0
    for a, b in product(images, repeat=2):
        for source, target in zip(native_tables, [add] + list(ops)):
            assert images[apply(source, a, b)] == apply(target, images[a], images[b])
            entries += 1
    assert set(images.values()) == closure(
        [tuple(range(len(add)))] + [(a,) * len(add) for a in absorbers],
        [add] + list(ops))
    print(json.dumps({'status': 'all assertions passed', 'generators': report,
                      'six_state_unary_homomorphism_entries': entries,
                      'six_state_unary_functions': len(set(images.values()))}, indent=2))


if __name__ == '__main__':
    check()
