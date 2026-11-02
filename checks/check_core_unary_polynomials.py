"""Independent native checks of the arbitrary-K unary polynomial theorem.

Exhaustive polynomial closure at K=3 is compared with every normal form.
Every proposed profile at K=4 is synthesized as a native core polynomial.
The proof for arbitrary parameters and arbitrary K is written in the TR.
"""

from core_unary_polynomials import profiles, synthesize, value
from fragments import denote


def own(owner, left, right):
    atom = 1 << owner
    return atom if atom in (left, right) else left | right


def polynomial_closure(owners):
    carrier = tuple(range(1, 1 << owners))
    tables = [carrier] + [(c,) * len(carrier) for c in carrier]
    seen = set(tables)
    previous = 0
    while previous < len(tables):
        current = len(tables)
        for a in range(current):
            for b in range(max(a, previous), current):
                for owner in range(owners):
                    table = tuple(own(owner, x, y) for x, y in zip(tables[a], tables[b]))
                    if table not in seen:
                        seen.add(table)
                        tables.append(table)
        previous = current
    return seen


def check():
    totals = []
    for owners in (3, 4):
        carrier = tuple(range(1, 1 << owners))
        parameters = tuple(1 << i for i in range(owners))
        normal = set()
        count = 0
        for profile in profiles(owners):
            expected = tuple(value(profile, x) for x in carrier)
            term = synthesize(profile)
            assert tuple(denote(term, (x,) + parameters) for x in carrier) == expected
            assert expected not in normal
            normal.add(expected)
            count += 1
        assert count == (1 + 2**(owners - 1))**owners
        normal.update((c,) * len(carrier) for c in carrier)
        assert len(normal) == count + 2**owners - 2
        for table in normal:
            assert all(table[table[table[x] - 1] - 1] == table[table[x] - 1]
                       for x in range(len(carrier)))
        if owners == 3:
            assert polynomial_closure(owners) == normal
        totals.append(len(normal))

    # The exponent two cannot be replaced by one.
    p = lambda x: own(0, 3, own(1, 7, x))
    assert p(2) == 3 and p(p(2)) == 7 and p(p(p(2))) == 7
    print(f'Core unary polynomials: exact K=3 closure has {totals[0]} functions; '
          f'all {totals[1]} K=4 normal forms synthesized and distinct; '
          'p^3=p^2 and sharpness checked. Arbitrary-K proof written.')


if __name__ == '__main__':
    check()
