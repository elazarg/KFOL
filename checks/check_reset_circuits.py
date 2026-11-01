"""Native reset DAG reduction, evaluated without unfolding shared gates."""
from itertools import product
from random import Random

from check_fragments import Valuations, cnfs, satisfiable


def reduction(formula, variables):
    # Negative node numbers are input references; nonnegative numbers are gates.
    def inp(i):
        return -i-1
    gates = []
    def reset(x, y):
        gates.append((x, y))
        return len(gates)-1
    def comb(xs, tail):
        for x in reversed(xs):
            tail = reset(x, tail)
        return tail
    rails = [inp(i) for i in range(2*variables)]
    z, c = inp(2*variables), inp(2*variables+1)
    baseline = comb(rails, z)
    bad = [reset(reset(c, rails[2*i]), rails[2*i+1]) for i in range(variables)]
    rhs = comb(bad, baseline)
    lhs = c
    for clause in formula:
        previous = lhs
        lhs = comb([reset(previous, rails[2*i + int(not sign)])
                    for i, sign in clause], z)
    lhs = reset(lhs, rhs)
    return gates, lhs, rhs


def evaluate(gates, inputs, operation):
    values = []
    def value(ref):
        return inputs[-ref-1] if ref < 0 else values[ref]
    for x, y in gates:
        values.append(operation(value(x), value(y)))
    return value


def check():
    rng = Random(1110)
    for roles, variables in ((3, 1), (3, 2), (4, 1)):
        tables = Valuations(roles, 2*variables+2)
        def parallel(x, y):
            many = tables.multiple(y)
            return tuple(b | (many & a) for a, b in zip(x, y))
        examples = cnfs(variables)
        for formula in examples:
            gates, lhs, rhs = reduction(formula, variables)
            assert len(gates) == 5*variables + 2*sum(map(len, formula)) + 1
            result = evaluate(gates, tables.rows, parallel)
            assert (result(lhs) == result(rhs)) == (not satisfiable(formula, variables))
            # Scalar and fixed-chain evaluations are independent of bit tables.
            chain_valid = True
            for inputs in product((1, 3, 7), repeat=2*variables+2):
                scalar = evaluate(gates, inputs, lambda a, b: b if b.bit_count() == 1 else a | b)
                chain_valid &= scalar(lhs) == scalar(rhs)
            assert chain_valid == (not satisfiable(formula, variables))
            for _ in range(3):
                index = rng.randrange(tables.count)
                scalar = evaluate(gates, tables.decode(index), lambda a, b: b if b.bit_count() == 1 else a | b)
                for ref in (lhs, rhs):
                    assert scalar(ref) == sum(((row >> index) & 1) << r for r, row in enumerate(result(ref)))
        print(f'Reset circuits: K={roles}, {len(examples)} CNFs on {variables} variables; '
              f'all {tables.count} mixed valuations and all fixed-chain valuations passed.', flush=True)


if __name__ == '__main__':
    check()
