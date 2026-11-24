"""Check the reductions on small formulas without enumerating their large output tables."""
from itertools import product
from random import Random

from addressed_rectangles import truth
from qbf_tables import three_cnf, separate_slots, make_rectangles, compile_qbf


def matrix(clauses, values):
    return all(any(values[abs(lit)-1] == (lit > 0) for lit in clause) for clause in clauses)


def extends(clauses, old, extra):
    return any(matrix(clauses, old + tail) for tail in product((False, True), repeat=extra))


def main():
    rng = Random(1124)
    splits = slots = rectangles = 0
    for length in range(8):
        for _ in range(25):
            clause = [rng.choice((-2, -1, 1, 2)) for _ in range(length)]
            prefix, short = three_cnf('AE', [clause])
            for old in product((False, True), repeat=2):
                assert matrix([clause], old) == extends(short, old, len(prefix)-2)
                splits += 1
    for prefix, clauses in [('AE', [(1,-2,1)]), ('E', [(1,), (-1,)]), ('', []), ('', [()])]:
        final, transformed = separate_slots(prefix, clauses)
        for old in product((False, True), repeat=len(prefix)):
            assert matrix(clauses, old) == extends(transformed, old, len(final)-len(prefix))
            slots += 1
    for n in range(3):
        for signs in product('EA', repeat=n):
            prefix = ''.join(signs)
            for sample in range(9):
                if n:
                    clauses = [[rng.choice((-1, 1))*rng.randint(1, n) for _ in range(rng.randint(0, 2))]
                               for _ in range(rng.randint(0, 2))]
                else:
                    clauses = [[]] if sample % 2 else []
                problem, _ = make_rectangles(prefix, clauses, max(1, n))
                yes = problem.witness(problem.full, problem.start) is not None
                assert yes == truth(prefix, clauses), (prefix, clauses)
                problem.witness.cache_clear()
                rectangles += 1
    for prefix, clauses in [('E', [[1]]), ('A', [[1]]), ('', []), ('', [[]])]:
        target = compile_qbf(prefix, clauses)
        for owners in (3, 4):
            for role in range(owners):
                assert target.values([1 << role] * (target.size+1))[-1] == 1 << role
    print(f'{splits} split extensions, {slots} slot extensions, {rectangles} native rectangle tests')


if __name__ == '__main__':
    main()
