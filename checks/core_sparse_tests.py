"""An exact all-arity test domain for an observer quotient of the core.

Atoms are 0..K-1 except the omitted owner; n=K and p=K+1. Assignments
containing exactly one p suffice. Only the output's p bit is needed;
the arbitrary-term reconstruction proof is in appendix-core-basis.tex.
"""

from itertools import product


def observer_tests(owners, arity, omitted):
    assert owners >= 3 and arity >= 1 and 0 <= omitted < owners
    atoms = tuple(i for i in range(owners) if i != omitted)
    for source in range(arity):
        for rest in product(atoms + (owners,), repeat=arity - 1):
            yield rest[:source] + (owners + 1,) + rest[source:]
