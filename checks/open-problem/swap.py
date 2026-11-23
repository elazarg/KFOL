"""Check the three-input swap obstruction directly in the winner-set algebra.

A signature records a term's outputs on the two singleton-profile tests and
the remaining marked row. Coordinatewise closure enumerates exactly the
signatures of core terms, independently of the offer-game recursion.
"""

from itertools import product

A, B, C = 1, 2, 4


def choose(owner, left, right):
    return owner if owner in (left, right) else left | right


def signature_closure(rows):
    signatures = set(zip(*rows))
    while True:
        generated = {
            tuple(choose(owner, x, y) for x, y in zip(left, right))
            for owner, left, right in product((A, B, C), signatures, signatures)
        }
        if generated <= signatures:
            return signatures
        signatures.update(generated)


def check():
    for name, b_row in [('parent', (B, C, B)), ('after swap', (C, B, B))]:
        rows = (b_row, (B, B, C), (B, C, A))
        signatures = signature_closure(rows)
        outputs = sorted(z for b, c, z in signatures if (b, c) == (B, C))
        assert any(not (z & A) for z in outputs) == (name == 'after swap')
        print(name, len(signatures), 'signatures, possible marked-row outputs', outputs)


if __name__ == '__main__':
    check()
