"""Check reset-unit absorption and its unrestricted sandwich consequence.

The first part independently verifies a universal equational certificate;
it does not run the prover that discovered it. The second audits the
written reset-homomorphism argument on the stored and native models.
"""

import json
from copy import deepcopy
from itertools import permutations, product
from pathlib import Path

from check_core_choice_images import equation, verify_derivation
from check_core_owned_reset import test_models


ASSUMPTIONS = (
    'f(x,g(x,c))=x',
    'f(x,x)=x', 'f(x,y)=f(y,x)', 'f(x,f(y,z))=f(f(x,y),z)',
    'g(x,x)=x', 'g(x,y)=g(y,x)', 'g(x,g(y,z))=g(g(x,y),z)',
    'f(x,g(x,y))=g(x,f(x,y))',
    'f(x,g(y,f(y,z)))=f(x,g(y,f(x,f(y,z))))',
    'g(x,f(y,g(y,z)))=g(x,f(y,g(x,g(y,z))))',
    'f(x,g(f(x,y),f(x,z)))=g(f(x,y),f(x,z))',
    'g(x,f(g(x,y),g(x,z)))=f(g(x,y),g(x,z))',
    'f(x,g(y,f(x,g(y,z))))=f(x,g(y,f(x,z)))',
    'g(x,f(y,g(x,f(y,z))))=g(x,f(y,g(x,z)))',
)
GOAL = 'f(x,g(c,f(x,y)))=f(x,g(c,y))'


def verify(certificate):
    proved, counts = verify_derivation(certificate, ASSUMPTIONS)
    assert proved[certificate['goal']] == equation(GOAL)
    return counts


def must_reject(certificate):
    try:
        verify(certificate)
    except AssertionError:
        return
    raise AssertionError('altered certificate accepted')


def audit(add, operations):
    triples = 0
    carrier = range(len(add))
    for f, g in permutations(operations, 2):
        for x, y, z in product(carrier, repeat=3):
            reset = lambda a: f[a][g[a][y]]
            v = f[x][g[y][z]]
            w = f[x][g[y][f[x][z]]]
            r, rz = reset(x), reset(z)
            assert add[x][r] == r and reset(r) == r
            assert f[x][g[y][w]] == w
            assert f[w][g[y][w]] == w == reset(w)
            assert reset(v) == f[r][g[y][rz]]
            assert reset(w) == f[r][g[y][f[r][rz]]]
            # The conditional equational lemma applies in the reset image.
            assert f[r][g[y][f[r][rz]]] == f[r][g[y][rz]]
            assert reset(g[y][z]) == g[y][z] == g[y][rz]
            assert w == reset(v) == f[r][g[y][z]]
            assert add[v][w] == w
            assert f[r][g[y][f[r][g[y][z]]]] == f[r][g[y][z]]
            triples += 1
    return triples


def check():
    path = Path(__file__).with_name('data') / 'core-reset-unit-absorption-proof.json'
    certificate = json.loads(path.read_text())
    counts = verify(certificate)
    altered = deepcopy(certificate)
    altered['steps'][0][1] = 'f(x,g(x,c))=c'
    must_reject(altered)
    altered = deepcopy(certificate)
    altered['steps'][-1][1] = 'f(x,g(c,f(x,y)))=x'
    must_reject(altered)
    altered = deepcopy(certificate)
    altered['goal'] = 3
    must_reject(altered)

    models = test_models()
    triples = sum(audit(add, operations) for add, operations in models)
    print(f'Reset-unit absorption: {sum(counts.values())} independently checked '
          f'equational steps ({dict(counts)}); altered unit, inference and goal '
          f'rejected. Sandwich reset: {triples} triples in {len(models)} models, '
          'including reset-image absorption, the parameter update, order '
          'inequality and idempotence. The universal certificate and written '
          'argument do not assert completeness of the core candidate.')


if __name__ == '__main__':
    check()
