"""Audit the complete binary table and interval erasure in candidate models.

All stored models of size at most 25 are used, including native generators
with up to six owners. The original six-state candidate is included even
though it fails mixed absorption; neither new binary result requires it.
"""

from itertools import product
import json

from core_basis import (BinaryProfile, MIXED_JOIN, MIXED_OPERATIONS,
                        binary_product, binary_profiles)
from check_core_owned_reset import test_models


def check():
    cache = {}
    models = valuations = entries = intervals = 0
    for join, choices in test_models() + [(MIXED_JOIN, MIXED_OPERATIONS)]:
        n, k = len(join), len(choices)
        if n > 25:
            continue
        models += 1
        if k not in cache:
            profiles = binary_profiles(k)
            index = {p: i for i, p in enumerate(profiles)}
            assert len(profiles) == 2 ** (k + 1) + k + 1
            products = []
            for a, p in enumerate(profiles):
                for b, q in enumerate(profiles):
                    joined = BinaryProfile(p.support | q.support,
                                           p.left & q.left, p.right & q.right)
                    products.append((0, a, b, index[joined]))
                    for i in range(k):
                        products.append((i + 1, a, b, index[binary_product(i, p, q)]))
            cache[k] = profiles, products
        profiles, products = cache[k]
        operations = [join] + list(choices)
        for x, y in product(range(n), repeat=2):
            upper = join[x][y]
            values = []
            for p in profiles:
                if p.support == 1:
                    value = x
                elif p.support == 2:
                    value = y
                elif p.left and p.right:
                    value = choices[p.left.bit_length() - 1][x][y]
                else:
                    source, mask = (x, p.left) if p.left else (y, p.right)
                    value = upper
                    for i in range(k):
                        if mask >> i & 1:
                            value = choices[i][source][value]
                values.append(value)
            for op, a, b, target in products:
                assert operations[op][values[a]][values[b]] == values[target]
            entries += len(products)
            valuations += 1
            for z in range(n):
                if join[x][z] != z or join[z][upper] != upper:
                    continue
                for i, j in product(range(k), repeat=2):
                    if i != j:
                        f, g = choices[i], choices[j]
                        assert f[y][g[x][z]] == f[y][z]
                        intervals += 1
    print(json.dumps({'status': 'all assertions passed', 'models': models,
                      'binary_valuations': valuations,
                      'operation_entries': entries,
                      'interval_erasure_cases': intervals}, indent=2))


if __name__ == '__main__':
    check()
