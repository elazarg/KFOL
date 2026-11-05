"""Audit support and the exact word/join form of finite absorber extensions."""

from functools import reduce
from itertools import combinations_with_replacement
import json

from check_core_owned_reset import test_models
from check_core_upper_bound_extension import close


def check():
    models = extensions = supports = 0
    for join, choices in test_models():
        n = len(join)
        if n > 25:
            continue
        models += 1
        operations = [join] + choices
        absorbers = [reduce(lambda a, b: table[a][b], range(n)) for table in choices]
        assert all(all(table[a][x] == a for x in range(n))
                   for table, a in zip(choices, absorbers))
        extensive = [{a for a in range(n)
                      if all(join[x][table[a][x]] == table[a][x] for x in range(n))}
                     for table in choices]
        seen = set()
        for x, y in combinations_with_replacement(range(n), 2):
            coefficients = frozenset(close([x, y], operations))
            if coefficients in seen:
                continue
            seen.add(coefficients)
            extensions += 1
            seed = list(coefficients) + absorbers
            generated = close(seed, operations)
            word_joins = close(seed, operations, coefficients)
            assert generated == word_joins
            for i, table in enumerate(choices):
                for u in generated:
                    assert (u == absorbers[i] or u in extensive[i]
                            or any(join[c][u] == u and table[c][u] == u
                                   for c in coefficients))
                    supports += 1
    print(json.dumps({'status': 'all assertions passed', 'models': models,
                      'extensions': extensions, 'support_cases': supports}, indent=2))


if __name__ == '__main__':
    check()
