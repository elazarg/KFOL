"""Audit support and the exact word/join form of finite absorber extensions."""

from functools import reduce
from itertools import combinations_with_replacement
import json

from check_core_owned_reset import test_models
from check_core_upper_bound_extension import close


def check():
    models = extensions = supports = 0
    singleton_extensions = unit_cases = nonunit_cases = observer_pairs = 0
    semilattice_cases = mixed_pairs = factor_entries = 0
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
            assert all(any(join[s][u] == u for s in seed) for u in generated)
            profiles = []
            for u in sorted(generated):
                profiles.append(tuple(reduce(lambda v, h: h[u][v], choices, join[s][u])
                                      for s in seed))
            assert len(set(profiles)) == len(generated)
            observer_pairs += len(generated) * (len(generated) - 1) // 2
            for i, table in enumerate(choices):
                for u in generated:
                    assert (u == absorbers[i] or u in extensive[i]
                            or any(join[c][u] == u and table[c][u] == u
                                   for c in coefficients))
                    supports += 1
            for i, a in enumerate(absorbers):
                single = close(list(coefficients) + [a], operations)
                words = close(list(coefficients) + [a], operations, coefficients)
                assert single == words
                singleton_extensions += 1
                other_active = [j for j, h in enumerate(choices) if j != i and h != join]
                if len(other_active) > 1:
                    continue
                j = other_active[0] if other_active else next(j for j in range(len(choices)) if j != i)
                f, g = choices[i], choices[j]
                assert all(h == join for k, h in enumerate(choices) if k not in (i, j))
                units = {u for u in single
                         if all(f[z][g[z][u]] == z for z in single)}
                old_units = units & coefficients
                expected = old_units
                if a in units:
                    expected = old_units | {a} | {join[a][c] for c in old_units}
                else:
                    nonunit_cases += 1
                assert units == expected
                unit_cases += 1
                if not all(h[c][d] == join[c][d] for h in (f, g)
                           for c in coefficients for d in coefficients):
                    continue
                image = {z: g[a][z] for z in single}
                end = {image[c] for c in coefficients}
                supported = set(coefficients) | end
                ideal = set(image.values())
                assert supported == set(close(list(supported), operations))
                assert all(h[x][y] == join[x][y] for h in (f, g)
                           for x in supported for y in supported)
                assert set(single) == supported | {a} | {join[a][e] for e in end}
                assert ideal == end | {a} | {join[a][e] for e in end}
                assert all(image[z] == z for z in ideal)
                for c in coefficients:
                    for d in coefficients:
                        assert (f[c][image[d]] == g[c][image[d]]
                                == join[c][image[d]] == image[join[c][d]])
                        mixed_pairs += 1
                # The absorbing image gives a Rees quotient. Check its
                # congruence, all-join operations, and joint separation
                # with the image endomorphism directly on the tables.
                quotient = {x: -1 if x in ideal else x for x in single}
                representative = {quotient[x]: x for x in single}
                assert len({(image[x], quotient[x]) for x in single}) == len(single)
                for h in operations:
                    assert all(h[x][y] in ideal for x in ideal for y in single)
                    for x in single:
                        for y in single:
                            assert image[h[x][y]] == h[image[x]][image[y]]
                            assert quotient[h[x][y]] == quotient[join[x][y]]
                            assert quotient[h[x][y]] == quotient[h[
                                representative[quotient[x]]][representative[quotient[y]]]]
                            factor_entries += 1
                semilattice_cases += 1
    print(json.dumps({'status': 'all assertions passed', 'models': models,
                      'extensions': extensions, 'support_cases': supports,
                      'singleton_absorber_extensions': singleton_extensions,
                      'separated_pairs': observer_pairs,
                      'two_owner_unit_cases': unit_cases,
                      'nonunit_absorber_cases': nonunit_cases,
                      'semilattice_coefficient_extensions': semilattice_cases,
                      'mixed_coefficient_pairs': mixed_pairs,
                      'subdirect_factor_entries': factor_entries}, indent=2))


if __name__ == '__main__':
    check()
