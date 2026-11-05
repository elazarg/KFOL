"""Audit the top-input word theorem and its exact branch linearizations.

The arbitrary-algebra argument is in the core-basis appendix.
This audit checks the stored finite models; it does not infer a basis
or local finiteness of arbitrary one-generator extensions from finite counts.
"""
import itertools
import time

from check_core_owned_reset import test_models


def close(seed, operations, coefficients=None):
    values = list(dict.fromkeys(seed))
    seen = set(values)
    for position, x in enumerate(values):
        for y in values[:position + 1]:
            z = operations[0][x][y]
            if z not in seen:
                seen.add(z)
                values.append(z)
        for h in operations[1:]:
            partners = values[:position + 1] if coefficients is None else coefficients
            for y in partners:
                z = h[x][y]
                if z not in seen:
                    seen.add(z)
                    values.append(z)
    return seen


def check():
    started = time.monotonic()
    cases = invariant_checks = linearizations = 0
    case_types = [0, 0, 0]  # two supports, one extensive, two extensive
    model_count = 0
    largest_extension = largest_coefficient_algebra = 0
    for model_index, (join, choices) in enumerate(test_models()):
        size = len(join)
        if size > 25:
            continue
        model_count += 1
        operations = [join] + choices
        seen_cases = set()
        for top in range(size):
            ideal = [a for a in range(size) if join[a][top] == top]
            extensive = [
                {u for u in ideal if all(join[z][h[u][z]] == h[u][z] for z in ideal)}
                for h in choices
            ]
            support = [
                {u: {c for c in ideal if join[c][u] == u and h[c][u] == u}
                 for u in ideal}
                for h in choices
            ]
            proper_ideal = [a for a in ideal if a != top]
            for arity in range(1, min(3, len(proper_ideal)) + 1):
                for generators in itertools.combinations(proper_ideal, arity):
                    coefficients = close(generators, operations)
                    if top in coefficients:
                        continue
                    key = top, tuple(sorted(coefficients))
                    if key in seen_cases:
                        continue
                    seen_cases.add(key)
                    cases += 1
                    full = close(list(coefficients) + [top], operations)
                    words_and_joins = close(list(coefficients) + [top], operations,
                                            sorted(coefficients))
                    assert full == words_and_joins, (
                        'word normal form', model_index, top, generators,
                        sorted(full - words_and_joins))
                    assert all(join[u][top] == top for u in full)
                    largest_extension = max(largest_extension, len(full))
                    largest_coefficient_algebra = max(largest_coefficient_algebra,
                                                     len(coefficients))
                    for owner, h in enumerate(choices):
                        witness = {}
                        for u in full:
                            invariant_checks += 1
                            if u in extensive[owner]:
                                witness[u] = None
                            else:
                                possible = support[owner][u] & coefficients
                                assert possible, ('support invariant', model_index,
                                                  top, generators, owner, u)
                                witness[u] = min(possible)
                        for u, v in itertools.product(full, repeat=2):
                            c, d = witness[u], witness[v]
                            if c is None and d is None:
                                rhs = join[u][v]
                                case_types[2] += 1
                            elif c is None:
                                rhs = join[v][h[d][u]]
                                case_types[1] += 1
                            elif d is None:
                                rhs = join[u][h[c][v]]
                                case_types[1] += 1
                            else:
                                rhs = join[h[c][v]][h[d][u]]
                                case_types[0] += 1
                            assert h[u][v] == rhs, (
                                'branch linearization', model_index, top,
                                generators, owner, u, v, c, d, h[u][v], rhs)
                            linearizations += 1
    print(f'Top-input word normal form: {cases} upper-bound extensions in '
          f'{model_count} stored/native models; {invariant_checks} support/'
          f'extensivity checks and {linearizations} exact branch '
          f'linearizations ({case_types[0]} two-support, {case_types[1]} '
          f'one-extensive, {case_types[2]} two-extensive). Word coefficients '
          f'were restricted to C, excluding the adjoined top. Largest C: '
          f'{largest_coefficient_algebra}; largest extension: '
          f'{largest_extension}. Runtime: {time.monotonic() - started:.2f}s.')


if __name__ == '__main__':
    check()
