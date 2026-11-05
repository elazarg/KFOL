"""Audit unrestricted two-choice translation words and input-reset erasure.

Close states consisting of a transformation and the join of its word's
coefficients. This tracks every possible parameter bound, including those
lost by merging equal transformations. Check the symbolic normalizer on
every transition and verify stabilization for every transformation.
"""

from collections import Counter
from itertools import permutations

from check_core_alternating_translations import compose
from check_core_owned_reset import test_models
from core_two_choice_words import normalize
from core_two_owner_unitization import unitize


def audit_global_input_reset(add, operations):
    n = len(add)
    counts = Counter()
    for a in range(n):
        reset = []
        for z in range(n):
            value = add[a][z]
            for h in operations:
                value = h[z][value]
            reset.append(value)
        R = tuple(reset)
        for h in (*operations, add):
            L = tuple(h[a])
            assert compose(L, R) == compose(R, L) == L
            counts['global_basic_erasures'] += n
            for k in (*operations, add):
                for b in range(n):
                    Q = tuple(k[b])
                    LQ = compose(L, Q)
                    assert compose(LQ, R) == LQ
                    counts['global_context_erasures'] += n
    return counts


def audit_with_join(add, f, g):
    n = len(add)
    identity = tuple(range(n))
    generators = {tuple(row) for table in (add, f, g) for row in table}
    maps = [identity]
    seen = {identity}
    for P in maps:
        square = compose(P, P)
        assert compose(square, P) == square
        for L in generators:
            Q = compose(P, L)
            if Q not in seen:
                seen.add(Q)
                maps.append(Q)

    lifted = unitize(unitize((add, f, g)), unit_owner=1)
    plus, first, second = lifted
    e, d = 2 * n, 4 * n + 2
    for a in range(len(plus)):
        alpha, beta = plus[e][a], plus[d][a]
        for z in range(len(plus)):
            assert first[alpha][second[beta][z]] == plus[a][z]
            assert second[beta][first[alpha][z]] == plus[a][z]
    return Counter(join_monoids=1, join_monoid_elements=len(maps),
                   join_factorizations=len(plus) ** 2), len(maps)


def audit(add, f, g):
    n = len(add)
    identity = tuple(range(n))
    generators = [(h, a, tuple(op[a]))
                  for h, op in enumerate((f, g)) for a in range(n)]
    reset = [tuple(f[z][g[z][a]] for z in range(n)) for a in range(n)]
    tables = {(h, a): L for h, a, L in generators}

    def evaluate(word):
        value = identity
        for letter in word:
            value = compose(value, tables[letter])
        return value

    representatives = {(identity, None): ()}
    states = [(identity, None)]
    maps = {identity}
    counts = Counter(monoids=1)
    for P, t in states:
        word = representatives[P, t]
        if t is not None:
            assert compose(P, reset[t]) == P
            observed = compose(reset[t], P)
            assert compose(observed, observed) == observed
            assert compose(P, observed) == compose(P, P)
            counts['input_resets'] += 1
        for h, a, L in generators:
            Q = compose(P, L)
            bound = a if t is None else add[t][a]
            extended = word + ((h, a),)
            normal = normalize(extended)
            assert evaluate(normal) == Q
            assert normalize(normal) == normal
            assert set(normal) == set(extended)
            m = len(set(extended))
            assert len(normal) <= m * (m + 1) // 2
            counts['normal_form_transitions'] += 1
            if (Q, bound) not in representatives:
                representatives[Q, bound] = normal
                states.append((Q, bound))
                maps.add(Q)
    for P in maps:
        square = compose(P, P)
        assert compose(square, P) == square
        counts['power_checks'] += 1
        for h, a, L in generators:
            # Kernel compatibility extends L R_a = L through every
            # intervening linear context in the complete monoid.
            LP = compose(L, P)
            assert compose(LP, reset[a]) == LP
            counts['context_erasures'] += 1
    counts['states'] = len(states)
    counts['monoid_elements'] = len(maps)
    return counts, len(maps)


def check():
    counts = Counter()
    largest = largest_join = 0
    models = test_models()
    for add, operations in models:
        counts.update(audit_global_input_reset(add, operations))
        for f, g in permutations(operations, 2):
            result, size = audit(add, f, g)
            counts.update(result)
            largest = max(largest, size)
            result, size = audit_with_join(add, f, g)
            counts.update(result)
            largest_join = max(largest_join, size)
    assert normalize(()) == ()
    assert normalize('ababcabac') == tuple('abacab')
    print(f'Unrestricted two-choice words: {len(models)} models; '
          + ', '.join(f'{value} {key}' for key, value in sorted(counts.items()))
          + f'; largest choice monoid {largest}, '
          f'largest monoid with join {largest_join}. '
          'All transformation/bound states were closed completely. '
          'The uniform word bound and stabilization have written proofs; '
          'finite basability of the full core is not asserted.')


if __name__ == '__main__':
    check()
