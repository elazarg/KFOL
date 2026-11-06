#!/usr/bin/env python3
"""Bounded checks for right-reset cut derivatives and atomic-tag paths.
Standard library only; no solver, data files, or repository imports.
Native D2,D3 and the nonflat five-state genuine-core join-diamond model.
"""
from itertools import permutations, product
from functools import lru_cache
import json


def native(k):
    n = k + 2
    join = [[x if x == y else max(k, x, y) for y in range(n)] for x in range(n)]
    choices = [[[i if i in (x, y) else join[x][y] for y in range(n)]
                for x in range(n)] for i in range(k)]
    return f"D{k}", join, choices, list(range(k + 1)) + [k]


def nonflat():
    join = [[0,1,2,3,4],[1,1,4,4,4],[2,4,2,4,4],[3,4,4,3,4],[4,4,4,4,4]]
    f = [[0,0,0,0,0],[0,1,2,3,4],[0,2,2,0,2],[0,3,0,3,3],[0,4,2,3,4]]
    return "nonflat_M3_core", join, [join, join, f], [0,3,1,2,3]


def audit_minimal_cuts(join, choices, rho):
    """Check the proved partial owner map; no extension claim is tested here."""
    n, k = len(join), len(choices)
    cuts = [tuple(int(join[x][b] != b) for x in range(n)) for b in range(n)]
    cuts.append((1,) * n)
    cases = entries = dichotomies = 0
    for p in range(n):
        for psi in cuts:
            if not psi[p] or any(
                    q != psi and q[p] and all(x <= y for x, y in zip(q, psi))
                    for q in cuts):
                continue
            zeros = [a for a in range(n) if not psi[a]]
            if not zeros:
                continue
            cases += 1
            types = {}
            for a in zeros:
                owners = []
                for i, h in enumerate(choices):
                    if psi[h[a][p]]:
                        assert all(psi[h[a][x]] == psi[x] for x in range(n))
                    else:
                        owners.append(i)
                    dichotomies += 1
                assert len(owners) <= 1
                types[a] = owners[0] if owners else k
            for a, b in product(zeros, repeat=2):
                native_join = types[a] if types[a] == types[b] else k
                assert types[join[a][b]] == native_join
                entries += 1
                for i, h in enumerate(choices):
                    value = i if i in (types[a], types[b]) else native_join
                    assert types[h[a][b]] == value
                    entries += 1
                if rho[a] == rho[b]:
                    assert types[a] == types[b]
            for a in range(n):
                if psi[a]:
                    assert any(join[p][join[a][z]] == join[a][z] for z in zeros)
    return {"minimal_cut_target_pairs": cases,
            "translation_dichotomies": dichotomies,
            "atomic_owner_map_entries": entries}


def audit_residual_profiles(join, choices, rho, quotient, cuts,
                            derivative, enabled, reduced_words):
    """Exact cut-orbit congruences, retaining the prescribed atomic base.

    Orders of tags can matter globally.  For one fixed initial cut, however,
    every legal ordering of the same set has one endpoint; every illegal
    word ends at constant one.  Only the nonconstant-one endpoints need
    profile coordinates.
    """
    n = len(join)
    m = max(rho) + 1
    tables = choices + [join]
    one = cuts.index((1,) * n)
    records = []
    all_class_maps = []
    transition_checks = congruence_checks = common_fiber_checks = 0
    separation_checks = 0
    for initial, chi in enumerate(cuts):
        orbit = {initial}
        todo = [initial]
        for current in todo:
            for tag in range(m):
                target = derivative[current][tag]
                if target not in orbit:
                    orbit.add(target)
                    todo.append(target)
                transition_checks += 1

        # Independently obtain the same orbit using legal squarefree words.
        legal_sets = {}
        for word in reduced_words:
            current = initial
            legal = True
            for tag in word:
                legal = legal and enabled[current][tag]
                current = derivative[current][tag]
            if legal:
                key = frozenset(word)
                assert key not in legal_sets or legal_sets[key] == current
                legal_sets[key] = current
            else:
                assert current == one
        kept = sorted(orbit - {one})
        assert set(kept) == set(legal_sets.values()) - {one}
        assert len(kept) <= len(legal_sets) <= (1 << m)
        assert all(derivative[current][tag] in orbit
                   for current in orbit for tag in range(m))

        signatures = [(rho[a], tuple(cuts[q][a] for q in kept))
                      for a in range(n)]
        ids = {signature: i for i, signature in enumerate(dict.fromkeys(signatures))}
        class_map = [ids[signature] for signature in signatures]
        representatives = [class_map.index(i) for i in range(len(ids))]
        class_tags = [rho[a] for a in representatives]
        class_tables = [
            [[class_map[h[a][b]] for b in representatives] for a in representatives]
            for h in tables
        ]
        assert set(class_tags) == set(range(m))
        assert all(class_tags[class_map[a]] == rho[a] for a in range(n))
        assert len(ids) <= m * (1 << len(kept)) <= m * (1 << (1 << m))

        for h, class_h in zip(tables, class_tables):
            for a, b in product(range(n), repeat=2):
                assert class_map[h[a][b]] == class_h[class_map[a]][class_map[b]]
                congruence_checks += 1
        for operation, class_h in enumerate(class_tables):
            for a, b in product(range(len(ids)), repeat=2):
                assert (class_tags[class_h[a][b]]
                        == quotient[operation][class_tags[a]][class_tags[b]])
                if class_tags[a] == class_tags[b]:
                    assert class_h[a][b] == class_tables[-1][a][b]
                    common_fiber_checks += 1
        for a, b in product(range(n), repeat=2):
            if chi[a] != chi[b]:
                assert class_map[a] != class_map[b]
                separation_checks += 1
        all_class_maps.append(class_map)
        records.append({"initial_cut": initial,
                        "nonconstant_one_derivatives": len(kept),
                        "legal_tag_sets": len(legal_sets),
                        "quotient_size": len(ids)})
    assert len({tuple(q[a] for q in all_class_maps) for a in range(n)}) == n
    return {"profile_quotients": len(records),
            "derivative_transition_checks": transition_checks,
            "quotient_homomorphism_entries": congruence_checks,
            "common_atomic_fiber_entries": common_fiber_checks,
            "original_cut_separations": separation_checks,
            "profiles": records}


@lru_cache(None)
def shapes(internal):
    if internal == 0:
        return (None,)
    return tuple((left, right) for i in range(internal)
                 for left in shapes(i) for right in shapes(internal - 1 - i))


def decorate(shape, labels):
    labels = iter(labels)
    leaf = 0
    def build(s):
        nonlocal leaf
        if s is None:
            ans = leaf
            leaf += 1
            return ans
        h = next(labels)
        return (h, build(s[0]), build(s[1]))
    return build(shape)


def audit_model(name, join, choices, rho):
    n = len(join)
    carrier = range(n)
    ops = []
    for h in choices + [join]:
        if h not in ops:
            ops.append(h)
    tags = range(max(rho) + 1)
    fibers = [[a for a in carrier if rho[a] == c] for c in tags]
    reps = [fiber[0] for fiber in fibers]
    quotient = [[[rho[h[a][b]] for b in reps] for a in reps] for h in choices + [join]]
    for h, qh in zip(choices + [join], quotient):
        for x, y in product(carrier, repeat=2):
            assert rho[h[x][y]] == qh[rho[x]][rho[y]]
            if rho[x] == rho[y]:
                assert h[x][y] == join[x][y]
    for c, x in product(tags, repeat=2):
        v = quotient[-1][c][x]
        for h in quotient[:-1]:
            v = h[x][v]
        assert v == x

    pi = []
    for c in carrier:
        row = []
        for x in carrier:
            v = join[c][x]
            for h in choices:
                v = h[x][v]
            row.append(v)
        pi.append(row)
    right = [[pi[x][a] for x in carrier] for a in carrier]
    for a, x, y in product(carrier, repeat=3):
        assert right[a][join[x][y]] == join[right[a][x]][right[a][y]]
        assert rho[right[a][x]] == rho[a]
        assert join[a][right[a][x]] == right[a][x]
        assert join[right[a][x]][join[a][x]] == join[a][x]
    for a, b, x in product(carrier, repeat=3):
        if rho[a] == rho[b]:
            assert right[join[a][b]][x] == join[b][right[a][x]] == join[a][right[b][x]]
            assert right[a][right[b][x]] == right[join[a][b]][x]

    # Every join cut on a finite join semilattice has an empty or principal zero ideal.
    cuts = [tuple(int(join[x][bound] != bound) for x in carrier) for bound in carrier]
    cuts.append((1,) * n)
    assert len(set(cuts)) == n + 1
    index = {cut: i for i, cut in enumerate(cuts)}
    derivative = []
    enabled = []
    factorization = 0
    for chi in cuts:
        enabled.append([any(chi[a] == 0 for a in fiber) for fiber in fibers])
        row = []
        for c, fiber in enumerate(fibers):
            result = tuple(min(chi[right[a][x]] for a in fiber) for x in carrier)
            assert result in index
            row.append(index[result])
            for a in fiber:
                for x in carrier:
                    assert chi[right[a][x]] == (chi[a] | result[x])
                    factorization += 1
                assert result[a] == chi[a]
        derivative.append(row)
    commuting = 0
    for q, chi in enumerate(cuts):
        for c in tags:
            result = derivative[q][c]
            assert derivative[result][c] == result
            if enabled[q][c]:
                assert all(a <= b for a, b in zip(cuts[result], chi))
            else:
                assert cuts[result] == (1,) * n
        for c, d in product(tags, repeat=2):
            if enabled[q][c] and enabled[q][d]:
                assert derivative[derivative[q][c]][d] == derivative[derivative[q][d]][c]
                commuting += 1

    operation_rule = cut_operation_rule = 0
    for h in ops:
        for x, y in product(carrier, repeat=2):
            out = h[x][y]
            for a in fibers[rho[out]]:
                assert right[a][join[x][y]] == join[a][out]
                operation_rule += 1
            for q, chi in enumerate(cuts):
                dchi = cuts[derivative[q][rho[out]]]
                assert chi[out] == (dchi[x] | dchi[y])
                cut_operation_rule += 1

    @lru_cache(None)
    def path_action(path):
        ans = []
        for q in range(len(cuts)):
            for tag in path:
                q = derivative[q][tag]
            ans.append(q)
        return tuple(ans)

    def first_occurrences(path):
        return tuple(dict.fromkeys(path))

    # Every reduced word and every one-letter extension are checked as
    # transformations of ALL cuts. Induction then checks arbitrary word
    # lengths in these finite models, including words with an illegal step.
    reduced_words = [word for length in range(len(tags) + 1)
                     for word in permutations(tags, length)]
    word_transitions = 0
    derivative_actions = set()
    for word in reduced_words:
        derivative_actions.add(path_action(word))
        for c in tags:
            extended = word + (c,)
            assert path_action(extended) == path_action(first_occurrences(extended))
            word_transitions += len(cuts)
    order_matters = sum(path_action((c, d)) != path_action((d, c))
                        for c, d in permutations(tags, 2))
    if name == "D2":
        assert order_matters  # Replacing ordered words by sets is invalid.

    def evaluate(term, values):
        if isinstance(term, int):
            value = values[term]
            return value, [((rho[value],), term)]
        h, left, rchild = term
        a, left_paths = evaluate(left, values)
        b, right_paths = evaluate(rchild, values)
        value = ops[h][a][b]
        tag = rho[value]
        return value, [((tag,) + p, leaf) for p, leaf in left_paths + right_paths]

    path_checks = term_valuations = 0
    scopes = []
    for internal in range(4):
        before = term_valuations
        for shape in shapes(internal):
            for labels in product(range(len(ops)), repeat=internal):
                term = decorate(shape, labels)
                for values in product(carrier, repeat=internal + 1):
                    actual, paths = evaluate(term, values)
                    endpoints = [(path_action(first_occurrences(path)), values[leaf])
                                 for path, leaf in paths]
                    for q, chi in enumerate(cuts):
                        predicted = int(any(cuts[action[q]][value] for action, value in endpoints))
                        assert chi[actual] == predicted
                        path_checks += 1
                    term_valuations += 1
        scopes.append({"internal_nodes": internal, "term_valuations": term_valuations - before})
    return {"model": name, "size": n, "atomic_base_size": len(fibers),
            "join_cuts": len(cuts), "distinct_basic_tables": len(ops),
            "factorization_checks": factorization, "enabled_commutations": commuting,
            "right_reset_operation_checks": operation_rule,
            "cut_operation_checks": cut_operation_rule,
            "first_occurrence_transition_checks": word_transitions,
            "distinct_derivative_word_actions": len(derivative_actions),
            "order_sensitive_tag_pairs": order_matters,
            "path_checks": path_checks, "path_scopes": scopes,
            "residual_profiles": audit_residual_profiles(
                join, choices, rho, quotient, cuts, derivative, enabled,
                reduced_words),
            "minimal_cuts": audit_minimal_cuts(join, choices, rho)}


def main():
    records = [audit_model(*model) for model in [native(2), native(3), nonflat()]]
    print(json.dumps({"status": "PASS", "models": records,
                      "scope": "All join cuts and their exact derivative-profile quotients; all operation/anchor tuples; all reduced-word transitions; every binary tree with at most3 internal nodes and all assignments."}, indent=2))


if __name__ == "__main__":
    main()
