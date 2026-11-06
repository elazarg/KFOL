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
                    endpoints = [(path_action(path), values[leaf]) for path, leaf in paths]
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
            "path_checks": path_checks, "path_scopes": scopes}


def main():
    records = [audit_model(*model) for model in [native(2), native(3), nonflat()]]
    print(json.dumps({"status": "PASS", "models": records,
                      "scope": "All join cuts; all operation/anchor tuples; every binary tree with at most3 internal nodes and all assignments."}, indent=2))


if __name__ == "__main__":
    main()
