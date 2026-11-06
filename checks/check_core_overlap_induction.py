#!/usr/bin/env python3
"""Bounded native checks for contraction, merging, and all-arity overlaps.
Standard library only; no solver, repository imports, or external data.
The uniform derivations are mathematical; finite checks do not replace them.
"""
from itertools import permutations, product
import json


def native_tables(k):
    size = k + 2
    join = [[x if x == y else max(k, x, y)
             for y in range(size)] for x in range(size)]
    return [
        [[i if i in (x, y) else join[x][y] for y in range(size)]
         for x in range(size)] for i in range(k)
    ] + [join]


def fold(table, values):
    assert values
    ans = values[0]
    for value in values[1:]:
        ans = table[ans][value]
    return ans


def verify_tc():
    tested = guarded = 0
    for k in range(2, 6):
        ops = native_tables(k)
        join = ops[-1]
        for i, j in permutations(range(len(ops)), 2):
            f, g = ops[i], ops[j]
            for x, y, u in product(range(k + 2), repeat=3):
                tested += 1
                q = f[x][y]
                if g[q][u] != u:
                    continue
                guarded += 1
                p, r = f[x][g[y][u]], f[x][u]
                top = join[x][u]
                assert join[top][p] == top
                assert join[p][join[x][r]] == join[x][r]
                assert join[p][join[q][r]] == join[q][r]
                assert join[p][r] == r
    f, g, join = native_tables(2)
    x, y, u = 2, 1, 3  # n, beta, p
    assert g[f[x][y]][u] == u
    assert f[x][g[y][u]] == 2 and f[x][u] == 3
    return {"tested_triples": tested, "guarded_triples": guarded,
            "strict_example": {"x": "n", "y": "beta", "u": "p",
                               "left": "n", "right": "p"}}


def verify_merge():
    tested = guarded = 0
    for k in range(2, 5):
        ops = native_tables(k)
        join = ops[-1]
        for i, j in permutations(range(len(ops)), 2):
            f, g = ops[i], ops[j]
            for x, y, z, u, v in product(range(k + 2), repeat=5):
                tested += 1
                if g[f[y][z]][u] != u or g[f[x][z]][v] != v:
                    continue
                guarded += 1
                left = f[f[x][y]][g[z][f[u][v]]]
                cross = fold(f, [x, y, g[z][u], g[z][v]])
                reduced = fold(f, [x, y, u, v])
                right = join[f[x][u]][f[y][v]]
                assert join[left][cross] == cross
                assert join[cross][reduced] == reduced
                assert join[reduced][right] == right
                assert join[left][right] == right
    return {"tested_five_tuples": tested, "guarded_five_tuples": guarded}


def verify_one_grouping(ops, f, g, sources, pads):
    join = ops[-1]
    n = len(sources)
    assert n >= 2 and len(pads) == n
    blockers = []
    arms = []
    for i, x in enumerate(sources):
        complement = fold(f, sources[:i] + sources[i + 1:])
        blocker = g[complement][pads[i]]
        assert g[complement][blocker] == blocker
        blockers.append(blocker)
        arms.append(f[x][blocker])

    # Merge only proper subsets; the complement fold is never empty.
    group_value, group_blocker, group_bound = sources[0], blockers[0], arms[0]
    merges = 0
    for i in range(1, n - 1):
        tail = fold(f, sources[i + 1:])
        singleton, singleton_blocker = sources[i], blockers[i]
        assert g[f[singleton][tail]][group_blocker] == group_blocker
        assert g[f[group_value][tail]][singleton_blocker] == singleton_blocker
        merged_value = f[group_value][singleton]
        merged_blocker = g[tail][f[group_blocker][singleton_blocker]]
        merged_arm = f[merged_value][merged_blocker]
        merge_bound = join[f[group_value][group_blocker]][arms[i]]
        assert join[merged_arm][merge_bound] == merge_bound
        group_bound = join[group_bound][arms[i]]
        assert join[merged_arm][group_bound] == group_bound
        assert g[tail][merged_blocker] == merged_blocker
        group_value, group_blocker = merged_value, merged_blocker
        merges += 1

    last, last_blocker = sources[-1], blockers[-1]
    assert g[last][group_blocker] == group_blocker
    assert g[group_value][last_blocker] == last_blocker
    total = f[group_value][last]
    binary_bound = join[f[group_value][group_blocker]][f[last][last_blocker]]
    assert join[total][binary_bound] == binary_bound
    full_bound = fold(join, arms)
    assert join[binary_bound][full_bound] == full_bound
    assert join[total][full_bound] == full_bound

    # Check every step of the collective factoring consequence as well.
    branches = [f[x][z] for x, z in zip(sources, pads)]
    q = fold(g, [total] + branches)
    alternatives = [fold(g, [arm] + branches[:i] + branches[i + 1:])
                    for i, arm in enumerate(arms)]
    middle = fold(g, arms)
    assert g[q][middle] == q
    assert g[middle][full_bound] == middle
    assert join[g[middle][total]][middle] == middle
    assert fold(g, [middle] + branches) == fold(g, alternatives)
    assert fold(join, alternatives) == q
    for h in ops:
        assert all(join[s][q] == q == h[s][q] for s in alternatives)
        assert fold(h, alternatives) == q
    return merges


def verify_group_induction():
    # Complete finite scopes, with all ordered distinct operations including join.
    scopes = [(2, 2), (3, 2), (4, 2), (2, 3), (3, 3), (2, 4)]
    cases = merge_steps = 0
    records = []
    for k, n in scopes:
        ops = native_tables(k)
        join = ops[-1]
        count = 0
        for i, j in permutations(range(len(ops)), 2):
            for values in product(range(k + 2), repeat=2 * n):
                count += 1
                merge_steps += verify_one_grouping(
                    ops, ops[i], ops[j], list(values[:n]), list(values[n:]))
        cases += count
        records.append({"owners": k, "sources": n, "valuations": count})
    return {"valuations": cases, "merge_steps": merge_steps, "scopes": records,
            "collective_factoring_checked_for_every_basic_operation": True}


def verify_required_alternative():
    f, g, join = native_tables(2)
    alpha, beta, neutral, greatest = range(4)
    sources = [neutral, neutral, greatest]
    pads = [beta, beta, alpha]
    branches = [f[x][z] for x, z in zip(sources, pads)]
    total = fold(f, sources)
    q = fold(g, [total] + branches)
    alternatives = []
    for i, x in enumerate(sources):
        complement = fold(f, sources[:i] + sources[i + 1:])
        arm = f[x][g[complement][pads[i]]]
        alternatives.append(fold(g, [arm] + branches[:i] + branches[i + 1:]))
    assert q == greatest and alternatives == [neutral, neutral, greatest]
    assert join[alternatives[0]][alternatives[1]] != q
    return {"q": "p", "alternatives": ["n", "n", "p"]}


def main():
    print(json.dumps({
        "status": "PASS",
        "TC": verify_tc(),
        "MERGE": verify_merge(),
        "group_induction": verify_group_induction(),
        "deleting_an_alternative_can_fail": verify_required_alternative(),
        "all_ordered_distinct_basic_operations_include_join": True,
    }, indent=2))


if __name__ == "__main__":
    main()
