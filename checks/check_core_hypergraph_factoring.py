#!/usr/bin/env python3
"""Finite checks of hypergraph cover factorization and its coverage boundary.

Standard library only. This checks explicit finite scopes, not the uniform
proof. All folds are nonempty. The extra five-state model has a native
seven-point cover checked here; no external corpus or solver is required.
"""
from itertools import combinations, permutations, product
import json


def native_tables(owners):
    size = owners + 2
    join = [[x if x == y else max(owners, x, y)
             for y in range(size)] for x in range(size)]
    return [
        [[i if i in (x, y) else join[x][y] for y in range(size)]
         for x in range(size)]
        for i in range(owners)
    ] + [join]


def fold(table, values):
    values = iter(values)
    answer = next(values)  # Empty folds are deliberately not defined.
    for value in values:
        answer = table[answer][value]
    return answer


def fixture(name, edges, families):
    edges = tuple(tuple(sorted(edge)) for edge in edges)
    vertices = tuple(sorted(set().union(*map(set, edges))))
    assert edges and all(len(edge) >= 2 for edge in edges)
    families = tuple(tuple(tuple(sorted(cover)) for cover in family)
                     for family in families)
    for family in families:
        assert family
        assert set().union(*map(set, family)) == set(vertices)
        for cover in family:
            assert cover and set(cover) <= set(vertices)
            assert all(set(cover).intersection(edge) for edge in edges)
    return name, vertices, edges, families


def fixtures():
    result = []
    possible_edges = ((0, 2), (0, 3), (1, 2), (1, 3))
    for mask in range(1, 16):
        edges = tuple(edge for i, edge in enumerate(possible_edges)
                      if mask & (1 << i))
        vertices = set().union(*map(set, edges))
        rows, columns = sorted(vertices & {0, 1}), sorted(vertices & {2, 3})
        result.append(fixture(f"bipartite_2_by_2_{mask}", edges,
                              ((rows, columns), (vertices,))))
    cycle = tuple((i, 3 + j) for i in range(3)
                  for j in (i, (i + 1) % 3))
    result.append(fixture("chordless_cycle_6", cycle,
                          (((0, 1, 2), (3, 4, 5)), (range(6),))))
    triangle = ((0, 1), (0, 2), (1, 2))
    covers = tuple(combinations(range(3), 2))
    result.append(fixture("triangle", triangle,
                          tuple(combinations(covers, 2)) + (covers,)))
    triples = tuple(combinations(range(4), 3))
    for mask in range(1, 16):
        edges = tuple(edge for i, edge in enumerate(triples)
                      if mask & (1 << i))
        vertices = set().union(*map(set, edges))
        co_singletons = tuple(vertices - {v} for v in sorted(vertices))
        result.append(fixture(f"three_uniform_on_four_{mask}", edges,
                              ((vertices,), co_singletons,
                               co_singletons[:2])))
    for name, edges in (
        ("three_uniform_chain", ((0, 1, 2), (1, 2, 3), (2, 3, 4))),
        ("mixed_residual_covered", ((0, 1, 2), (0, 3), (1, 4))),
    ):
        vertices = set(range(5))
        covers = tuple(vertices - {v} for v in range(5))
        result.append(fixture(name, edges,
                              ((vertices,), covers, covers[:2])))
    return result


def five_state_core():
    """Stored M3 example, with its native cover supplied explicitly."""
    join = [[0] * 5 for _ in range(5)]
    for x, y in product(range(5), repeat=2):
        join[x][y] = y if x == 0 else x if y == 0 else x if x == y else 4
    f = [
        [0, 0, 0, 0, 0],
        [0, 1, 2, 3, 4],
        [0, 2, 2, 0, 2],
        [0, 3, 0, 3, 3],
        [0, 4, 2, 3, 4],
    ]
    tables = [join, join, f, join]
    # Native D3 values: owner-2 atom=2, neutral=3, greatest marker=4.
    cover = {(2, 2): 0, (2, 4): 3, (3, 3): 1, (3, 4): 4,
             (4, 2): 2, (4, 3): 4, (4, 4): 4}
    native = native_tables(3)
    entries = 0
    assert set(cover.values()) == set(range(5))
    for k, table in enumerate(native):
        for x, y in product(cover, repeat=2):
            value = tuple(table[a][b] for a, b in zip(x, y))
            assert value in cover
            assert cover[value] == tables[k][cover[x]][cover[y]]
            entries += 1
    assert entries == 196
    return tables, entries


def verify_fixture(tables, case):
    _, vertices, edges, families = case
    join = tables[-1]
    size = len(join)
    counts = {"valuations": 0, "cover_family_checks": 0,
              "edge_cover_checks": 0, "support_checks": 0}
    for f_index, g_index in permutations(range(len(tables)), 2):
        f, g = tables[f_index], tables[g_index]
        for values in product(range(size), repeat=len(vertices)):
            x = dict(zip(vertices, values))
            edge_values = [fold(f, (x[v] for v in edge)) for edge in edges]
            q = fold(g, edge_values)
            arms = {}
            for vertex in vertices:
                neighbors = [fold(f, (x[u] for u in edge if u != vertex))
                             for edge in edges if vertex in edge]
                arms[vertex] = f[x[vertex]][fold(g, neighbors)]
                assert g[q][arms[vertex]] == q
            w = fold(g, arms.values())
            assert g[q][w] == q
            for edge, value in zip(edges, edge_values):
                bound = fold(join, (arms[v] for v in edge))
                assert join[value][bound] == bound
                # The contraction is an inequality, not generally equality.
                assert join[g[w][value]][w] == w
                counts["edge_cover_checks"] += 1
            assert w == q
            cover_cache = {}
            for family in families:
                results = []
                for cover in family:
                    if cover not in cover_cache:
                        s = fold(g, (arms[v] for v in cover))
                        assert join[s][q] == q
                        assert all(h[s][q] == q for h in tables)
                        counts["support_checks"] += len(tables) + 1
                        cover_cache[cover] = s
                    results.append(cover_cache[cover])
                assert fold(join, results) == q
                assert all(fold(h, results) == q for h in tables)
                counts["cover_family_checks"] += 1
            counts["valuations"] += 1
    return counts


def omitted_vertex_boundary():
    f, g, join = native_tables(2)
    # Edges {x,y,z}, {x,u}, {y,v}; the two covers omit z.
    x, y, z, u, v = 2, 2, 3, 1, 1
    q = fold(g, (fold(f, (x, y, z)), f[x][u], f[y][v]))
    s = g[f[x][g[f[y][z]][u]]][f[y][v]]
    t = g[f[y][g[f[x][z]][v]]][f[x][u]]
    assert (q, s, t, join[s][t]) == (3, 2, 2, 2)
    assert all(h[s][t] == join[s][t] for h in (f, g, join))
    return {"D2_valuation_x_y_z_u_v": ["n", "n", "p", "beta", "beta"],
            "Q": "p", "S": "n", "T": "n", "S_plus_T": "n",
            "residual_R_S_T": True}


def main():
    cases = fixtures()
    extra, native_entries = five_state_core()
    models = (("D2", native_tables(2), cases),
              ("D3", native_tables(3), cases),
              ("five_state_core_M3", extra,
               [case for case in cases if len(case[1]) <= 4]))
    result = {}
    for name, tables, selected in models:
        total = {"valuations": 0, "cover_family_checks": 0,
                 "edge_cover_checks": 0, "support_checks": 0}
        for case in selected:
            counts = verify_fixture(tables, case)
            for key, value in counts.items():
                total[key] += value
        total["hypergraphs"] = len(selected)
        result[name] = total
    print(json.dumps({"status": "PASS", "finite_scopes": result,
                      "ordered_distinct_operation_symbols_include_join": True,
                      "five_state_native_cover_entries": native_entries,
                      "omitted_vertex_boundary": omitted_vertex_boundary()}, indent=2))


if __name__ == "__main__":
    main()
