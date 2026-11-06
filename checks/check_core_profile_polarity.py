#!/usr/bin/env python3
"""Check the owner-profile polarity theorem at every term depth.

For a selected owner h, a Boolean profile interprets h as AND and all
other operations as OR.  We close triples (actual value, low, high), where
low is the profile at x=1/other variables=0 and high is its value at
x=0/other variables=1.  All carrier elements are available as separate
parameter variables.  Thus finite closure covers all arities and depths
in each selected algebra, rather than a bounded list of terms.

The written proof uses choice-image closure to obtain
    t_h <= x  ==> h(x,t)=t,
and the mixed-meet formula to obtain
    t_h >= x  ==> x <= h(x,t).
In particular, an atomic identity P=x makes every h(x,P)=P; pair coverage
then gives x+P=P.  The computation below is a finite audit of these
conclusions, not a proof of free atomic generator irreducibility or an
unrestricted finite basis.

Only the Python standard library and checked-in model tables are used.
"""

from __future__ import annotations

import itertools
import json
from pathlib import Path


def native_tables(owners):
    """The ambient marker algebra D_K, with join first."""
    neutral, top = owners, owners + 1
    values = range(owners + 2)

    def join(x, y):
        if x == y:
            return x
        return top if top in (x, y) else neutral

    tables = [[[join(x, y) for y in values] for x in values]]
    tables.extend(
        [[i if i in (x, y) else join(x, y) for y in values]
         for x in values]
        for i in range(owners)
    )
    return tables


def models():
    yield "D2", native_tables(2)
    yield "D3", native_tables(3)
    data = Path(__file__).with_name("data")
    six = json.loads((data / "core-six-models.json").read_text())
    for index, description in ((2, "one-owner"), (0, "two-owner")):
        model = six[index]
        tables = [model["join"], *model["operations"]]
        assert len(tables[0]) == 6
        active = sum(table != tables[0] for table in tables[1:])
        assert active == (1 if index == 2 else 2)
        yield f"core6-{description}", tables
    model = json.loads(
        (data / "core-owned-unit-depth-countermodel.json").read_text()
    )
    assert len(model["join"]) == 24
    yield "core24", [model["join"], *model["operations"]]


def audit_laws(tables):
    """Independently verify exactly Gamma and all ordered M laws."""
    add, *choices = tables
    size = len(add)
    values = range(size)
    checks = 0
    for table in tables:
        assert len(table) == size
        assert all(len(row) == size for row in table)
        assert all(0 <= z < size for row in table for z in row)
        for x in values:
            assert table[x][x] == x
            checks += 1
        for x, y in itertools.product(values, repeat=2):
            assert table[x][y] == table[y][x]
            checks += 1
        for x, y, z in itertools.product(values, repeat=3):
            assert table[table[x][y]][z] == table[x][table[y][z]]
            checks += 1
    for choice in choices:
        for x, y, z in itertools.product(values, repeat=3):
            assert choice[x][add[y][z]] == add[choice[x][y]][choice[x][z]]
            checks += 1
    for i, first in enumerate(choices):
        for j, second in enumerate(choices):
            if i == j:
                continue
            for x, y in itertools.product(values, repeat=2):
                assert first[x][second[x][y]] == second[x][first[x][y]]
                assert add[first[x][y]][second[x][y]] == add[x][y]
                checks += 2
            for x, y, z in itertools.product(values, repeat=3):
                yz = first[y][z]
                assert (first[x][second[y][yz]]
                        == first[x][second[y][first[x][yz]]])
                checks += 1
    return checks


def profile_product(selected, operation, left, right):
    if operation == selected:
        return left & right
    return left | right


def audit_closure(tables, selected, distinguished):
    size = len(tables[0])
    states, nodes, positions = [], [], {}

    def insert(state, node):
        if state not in positions:
            positions[state] = len(states)
            states.append(state)
            nodes.append(node)
        return positions[state]

    insert((distinguished, 1, 0), ("x",))
    for value in range(size):
        insert((value, 0, 1), ("parameter", value))
    cursor = 0
    while cursor < len(states):
        a, low_a, high_a = states[cursor]
        for other in range(cursor + 1):
            b, low_b, high_b = states[other]
            for operation, table in enumerate(tables):
                insert(
                    (table[a][b],
                     profile_product(selected, operation, low_a, low_b),
                     profile_product(selected, operation, high_a, high_b)),
                    (operation, cursor, other),
                )
        cursor += 1
    assert len(states) <= 4 * size

    # Replay every retained witness from its DAG, without trusting its state.
    replayed = []
    for index, node in enumerate(nodes):
        if node[0] == "x":
            value = (distinguished, 1, 0)
        elif node[0] == "parameter":
            value = (node[1], 0, 1)
        else:
            operation, left, right = node
            assert left < index and right < index
            a, low_a, high_a = replayed[left]
            b, low_b, high_b = replayed[right]
            boolean = ((lambda x, y: int(bool(x) and bool(y)))
                       if operation == selected else
                       (lambda x, y: int(bool(x) or bool(y))))
            value = (tables[operation][a][b],
                     boolean(low_a, low_b), boolean(high_a, high_b))
        assert value == states[index]
        replayed.append(value)

    # An independent ordered-pair pass certifies actual closure.
    closure_entries = 0
    for operation, table in enumerate(tables):
        for a, low_a, high_a in states:
            for b, low_b, high_b in states:
                state = (
                    table[a][b],
                    profile_product(selected, operation, low_a, low_b),
                    profile_product(selected, operation, high_a, high_b),
                )
                assert state in positions
                closure_entries += 1

    def expression(index):
        node = nodes[index]
        if node[0] == "x":
            return "x"
        if node[0] == "parameter":
            return f"y{node[1]}"
        operation, left, right = node
        symbol = "+" if operation == 0 else f"f{operation - 1}"
        return f"{symbol}({expression(left)},{expression(right)})"

    polarity_entries = 0
    add, choice = tables[0], tables[selected]
    for index, (value, low, high) in enumerate(states):
        translated = choice[distinguished][value]
        if low:
            assert add[distinguished][translated] == translated, (
                "upper-profile failure", selected - 1, distinguished,
                value, expression(index),
            )
            polarity_entries += 1
        if not high:
            assert translated == value, (
                "lower-profile failure", selected - 1, distinguished,
                value, expression(index),
            )
            polarity_entries += 1
    return len(states), closure_entries, polarity_entries


def check():
    totals = dict(models=0, law_instances=0, closures=0, witness_states=0,
                  closure_entries=0, polarity_entries=0)
    for name, tables in models():
        totals["models"] += 1
        totals["law_instances"] += audit_laws(tables)
        row = dict(model=name, size=len(tables[0]), closures=0,
                   witness_states=0, closure_entries=0, polarity_entries=0)
        for selected in range(1, len(tables)):
            for distinguished in range(len(tables[0])):
                states, closure, polarity = audit_closure(
                    tables, selected, distinguished
                )
                row["closures"] += 1
                row["witness_states"] += states
                row["closure_entries"] += closure
                row["polarity_entries"] += polarity
        for key in ("closures", "witness_states", "closure_entries",
                    "polarity_entries"):
            totals[key] += row[key]
        print(json.dumps(row, sort_keys=True))
    print("PASS", json.dumps(totals, sort_keys=True))
    return totals


if __name__ == "__main__":
    check()
