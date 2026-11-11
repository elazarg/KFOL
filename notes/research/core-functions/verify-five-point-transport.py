#!/usr/bin/env python3
"""Check a finite owner-elimination certificate using only its input matrix.

Run this file directly; --clauses also prints its complete clause family.
No generated subpower, term-function enumeration, or third-party package is
used. See transport-orders.md for the mathematical soundness argument.

An atom is encoded by row * K + role. A clause has an optional membership
premise and a list of head atoms. None in an auxiliary slot means that its
expanded blocker is tautological. Otherwise the slot names a family clause
with the same premise (or no premise) and a subset of the required head.
"""

import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(certificate):
    require(certificate["format"] == "kfol-owner-transport-v1", "format")
    k = certificate["K"]
    m = certificate["M"]
    require(type(k) is int and k > 0, "positive number of roles")
    require(type(m) is int and m > 0, "positive number of rows")
    size = k * m
    family = certificate["clauses"]
    rows = certificate["rows"]
    require(len(rows) == m, "matrix row count")
    arity = len(rows[0])
    require(all(len(row) == arity for row in rows), "rectangular matrix")
    require(
        all(type(value) is int and 0 < value < (1 << k)
            for row in rows for value in row),
        "matrix entries must be nonempty role sets",
    )
    require(0 <= certificate["root"] < len(family), "root clause index")

    for clause in family:
        premise = clause["premise"]
        head = clause["head"]
        require(
            premise is None or type(premise) is int and 0 <= premise < size,
            "premise atom",
        )
        require(
            all(type(atom) is int and 0 <= atom < size for atom in head),
            "head atoms",
        )
        require(len(set(head)) == len(head), "repeated head atom")
        require(len(clause["owners"]) == k, "owner-order count")

    def entails(index, premise, head):
        if index is None:
            return premise is not None and premise in head
        require(type(index) is int and 0 <= index < len(family),
                "auxiliary clause index")
        auxiliary = family[index]
        return (
            auxiliary["premise"] in (None, premise)
            and set(auxiliary["head"]) <= head
        )

    # Variable cases: each input column must satisfy the whole family.
    for column in zip(*rows):
        memberships = sum(value << (k * row) for row, value in enumerate(column))
        for clause in family:
            premise = clause["premise"]
            require(
                premise is not None and not (memberships >> premise & 1)
                or any(memberships >> atom & 1 for atom in clause["head"]),
                "a variable column violates a clause",
            )

    steps = 0
    for clause in family:
        premise = clause["premise"]
        head = set(clause["head"])
        for owner, data in enumerate(clause["owners"]):
            inherited = {atom for atom in head if atom % k == owner}
            for step in data["order"]:
                atom = step["atom"]
                require(atom in head - inherited, "new head atom in order")
                expanded_head = inherited | {
                    atom // k * k + role for role in range(k) if role != owner
                }
                if premise is None or premise % k == owner:
                    expanded_premises = [None]
                else:
                    expanded_premises = [
                        premise // k * k + role
                        for role in range(k) if role != owner
                    ]
                require(len(expanded_premises) == len(step["aux"]),
                        "expanded-blocker count")
                require(
                    all(entails(index, expanded, expanded_head)
                        for index, expanded in
                        zip(step["aux"], expanded_premises)),
                    "an auxiliary does not imply its blocker",
                )
                inherited.add(atom)
                steps += 1
            require(entails(data["terminal"], premise, inherited),
                    "terminal clause is not supported by the inherited head")
    return arity, steps


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clauses", action="store_true")
    args = parser.parse_args()
    certificate = json.loads(
        Path(__file__).with_name("five-point-transport.json").read_text()
    )
    arity, steps = verify(certificate)
    k = certificate["K"]
    role_names = certificate["role_names"]
    row_names = certificate["row_names"]

    def atom_name(atom):
        return role_names[atom % k] + row_names[atom // k]

    def clause_name(clause):
        premise = clause["premise"]
        left = "TRUE" if premise is None else atom_name(premise)
        return left + " => " + " or ".join(map(atom_name, clause["head"]))

    family = certificate["clauses"]
    print(f"Verified {len(family)} clauses on {arity} input columns; "
          f"{k * len(family)} owner orders and {steps} blocker steps.")
    print("Root:", clause_name(family[certificate["root"]]))
    if args.clauses:
        for index, clause in enumerate(family):
            print(index, clause_name(clause))


if __name__ == "__main__":
    main()
