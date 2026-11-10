"""Optional real-XPath regression for the TR navigation translation.

Run with python3 checks/check_xpath.py; requires lxml (libxml2 XPath 1.0).
The standard-library suite does not acquire this optional engine dependency.
General correctness and the quadratic constructor bound are proved in Lean.
"""

from itertools import product
from random import Random

from lxml import etree


def non_owner(term, role):
    kind, *args = term
    if kind == "var":
        return f"boolean(child::*[child::in{args[0]}][not(self::r{role})])"
    if kind == "winner":
        return "false()" if args[0] == role else "true()"
    owner, left, right = args
    op = "and" if owner == role else "or"
    return f"({non_owner(left, role)} {op} {non_owner(right, role)})"


def compile_query(term):
    kind, *args = term
    if kind == "var":
        return f"child::*[child::in{args[0]}]"
    if kind == "winner":
        return f"child::r{args[0]}"
    owner, left, right = args
    guard = f"{non_owner(left, owner)} and {non_owner(right, owner)}"
    return (f"({compile_query(left)} | {compile_query(right)})"
            f"[self::r{owner} or parent::*[{guard}]]")


def evaluate(term, valuation):
    kind, *args = term
    if kind == "var":
        return valuation[args[0]]
    if kind == "winner":
        return 1 << args[0]
    role, left, right = args
    a, b = evaluate(left, valuation), evaluate(right, valuation)
    return 1 << role if a == 1 << role or b == 1 << role else a | b


def document(roles, valuation):
    root = etree.Element("valuation")
    for role in range(roles):
        node = etree.SubElement(root, f"r{role}")
        for name, value in enumerate(valuation):
            if value & (1 << role):
                etree.SubElement(node, f"in{name}")
    return root


def main():
    rng = Random(20261110)
    checked = 0
    for roles, arity in [(3, 3), (4, 2)]:
        def generate(depth):
            if depth == 0 or rng.randrange(4) == 0:
                return ("var", rng.randrange(arity)) if rng.randrange(3) else ("winner", rng.randrange(roles))
            return ("choice", rng.randrange(roles), generate(depth - 1), generate(depth - 1))
        terms = [("var", j) for j in range(arity)]
        terms += [("winner", r) for r in range(roles)]
        terms += [generate(4) for _ in range(100)]
        programs = [etree.XPath(compile_query(t)) for t in terms]
        for valuation in product(range(1, 1 << roles), repeat=arity):
            root = document(roles, valuation)
            for term, program in zip(terms, programs):
                actual = {int(node.tag[1:]) for node in program(root)}
                expected = {r for r in range(roles) if evaluate(term, valuation) & (1 << r)}
                assert actual == expected, (term, valuation, actual, expected)
                checked += 1
    neutral = ("choice", 2, ("choice", 0, ("var", 0), ("var", 1)),
               ("choice", 1, ("var", 0), ("var", 1)))
    root = document(3, [0, 4])
    assert etree.XPath(compile_query(neutral))(root) == []
    assert [n.tag for n in root.xpath("child::*[child::in0] | child::*[child::in1]")] == ["r2"]
    print(f"XPath: {checked} comparisons with libxml2 {etree.LIBXML_VERSION}; "
          "all nonempty valuations at K=3/arity=3 and K=4/arity=2; empty-input scope counterexample passed.")


if __name__ == "__main__":
    main()
