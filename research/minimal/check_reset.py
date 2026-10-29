"""Independent checks of the exact reset calculus, including mixed inputs."""

from itertools import combinations, product
from math import comb
from random import Random

from reset import (Normal, Reset, admissible, antimatroids, compose, evaluate,
                   feasible, form_from_family, frontier, minimal, normal,
                   product_families, realize, selected, selector_closure,
                   synthesize, witness)
from structure import Var


def check_families():
    counts = [len(antimatroids(n)) for n in range(5)]
    assert counts == [1, 1, 3, 22, 485]
    forms_by_arity = {}
    for arity in range(1, 5):
        # Enumerate all families on the arity, permitting dummy variables,
        # then select the antimatroids with a unique initial element.
        forms = set()
        for support in range(1, 1 << arity):
            labels = [i for i in range(arity) if support & (1 << i)]
            for small in antimatroids(len(labels)):
                family = frozenset(sum(1 << labels[i] for i in range(len(labels)) if a & (1 << i))
                                   for a in small)
                if sum(1 for a in family if a.bit_count() == 1) != 1:
                    continue
                form = form_from_family(family, arity)
                assert admissible(form) and feasible(form) == family
                term = synthesize(form)
                assert normal(term, arity) == form
                for status in range(1 << arity):
                    assert selected(form, status) == frontier(family, status, arity)
                forms.add(form)
        tables = {tuple(selected(f, s) for s in range(1 << arity)) for f in forms}
        assert tables == selector_closure(arity)
        expected = sum(comb(arity, m) * m * counts[m-1] for m in range(1, arity+1))
        assert len(forms) == expected
        forms_by_arity[arity] = sorted(forms, key=lambda f: (f.root, f.guards))
        print(f"Arity {arity}: {len(forms)} reset functions; independent term closure and antimatroid enumeration agree",
              flush=True)
    # All binary compositions of the 140 four-argument functions.
    forms = forms_by_arity[4]
    for first, second in product(forms, repeat=2):
        term = Reset(synthesize(first), synthesize(second))
        result = normal(term, 4)
        assert feasible(result) == product_families(feasible(first), feasible(second))
    print("All 140^2 antimatroid products match reset", flush=True)
    return forms_by_arity


def check_tables_five():
    # Exhaust every possible normalized prerequisite table with root 0.
    # For each other output, guards contain 0 and omit that output:
    # monotone antichains on the remaining three bits give 20 choices.
    arity = 5
    choices = []
    for j in range(1, arity):
        others = [i for i in range(1, arity) if i != j]
        subsets = [1 | sum(1 << others[i] for i in range(3) if a & (1 << i)) for a in range(8)]
        families = {minimal(subsets[i] for i in range(8) if mask & (1 << i)) for mask in range(256)}
        assert len(families) == 20
        choices.append(sorted(families))
    accepted = []
    for rest in product(*choices):
        form = Normal(0, ((0,),) + rest)
        if admissible(form):
            assert normal(synthesize(form), arity) == form
            accepted.append(form)
    assert len(accepted) == 596
    assert 5 * len(accepted) == 2980
    print("Arity 5: all 20^4 root-0 prerequisite tables checked; 596 accepted, giving 2980 functions", flush=True)
    return accepted


def check_semantics(forms_by_arity, large):
    for arity in (2, 3):
        for form in forms_by_arity[arity]:
            term = synthesize(form)
            for inputs in product(range(1, 8), repeat=arity):
                assert evaluate(term, inputs) == realize(form, inputs)
    forms = forms_by_arity[4]
    for first, second in combinations(forms, 2):
        inputs = witness(first, second)
        assert inputs is not None and realize(first, inputs) != realize(second, inputs)
    rng = Random(730)
    for _ in range(500):
        form = rng.choice(large)
        term = synthesize(form)
        inputs = tuple(rng.randrange(1, 16) for _ in range(5))
        assert evaluate(term, inputs) == realize(form, inputs)
    for _ in range(1000):
        outer = rng.choice(forms_by_arity[3])
        inner = [rng.choice(forms) for _ in range(3)]
        result = compose(outer, inner)
        assert admissible(result)
        for _ in range(5):
            inputs = tuple(rng.randrange(1, 8) for _ in range(4))
            assert realize(result, inputs) == realize(outer, tuple(realize(f, inputs) for f in inner))
    # All two-value domains fail to test associativity, even when not closed.
    x, y, z = Var(0), Var(1), Var(2)
    first, second = Reset(Reset(x, y), z), Reset(x, Reset(y, z))
    assert evaluate(first, (7, 1, 3)) != evaluate(second, (7, 1, 3))
    for a, b in combinations(range(1, 16), 2):
        assert all(evaluate(first, inputs) == evaluate(second, inputs)
                   for inputs in product((a, b), repeat=3))
    print("Full small mixed-input semantics, all four-variable separators, and 1000 substitutions passed", flush=True)


if __name__ == "__main__":
    small = check_families()
    large = check_tables_five()
    check_semantics(small, large)
