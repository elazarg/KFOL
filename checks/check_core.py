"""Independent checks of idempotent elimination and optimal test domains."""

from itertools import combinations, permutations
from random import Random

from core import complete_idempotency_domain, idempotent_core, optimal_idempotency_domain
from structure import Choice, Var, Win, neutral_join
from symmetric import Rename, evaluate, swap, unary_closure_three


def check_domains():
    functions = unary_closure_three()
    global_minimum = min(len(domain) for mask in range(128)
                         if (domain := [s for s in range(1, 8) if mask & (1 << (s-1))])
                         and sum(all(f[s-1] == s for s in domain) for f in functions) == 1)
    assert global_minimum == 3
    for count in (3, 4):
        ambiguous = [s for s in range(1, 1 << count) if s.bit_count() >= 2]
        minimum = len(ambiguous)
        for mask in range(1 << len(ambiguous)):
            domain = [s for j, s in enumerate(ambiguous) if mask & (1 << j)]
            complete = complete_idempotency_domain(domain, count)
            if count == 3:
                agrees = [f for f in functions if all(f[s-1] == s for s in domain)]
                assert (agrees == [tuple(range(1, 8))]) == complete
            if complete:
                minimum = min(minimum, len(domain))
                continue
            intersection = (1 << count) - 1
            for s in domain:
                intersection &= s
            if intersection:
                role = (intersection & -intersection).bit_length() - 1
                witness = neutral_join(Var(0), Win(role))
            else:
                i, j = next((i, j) for i, j in combinations(range(count), 2)
                            if all(bool(s & (1 << i)) == bool(s & (1 << j)) for s in domain))
                witness = Rename(swap(count, i, j), Var(0))
            assert all(evaluate(witness, (s,)) == s for s in domain)
            assert any(evaluate(witness, (s,)) != s for s in range(1, 1 << count))
        assert minimum == len(optimal_idempotency_domain(count)) == 3
    for count in range(5, 65):
        domain = optimal_idempotency_domain(count)
        assert complete_idempotency_domain(domain, count)
        assert len(domain) == count.bit_length()
    print("Idempotency domains: every ambiguous domain at K=3,4; optimal constructions K=3..64")


def check_elimination():
    rng = Random(92)
    checked = 0
    for count in range(3, 7):
        ps = list(permutations(range(count)))
        arity = 3
        def arbitrary(depth, pure=False):
            if not depth:
                return Var(rng.randrange(arity)) if pure or rng.randrange(2) else Win(rng.randrange(count))
            if not pure and rng.randrange(3) == 0:
                return Rename(rng.choice(ps), arbitrary(depth - 1))
            return Choice(rng.randrange(count), arbitrary(depth - 1, pure), arbitrary(depth - 1, pure))
        def decorate(t):
            if isinstance(t, Var):
                return t
            p = rng.choice(ps)
            inverse = tuple(p.index(i) for i in range(count))
            return Rename(p, Choice(inverse[t.role], Rename(inverse, decorate(t.left)),
                                    Rename(inverse, decorate(t.right))))
        for i in range(300):
            term = arbitrary(3) if i % 2 else decorate(arbitrary(2, True))
            pure = idempotent_core(term, count)
            semantic = all(evaluate(term, (s,) * arity) == s for s in range(1, 1 << count))
            assert semantic == (pure is not None)
            assert semantic == all(evaluate(term, (s,) * arity) == s
                                   for s in optimal_idempotency_domain(count))
            if pure is not None:
                for _ in range(20):
                    inputs = tuple(rng.randrange(1, 1 << count) for _ in range(arity))
                    assert evaluate(term, inputs) == evaluate(pure, inputs)
            checked += 1
    print(f"Idempotent elimination: {checked} terms, full diagonal checks and equivalent extracted cores")


if __name__ == "__main__":
    check_domains()
    check_elimination()
