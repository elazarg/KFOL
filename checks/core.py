"""The intrinsic idempotent core, and optimal ambiguous idempotency tests.

The criterion is exact at K>=3, for arbitrary arity and tree size. The
proof uses live provenance; the finite verification is in check_core.py.
"""

from structure import Choice, Var, Win
from symmetric import Rename


def idempotent_core(term, count):
    """Return an equivalent constant-free owned term, or None if not idempotent."""
    identity = tuple(range(count))
    def go(t, accumulated):
        if isinstance(t, Win):
            return None
        if isinstance(t, Var):
            return t if accumulated == identity else None
        if isinstance(t, Rename):
            return go(t.child, tuple(accumulated[t.permutation[i]] for i in range(count)))
        first, second = go(t.left, accumulated), go(t.right, accumulated)
        if first is None or second is None:
            return None
        return Choice(accumulated[t.role], first, second)
    return go(term, identity)


def complete_idempotency_domain(domain, count):
    """Exact criterion for domains consisting only of ambiguous sets."""
    full = (1 << count) - 1
    if any(s <= 0 or s > full or s.bit_count() < 2 for s in domain):
        raise ValueError("domain must contain only ambiguous winner sets")
    intersection = full
    for s in domain:
        intersection &= s
    signatures = {tuple(bool(s & (1 << i)) for s in domain) for i in range(count)}
    return intersection == 0 and len(signatures) == count


def optimal_idempotency_domain(count):
    if count < 3:
        raise ValueError("requires at least three roles")
    if count == 3:
        return (3, 5, 6)
    size = count.bit_length()  # ceil(log2(K+1)), exactly, without floats
    full_signature = (1 << size) - 1
    # A cycle of two-bit signatures ensures each test set is ambiguous.
    signatures = [(1 << i) | (1 << ((i + 1) % size)) for i in range(size)]
    signatures.extend(s for s in range(full_signature) if s not in signatures)
    signatures = signatures[:count]
    domain = tuple(sum(1 << i for i, s in enumerate(signatures) if s & (1 << j))
                   for j in range(size))
    assert complete_idempotency_domain(domain, count)
    return domain
