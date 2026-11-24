"""Independent finite checks of the one-selector complete-table construction.

Tiny examples enumerate every input tuple, check source reconstruction, and
decide core membership by two-child row peeling. Larger quantified examples
use the actual private-label padding and overlapping addressed rails; their
yes words and one-selector targets are compared on sampled tuples and every
prescribed probe. One-owner envelopes are calculated by explicit safe folds
in the tiny examples and by their greatest allowed support in larger ones.
"""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from random import Random

from addressed_rectangles import (
    Logical, Row, contained, forced_member, joined, members, quantified_rectangles, star, truth,
)


K = 3
C = 2
MENUS = tuple(range(1, 1 << K))
FULL = (1 << K) - 1


def fold(owner, values):
    values = iter(values)
    result = next(values)
    for value in values:
        result = star(owner, result, value)
    return result


def term_value(term, values):
    @cache
    def visit(word):
        if isinstance(word, int):
            return values[word]
        owner, left, right = word
        return star(owner, visit(left), visit(right))
    return visit(term)


def term_support(term):
    if isinstance(term, int):
        return 1 << term
    return term_support(term[1]) | term_support(term[2])


def add_private_labels(logical):
    base = logical.size
    rows = [Row(z.head, z.owner, z.block | (1 << (base + z.owner))) for z in logical.rows]
    start = tuple(block | (1 << (base + owner)) for owner, block in enumerate(logical.start))
    return Logical(base + 2, rows, start, logical.permanent)


def pad(logical):
    padded = add_private_labels(logical)
    base = logical.size
    witness = logical.witness(logical.full, logical.start)
    if witness is None:
        return padded, None
    all_fold = 0
    for i in range(1, padded.size):
        all_fold = (0, all_fold, i)
    return padded, (0, witness, (1, all_fold, base + 1))


def tracks_and_codes(logical):
    # The last two labels are private; color the original sparse conflict
    # graph first, then assign a private track to each padded label.
    originals = logical.size - 2
    neighbors = [set() for _ in range(originals)]
    for block in logical.blocks:
        labels = [v for v in members(block) if v < originals]
        for x in labels:
            neighbors[x].update(y for y in labels if x != y)
    for z in logical.rows:
        for y in members(z.block):
            if y < originals:
                neighbors[z.head].add(y)
                neighbors[y].add(z.head)
    # Permission labels can have unbounded incidence, but never conflict
    # with each other. Reserve track zero for them. Every ordinary label
    # has bounded conflict degree when the permission neighbors are omitted.
    tracks = []
    for x in range(originals):
        if x in logical.permanent:
            assert not neighbors[x].intersection(logical.permanent)
            tracks.append(0)
            continue
        used = {tracks[y] for y in neighbors[x] if y < x}
        tracks.append(next(i for i in range(1, len(used) + 2) if i not in used))
    tracks += [max(tracks, default=-1) + 1, max(tracks, default=-1) + 2]
    rails, codes = address_codes(tracks)
    return tracks, rails, codes


def address_codes(tracks):
    bits = max(2, len(tracks).bit_length())
    rails = {}
    codes = []
    count = Counter()
    for track in tracks:
        serial = count[track]
        count[track] += 1
        code = 0
        for bit in range(bits):
            name = track, bit, (serial >> bit) & 1
            index = rails.setdefault(name, len(rails))
            code |= 1 << index
        codes.append(code)
    return rails, codes


class Envelope:
    def __init__(self, logical, owner):
        self.owner = owner
        self.full = (1 << logical.size) - 1
        self.arcs = [(1 << z.head, z.block) for z in logical.rows if z.owner == owner]
        initial = logical.start[owner]
        self.arcs.extend((1 << h, initial) for h in members(self.full & ~initial))

    def greatest(self, allowed):
        support = allowed
        while True:
            invalid = joined(head for head, block in self.arcs if not block & support)
            new = support & ~invalid
            if new == support:
                return support
            support = new

    def value(self, values):
        r = self.owner
        atom = 1 << r
        supports = self.greatest(self.full)
        avoid = self.greatest(self.full ^ joined(1 << j for j, value in enumerate(values)
                                                  if value == atom))
        # In the r-coordinate absorption preserves membership. In other
        # coordinates an r-fold must use only inputs outside the r-atoms.
        result = atom if any(values[j] & atom for j in members(supports)) else 0
        result |= joined(values[j] for j in members(avoid))
        assert result
        return result

    def brute_value(self, values):
        result = 0
        for support in range(1, self.full + 1):
            if all(not (head & support) or block & support for head, block in self.arcs):
                result |= fold(self.owner, [values[i] for i in members(support)])
        return result


class Target:
    def __init__(self, logical, codes):
        self.logical = logical
        self.codes = tuple(codes)
        self.size = joined(codes).bit_length()
        self.sides = tuple(Envelope(logical, r) for r in range(2))

    def helpers(self, rails):
        return tuple(fold(C, [rails[i] for i in members(code)]) for code in self.codes)

    def values(self, valuation, brute=False):
        rails, selector = valuation[:-1], valuation[-1]
        logical = self.helpers(rails)
        groups = tuple(group.value(logical) for group in self.sides)
        if brute:
            assert groups == tuple(group.brute_value(logical) for group in self.sides)
        baseline = selector | star(1, selector, groups[0]) | star(0, selector, groups[1])
        capped = all(v == 4 for v in logical)
        answer = 4 if capped else baseline
        assert (answer & 4) == (baseline & 4)
        return logical, groups, baseline, answer


def compile_qbf(quantifiers, clauses):
    """Return the addressed operation without deciding QBF or enumerating terms.

    Quantifiers A/E bind the consecutive variables starting at 1. Literals are
    signed variable indices. The result accepts bit-mask menus on the rails
    followed by the selector, for any fixed number of owners at least three.
    """
    if any(q not in 'AE' for q in quantifiers):
        raise ValueError('expected prefix letters A and E')
    clauses = tuple(tuple(clause) for clause in clauses)
    if any(type(lit) is not int or not 1 <= abs(lit) <= len(quantifiers)
           for clause in clauses for lit in clause):
        raise ValueError('literal outside the quantified prefix')
    # The rectangle construction has a nonempty clause tree and test edges.
    if not clauses:
        quantifiers, clauses = 'E', ((1,),)
    elif any(not clause for clause in clauses):
        quantifiers, clauses = 'A', ((1,),)
    logical = add_private_labels(quantified_rectangles(quantifiers, clauses))
    _, _, codes = tracks_and_codes(logical)
    return Target(logical, codes)


def full_table(target, owners=3):
    """Stream lexicographically ordered (valuation, output) pairs."""
    if owners < 3:
        raise ValueError('the reduction requires at least three owners')
    for valuation in product(range(1, 1 << owners), repeat=target.size + 1):
        yield valuation, target.values(valuation)[-1]


def source_table(target, owners=3):
    """Stream (observer, head, passive posting, bit) for every source probe."""
    if owners < 3:
        raise ValueError('the reduction requires at least three owners')
    arity = target.size + 1
    universe = (1 << owners) - 1
    for k in range(owners):
        postings = (None,) + tuple(r for r in range(owners) if r != k)
        for head in range(arity):
            for passive in product(postings, repeat=arity - 1):
                valuation = [universe ^ (1 << k) if r is None else 1 << r for r in passive]
                valuation.insert(head, 1 << k)
                yield k, head, passive, bool(target.values(valuation)[-1] & (1 << k))


def minimal(values):
    result = []
    for p in sorted(values, key=lambda v: sum(x.bit_count() for x in v)):
        if not any(all(contained(x, y) for x, y in zip(old, p)) for old in result):
            result.append(p)
    return result


def maximal(values):
    result = []
    for p in sorted(values, key=lambda v: -sum(x.bit_count() for x in v)):
        if not any(all(contained(x, y) for x, y in zip(p, old)) for old in result):
            result.append(p)
    return result


def recognize(table, n):
    """Extract probes, reconstruct each entry, then use exact canonical row cuts."""
    coeff = [{} for _ in range(n)]
    for h in range(n):
        others = [i for i in range(n) if i != h]
        for k in range(K):
            symbols = [v for v in range(K) if v != k] + [None]
            for posting in product(symbols, repeat=len(others)):
                val = [1 << k] * n
                blocks = [0] * K
                for i, r in zip(others, posting):
                    val[i] = FULL ^ (1 << k) if r is None else 1 << r
                    if r is not None:
                        blocks[r] |= 1 << i
                p = tuple(blocks)
                bit = bool(table[tuple(val)] & (1 << k))
                assert coeff[h].setdefault(p, bit) == bit
    for val, output in table.items():
        result = 0
        for h in range(n):
            for k in members(val[h]):
                p = tuple(sum(1 << i for i, menu in enumerate(val)
                              if i != h and r != k and menu == 1 << r)
                          for r in range(K))
                if coeff[h][p]:
                    result |= 1 << k
        assert result == output
    negatives = [(h, p) for h, bits in enumerate(coeff) for p in minimal(p for p in bits if not bits[p])]
    positives = [(h, p) for h, bits in enumerate(coeff) for p in maximal(p for p in bits if bits[p])]
    # Every negative is an upward-closed loss on each proper observer facet.
    for h, bits in enumerate(coeff):
        for p, bit in bits.items():
            assert bit == (not any(j == h and all(contained(x, y) for x, y in zip(q, p))
                                   for j, q in negatives))
    full_budget = (1 << len(negatives)) - 1
    by_head = [sum(1 << i for i, (j, _) in enumerate(negatives) if j == h) for h in range(n)]
    offers = {}
    for _, p in negatives:
        for r, block in enumerate(p):
            if block:
                offers[r, block] = sum(1 << i for i, (_, q) in enumerate(negatives) if contained(block, q[r]))

    def feasible(h, passive):
        @cache
        def win(budget, reg):
            indices = [r for r, block in enumerate(reg) if block]
            if not indices:
                eligible = 1 << h
            elif len(indices) == 1:
                r = indices[0]
                eligible = reg[r] & ~passive[r]
            else:
                eligible = (1 << n) - 1
                for r in indices:
                    eligible &= reg[r]
            if not eligible:
                return False
            if any(not (by_head[i] & budget) for i in members(eligible)):
                return True
            for (r, block), removed in offers.items():
                rest = budget & ~removed
                if rest == budget:
                    continue
                child = reg[:r] + (block,) + reg[r + 1:]
                if win(rest, child) and win(rest, reg):
                    return True
            return False
        outcome = win(full_budget, (0,) * K)
        win.cache_clear()
        return outcome
    return all(feasible(h, p) for h, p in positives)


def yes_term_all_labels(logical):
    # Exhaust the two-input, two-main-owner clone with syntactic support.
    assert logical.size == 2
    valuations = tuple(product(MENUS, repeat=2))
    projections = [tuple(v[i] for v in valuations) for i in (0, 1)]
    operations = {(projections[0], 1): 0, (projections[1], 2): 1}
    items = list(operations)
    for table, support in items:
        left = operations[table, support]
        for tab2, supp2 in list(items):
            right = operations[tab2, supp2]
            for r in (0, 1):
                output = tuple(star(r, x, y) for x, y in zip(table, tab2)), support | supp2
                if output not in operations:
                    operations[output] = (r, left, right)
                    items.append(output)
    valindex = {v: i for i, v in enumerate(valuations)}
    for (tab, support), t in operations.items():
        if support != 3:
            continue
        for r, initial in enumerate(logical.start):
            val = tuple(1 << r if initial & (1 << i) else FULL ^ (1 << r) for i in range(2))
            if tab[valindex[val]] != 1 << r:
                break
        else:
            if all(not (tab[valindex[tuple(4 if i == z.head else
                                            1 << z.owner if z.block & (1 << i) else 3
                                            for i in range(2))]] & 4)
                   for z in logical.rows):
                return t
    return None


def tiny(counts):
    rng = Random(1)
    for codes in [(1, 2), (3, 4)]:
        for _ in range(10):
            rows = [Row(h, r, 1 << (1 - h)) for h in range(2) for r in range(2) if rng.randrange(2)]
            logical = Logical(2, rows, (rng.randrange(1, 4), rng.randrange(1, 4)))
            yes = logical.witness(logical.full, logical.start) is not None
            allword = yes_term_all_labels(logical)
            if yes and allword is None:
                # These generic toy inputs lack the private support-padding promise.
                counts['tiny skipped, missing support promise'] += 1
                continue
            target = Target(logical, codes)
            table = {}
            for val in product(MENUS, repeat=target.size + 1):
                helpers, groups, base, out = target.values(val, brute=True)
                if allword is not None:
                    w = term_value(allword, helpers)
                    assert all(contained(w, group) for group in groups)
                    assert star(2, base, w) == out
                table[val] = out
            actual = recognize(table, target.size + 1)
            assert actual == yes, (rows, logical.start, codes, actual, yes)
            counts['tiny yes tables' if actual else 'tiny no tables'] += 1
            counts['full table entries'] += len(table)
            logical.witness.cache_clear()


def overlap(counts):
    # In one track bits 0 and 1 use rails (0) and (1,2), respectively.
    # The two first addresses share rail 0 and disagree on the second bit.
    # The third variable is on its own, one-bit track.
    codes = (3, 5, 8)
    term = (1, (0, 0, 2), (0, 1, 2))
    examples = [
        ([], (1, 2), None),
        ([Row(2, 0, 1), Row(2, 1, 2)], (5, 6), None),
        ([Row(0, 0, 4), Row(1, 0, 4)], (5, 6), term),
    ]
    for rows, start, expected_word in examples:
        logical = Logical(3, rows, start)
        assert (logical.witness(logical.full, start) is not None) == (expected_word is not None)
        target = Target(logical, codes)
        table = {}
        for val in product(MENUS, repeat=target.size + 1):
            helpers, groups, base, out = target.values(val, brute=True)
            if expected_word is not None:
                h = term_value(expected_word, helpers)
                assert all(contained(h, group) for group in groups)
                assert star(C, base, h) == out
            table[val] = out
        actual = recognize(table, target.size + 1)
        assert actual == (expected_word is not None)
        counts['overlap yes tables' if actual else 'overlap no tables'] += 1
        counts['full table entries'] += len(table)
        logical.witness.cache_clear()


def sparse_cut(logical, codes, tracks, groups, physical_size, counts):
    """Validate each local obstruction of the sparse-color shortest-word induction."""
    def post(labels):
        return joined(codes[i] for i in members(labels))
    track_masks = {g: joined(group for (t, _), group in groups.items() if t == g) for g in tracks}
    static_blocks = set(groups.values())
    visited = set()

    def visit(budget, pair):
        # At a minimal infeasible budget every chosen row has an infeasible
        # replacement branch on deletion of that one row.
        for z in list(members(budget)):
            smaller = budget & ~(1 << z)
            if logical.witness(smaller, pair) is None:
                budget = smaller
        if (budget, pair) in visited:
            return
        visited.add((budget, pair))
        live = pair[0] & pair[1]
        a, b = map(post, pair)
        raw = a & b
        selected = [logical.rows[z] for z in members(budget)]
        assert not (live & ~joined(1 << z.head for z in selected))

        # c-folds that satisfy all static rows and both vertex demands use
        # no part of a track unless they span every bit in that track.
        allowed = raw
        for g in track_masks:
            if any(not (raw & group) for (track, _), group in groups.items() if track == g):
                allowed &= ~track_masks[g]
        assert allowed == post(live)
        if raw & ~allowed:
            counts['sparse cut cells with partial-address intersections'] += 1
        dynamic_aux = [track_masks[tracks[z.head]] ^ codes[z.head] for z in selected]
        for candidate in static_blocks | set(dynamic_aux):
            if not (candidate & allowed):
                counts['sparse cut offers excluded by static rows'] += 1
                continue
            hits = [i for i in members(live) if candidate & codes[i]]
            assert len(hits) == 1
            label = hits[0]
            z = next(row for row in selected if row.head == label)
            marks, reset = codes[label], post(z.block)
            complement = track_masks[tracks[label]] ^ marks
            r, s = z.owner, 1 - z.owner
            assert not (complement & raw) and not (reset & candidate)
            tests = a, b, candidate
            for owners in (3, 4):
                full = (1 << owners) - 1
                leaves = set()
                for u in range(physical_size):
                    bit = 1 << u
                    value = 1 << s if marks & bit else 1 << r if reset & bit else 4 if complement & bit else full ^ (1 << s)
                    flags = sum(1 << k for k, block in enumerate(tests) if bit & block)
                    leaves.add((flags, value))
                assert forced_member(owners, s, frozenset(leaves))
                counts['sparse cut menu closures'] += 1
        for i in members(budget):
            z = logical.rows[i]
            smaller = budget & ~(1 << i)
            child = list(pair)
            child[z.owner] = z.block
            assert logical.witness(smaller, pair) is not None
            assert logical.witness(smaller, tuple(child)) is None
            visit(smaller, tuple(child))
        counts['sparse cut cells'] += 1
    assert logical.witness(logical.full, logical.start) is None
    visit(logical.full, logical.start)


def factored(logical, expected, counts):
    padded, word = pad(logical)
    tracks, rails, codes = tracks_and_codes(padded)
    target = Target(padded, codes)
    rng = Random(2)
    assert bool(word is not None) == expected
    if word is not None:
        assert term_support(word) == (1 << padded.size) - 1
    groups = {}
    for (g, bit, _), index in rails.items():
        groups[g, bit] = groups.get((g, bit), 0) | (1 << index)
    if word is None:
        sparse_cut(padded, codes, tracks, groups, target.size, counts)
    track_rails = {g: joined(group for (t, _), group in groups.items() if t == g) for g in tracks}
    physical = []
    for (g, bit, _), u in rails.items():
        for (t, other), block in groups.items():
            if g == t and bit != other:
                physical.append((u, {2: block}, 0, 1))
    def post(vertices):
        return joined(codes[v] for v in members(vertices))
    for z in padded.rows:
        g = tracks[z.head]
        assert all(tracks[v] != g for v in members(z.block))
        for u in members(codes[z.head]):
            physical.append((u, {z.owner: post(z.block), 2: track_rails[g] ^ codes[z.head]},
                             z.owner, 1 - z.owner))
    for u, blocks, selector_owner, observer in physical:
        val = [FULL ^ (1 << observer)] * target.size
        for r, block in blocks.items():
            for i in members(block):
                val[i] = 1 << r
        val[u] = 1 << observer
        helpers, _, _, out = target.values(val + [1 << selector_owner])
        assert not (out & (1 << observer))
        if word is not None:
            assert not (term_value(word, helpers) & (1 << observer))
        counts['padded physical probes'] += 1
    for r, initial in enumerate(padded.start):
        block = post(initial)
        val = [1 << r if block & (1 << i) else FULL ^ (1 << r) for i in range(target.size)]
        helpers, _, _, out = target.values(val + [1 << r])
        assert out == 1 << r
        if word is not None:
            assert term_value(word, helpers) == out
    for _ in range(250):
        if rng.randrange(3) == 0:
            val = [4 if rng.randrange(3) != 0 else rng.choice(MENUS) for _ in range(target.size + 1)]
        else:
            val = [rng.choice(MENUS) for _ in range(target.size + 1)]
        helpers, groups, baseline, out = target.values(val)
        if word is not None:
            h = term_value(word, helpers)
            assert all(contained(h, group) for group in groups)
            assert star(2, baseline, h) == out
            counts['padded complete identity samples'] += 1
    padded.witness.cache_clear()


def quantified_suite(counts):
    # Every nonempty one-/two-literal clause on two variables; unordered CNF
    # matrices of one or two clauses, with repetition. Tautologies included.
    literals = (-2, -1, 1, 2)
    choices = list(combinations(literals, 1)) + list(combinations(literals, 2))
    for prefix in ('AA', 'AE', 'EA', 'EE'):
        for n in (1, 2):
            for clauses in combinations_with_replacement(choices, n):
                logical = quantified_rectangles(prefix, clauses)
                expected = truth(prefix, clauses)
                actual = logical.witness(logical.full, logical.start) is not None
                assert actual == expected, (prefix, clauses, actual)
                counts['two-variable yes formulas' if actual else 'two-variable no formulas'] += 1
                logical.witness.cache_clear()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--qbf-suite', action='store_true', help='also exhaust two-variable CNFs')
    args = parser.parse_args()
    counts = Counter()
    tiny(counts)
    overlap(counts)
    for prefix, clauses in [
        ('E', ((1,),)), ('A', ((1,),)), ('E', ((1,), (-1,))),
        ('A', ((1,-1),)), ('EA', ((1,2),)), ('AE', ((1,2),)),
        ('EA', ((1,2),(-1,-2))), ('AE', ((1,2),(-1,-2))),
    ]:
        logical = quantified_rectangles(prefix, clauses)
        factored(logical, truth(prefix, clauses), counts)
    if args.qbf_suite:
        quantified_suite(counts)
    for key, val in sorted(counts.items()):
        print(f'{key}: {val}')


if __name__ == '__main__':
    main()
