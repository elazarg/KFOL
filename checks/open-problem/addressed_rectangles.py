"""Check logarithmic-arity address substitution on small two-owner row budgets.

Each winning logical cut yields a concrete term. The check substitutes the rail
folds and evaluates it on all prescribed rail probes. For an infeasible cut,
the check follows a losing reply to every main-owner offer. At each visited
cell it checks the obstruction to each auxiliary offer using closure of menu
and singleton-test signatures under all owners' gates.

Run python3 checks/open-problem/addressed_rectangles.py --random 200
"""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product
from random import Random


def members(mask):
    while mask:
        least = mask & -mask
        yield least.bit_length() - 1
        mask ^= least


def joined(masks):
    result = 0
    for mask in masks:
        result |= mask
    return result


def star(owner, x, y):
    atom = 1 << owner
    return atom if x == atom or y == atom else x | y


def contained(left, right):
    return left & right == left


@dataclass(frozen=True)
class Row:
    head: int
    owner: int
    block: int


class Logical:
    def __init__(self, size, rows, start, permanent=()):
        self.permanent = frozenset(permanent)
        self.size = size
        self.rows = tuple(rows)
        self.start = tuple(start)
        self.full = (1 << len(rows)) - 1
        self.blocks = set(start) | {row.block for row in rows}
        self.offers = {}
        for row in rows:
            owner, block = row.owner, row.block
            self.offers[owner, block] = sum(
                1 << i for i, z in enumerate(rows)
                if z.owner == owner and contained(block, z.block)
            )

    def children(self, budget, pair):
        for (owner, block), cover in self.offers.items():
            rest = budget & ~cover
            if rest == budget:
                continue
            new = list(pair)
            new[owner] = block
            yield owner, block, (rest, pair), (rest, tuple(new))

    @cache
    def witness(self, budget, pair):
        if not pair[0] & pair[1]:
            return None
        heads = joined(1 << self.rows[i].head for i in members(budget))
        free = pair[0] & pair[1] & ~heads
        if free:
            return next(members(free))
        for owner, block, decline, adopt in self.children(budget, pair):
            right = self.witness(*adopt)
            if right is None:
                continue
            left = self.witness(*decline)
            if left is not None:
                return (owner, left, right)
        return None


class Address:
    def __init__(self, logical):
        # Around each common label, every distinct incident label gets a
        # distinct track. Marks also differ in track from their posted inputs.
        self.logical = logical
        neighbors = [set() for _ in range(logical.size)]
        for label in range(logical.size):
            local = joined(block for block in logical.blocks if block & (1 << label))
            for x, y in combinations(members(local), 2):
                neighbors[x].add(y)
                neighbors[y].add(x)
        for row in logical.rows:
            for x in members(row.block):
                neighbors[x].add(row.head)
                neighbors[row.head].add(x)
        tracks = []
        for x in range(logical.size):
            occupied = {tracks[y] for y in neighbors[x] if y < x}
            tracks.append(next(g for g in range(len(occupied) + 1) if g not in occupied))
        self.tracks = tracks
        multiplicity = max(Counter(tracks).values())
        self.bits = max(2, (multiplicity - 1).bit_length())
        self.size = 2 * self.bits * (max(tracks) + 1)
        counters = Counter()
        self.codes = []
        for track in tracks:
            number = counters[track]
            counters[track] += 1
            self.codes.append(sum(1 << (2 * (track * self.bits + d) + ((number >> d) & 1))
                                  for d in range(self.bits)))
        self.static = []
        for u in range(self.size):
            track, rail = divmod(u, 2 * self.bits)
            nd = (rail // 2 + 1) % self.bits
            self.static.append((u, 3 << (2 * (track * self.bits + nd))))
        self.dynamic = []
        for row in logical.rows:
            track = self.tracks[row.head]
            complement = self.track_mask(track) ^ self.codes[row.head]
            assert not (self.post(row.block) & self.track_mask(track))
            self.dynamic.append([
                (u, row.owner, self.post(row.block), complement)
                for u in members(self.codes[row.head])
            ])

    def track_mask(self, track):
        return ((1 << (2 * self.bits)) - 1) << (2 * self.bits * track)

    def post(self, labels):
        return joined(self.codes[i] for i in members(labels))

    def spans(self, rails):
        for track in set(self.tracks):
            if all(rails & (3 << (2 * (track * self.bits + d))) for d in range(self.bits)):
                return True
        return False

    def check_incidences(self):
        for first, second in product(self.logical.blocks, repeat=2):
            raw = self.post(first) & self.post(second)
            intersection = first & second
            assert self.spans(raw) == bool(intersection)
            if intersection:
                assert raw == self.post(intersection)
            assert contained(self.post(first), self.post(second)) == contained(first, second)

    def evaluate(self, term, valuation):
        folded = []
        for address in self.codes:
            rails = iter(members(address))
            value = valuation[next(rails)]
            for index in rails:
                value = star(2, value, valuation[index])
            folded.append(value)

        @cache
        def visit(node):
            if isinstance(node, int):
                return folded[node]
            owner, left, right = node
            return star(owner, visit(left), visit(right))
        return visit(term)

    def check_witness(self, term, owners, counts):
        rows = [(u, {2: block}) for u, block in self.static]
        for copies in self.dynamic:
            rows.extend((u, {r: posted, 2: opposite}) for u, r, posted, opposite in copies)
        all_owners = (1 << owners) - 1
        for head, blocks in rows:
            for observer in range(owners):
                if observer in blocks:
                    continue
                mark = 1 << observer
                valuation = [all_owners ^ mark] * self.size
                for r, block in blocks.items():
                    for rail in members(block):
                        valuation[rail] = 1 << r
                valuation[head] = mark
                assert not (mark & self.evaluate(term, valuation))
                counts['yes negative probes'] += 1
        for r, initial in enumerate(self.logical.start):
            atom = 1 << r
            block = self.post(initial)
            valuation = [atom if block & (1 << u) else all_owners ^ atom for u in range(self.size)]
            assert self.evaluate(term, valuation) == atom
            counts['yes singleton probes'] += 1

    def check_cut(self, owners, counts):
        logical = self.logical
        seen = set()

        def visit(budget, pair):
            if (budget, pair) in seen:
                return
            seen.add((budget, pair))
            live = pair[0] & pair[1]
            raw = self.post(pair[0]) & self.post(pair[1])
            if not live:
                assert not self.spans(raw)
                counts['disjoint cells'] += 1
                return
            counts['blocked cells'] += 1
            assert raw == self.post(live)
            blocked = {}
            for index in members(budget):
                blocked[logical.rows[index].head] = index
            assert all(v in blocked for v in members(live))
            auxiliary = {block for _, block in self.static}
            auxiliary.update(self.dynamic[z][0][3] for z in members(budget))
            for candidate in auxiliary:
                if not candidate & raw:
                    counts['disjoint auxiliary offers'] += 1
                    continue
                hits = [i for i in members(live) if candidate & self.codes[i]]
                assert len(hits) == 1
                label = hits[0]
                copies = self.dynamic[blocked[label]]
                head, reset_owner, reset, opposite = copies[0]
                assert all(not contained(candidate, complement) for _, _, _, complement in copies)
                observer = 1 - reset_owner
                assert not candidate & reset
                assert not opposite & raw
                marks = self.codes[label]
                assert not (marks & (opposite | reset))
                atom = 1 << observer
                full = (1 << owners) - 1
                valuations = [atom if marks & (1 << u) else
                              1 << reset_owner if reset & (1 << u) else
                              4 if opposite & (1 << u) else full ^ atom
                              for u in range(self.size)]
                tests = self.post(pair[0]), self.post(pair[1]), candidate
                leaves = frozenset(
                    (sum(1 << r for r, block in enumerate(tests) if block & (1 << u)), valuations[u])
                    for u in range(self.size)
                )
                assert forced_member(owners, observer, leaves)
                counts['auxiliary menu closures'] += 1
            for owner, block, decline, adopt in logical.children(budget, pair):
                # Independently check that the physical full posting deletes
                # precisely the copies of the logically covered rows.
                removed = [z for z in members(budget)
                           if any(r == owner and contained(self.post(block), p)
                                  for _, r, p, _ in self.dynamic[z])]
                assert budget & ~sum(1 << z for z in removed) == decline[0]
                reply = adopt if logical.witness(*adopt) is None else decline
                assert logical.witness(*reply) is None
                visit(*reply)
        visit(logical.full, logical.start)


@cache
def forced_member(owners, observer, leaves):
    """Exact finite closure of three singleton tests and one menu column."""
    closed = set(leaves)
    queue = list(closed)
    while queue:
        flags, menu = queue.pop()
        if flags == 7 and not (menu & (1 << observer)):
            return False
        for flags2, menu2 in tuple(closed):
            common, either = flags & flags2, flags | flags2
            for owner in range(owners):
                result = (common | (either & (1 << owner)), star(owner, menu, menu2))
                if result not in closed:
                    closed.add(result)
                    queue.append(result)
    return True


def check(logical, counts):
    address = Address(logical)
    address.check_incidences()
    witness = logical.witness(logical.full, logical.start)
    if witness is None:
        for owners in (3, 4):
            address.check_cut(owners, counts)
        counts['no budgets'] += 1
    else:
        for owners in (3, 4):
            address.check_witness(witness, owners, counts)
        counts['yes budgets'] += 1
    logical.witness.cache_clear()


def quantified_rectangles(quantifiers, clauses):
    """Three-posting construction, using signed integers 1,-1,2,-2,... as literals."""
    vertices = []
    owner = []
    marks = {}
    labels = []

    def vertex(r):
        i = len(vertices)
        vertices.append(0)
        owner.append(r)
        return i

    def label(endpoints, marked=()):
        i = len(labels)
        labels.append(i)
        for v in endpoints:
            vertices[v] |= 1 << i
        for v in marked:
            assert v not in marks
            marks[v] = i
        return i

    first, second, third = vertex(0), vertex(1), vertex(0)
    label((first, second), (third,))
    a, b = second, third
    branches = {}
    for i, quantifier in enumerate(quantifiers, start=1):
        positive, negative = vertex(1 - owner[b]), vertex(1 - owner[b])
        branches[i], branches[-i] = positive, negative
        if quantifier == 'E':
            label((a, b), (positive,))
            label((a, b), (negative,))
        else:
            label((a, b), (positive, negative))
        join = vertex(owner[b])
        relay = vertex(1 - owner[b])
        label((b, positive, negative), (join,))
        label((positive, negative, join), (relay,))
        a, b = join, relay

    resources = {}
    permanent = []
    for i, clause in enumerate(clauses):
        for j, literal in enumerate(clause):
            resources[i, j] = vertex(1 - owner[branches[literal]])
    for literal, v in branches.items():
        used = [resources[i, j] for i, clause in enumerate(clauses)
                for j, lit in enumerate(clause) if lit == literal]
        if used:
            permanent.append(label([v] + used))

    def select(a, b, indices):
        if len(indices) > 1:
            first_half = len(indices) // 2
            successors = [vertex(1 - owner[b]) for _ in range(2)]
            label((a, b), successors)
            select(b, successors[0], indices[:first_half])
            select(b, successors[1], indices[first_half:])
            return
        index = indices[0]
        nxt = vertex(1 - owner[b])
        label((a, b), (nxt,))
        a, b = b, nxt
        for j in range(len(clauses[index])):
            label((a, b), (resources[index, j],))
            if j + 1 < len(clauses[index]):
                skip, relay = vertex(1 - owner[b]), vertex(owner[b])
                label((a, b), (skip,))
                label((b, skip), (relay,))
                a, b = skip, relay
    select(a, b, list(range(len(clauses))))
    rows = [Row(head, owner[v], vertices[v]) for v, head in marks.items()]
    assert all(1 <= row.block.bit_count() <= 3 and not (row.block & (1 << row.head))
               for row in rows)
    return Logical(len(labels), rows, (vertices[first], vertices[second]), permanent)


def truth(quantifiers, clauses, valuation=()):
    i = len(valuation)
    if i == len(quantifiers):
        return all(any(valuation[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in clauses)
    children = (truth(quantifiers, clauses, valuation + (bit,)) for bit in (False, True))
    return (any if quantifiers[i] == 'E' else all)(children)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--random', type=int, default=200)
    args = parser.parse_args()
    counts = Counter()
    # All two-row probes on three labels, with intersecting and
    # disjoint starts represented by all ordered singleton starts.
    options = [Row(i, owner, block) for i in range(3) for owner in range(2)
               for block in range(1, 8) if not block & (1 << i)]
    for rows in combinations(options, 2):
        for i, j in product(range(3), repeat=2):
            check(Logical(3, rows, (1 << i, 1 << j)), counts)
    for prefix, clauses in [
        ('E', ((1,),)), ('A', ((1,),)), ('E', ((1,), (-1,))),
        ('A', ((1, -1),)), ('EA', ((1, 2),)), ('AE', ((1, 2),)),
    ]:
        logical = quantified_rectangles(prefix, clauses)
        assert (logical.witness(logical.full, logical.start) is not None) == truth(prefix, clauses)
        check(logical, counts)
        counts['quantified instances'] += 1
    rng = Random(0)
    for _ in range(args.random):
        n = rng.randrange(4, 10)
        def block(allowed):
            selected = rng.sample(allowed, rng.randint(1, min(3, len(allowed))))
            return sum(1 << x for x in selected)
        start = (block(range(n)), block(range(n)))
        rows = []
        for _ in range(rng.randrange(2, 12)):
            head = rng.randrange(n)
            rows.append(Row(head, rng.randrange(2), block([j for j in range(n) if j != head])))
        check(Logical(n, rows, start), counts)
    for key, count in sorted(counts.items()):
        print(f'{key}: {count}')
    print(f'distinct signature closures: {forced_member.cache_info().currsize}')


if __name__ == '__main__':
    main()
