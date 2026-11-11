"""Shared finite research machinery for the five-input, three-owner examples.

Only the standard library is used. Full functions have 1,215 source observations;
actual term tables and sampled subpowers provide independent checks.
"""
from collections import deque
NV = 5
OWNERS = range(3)
VALUES = range(1, 8)
PAT = 3 ** (NV - 1)
NBITS = 3 * NV * PAT


def choice(owner: int, left: int, right: int) -> int:
    atom = 1 << owner
    return atom if left == atom or right == atom else left | right


def term_value(term, values) -> int:
    if isinstance(term, int):
        assert 0 <= term < NV
        return values[term]
    owner, left, right = term
    assert owner in range(4)
    a, b = term_value(left, values), term_value(right, values)
    return a | b if owner == 3 else choice(owner, a, b)


def patch_value(components, values) -> int:
    result = 0
    for term in components:
        result |= term_value(term, values)
    return result


def observations():
    result = []
    for k in OWNERS:
        others = [r for r in OWNERS if r != k]
        for source in range(NV):
            for pattern in range(PAT):
                p, row = pattern, [0] * NV
                row[source] = 1 << k
                for j in range(NV):
                    if j != source:
                        digit, p = p % 3, p // 3
                        row[j] = 1 << others[digit] if digit < 2 else 7 ^ (1 << k)
                result.append((k, source, tuple(row)))
    return result


OBS = observations()


def coefficient_queries(values):
    """The source-decomposition queries for all three output memberships."""
    result = [0, 0, 0]
    for k in OWNERS:
        others = [r for r in OWNERS if r != k]
        for source in range(NV):
            if not values[source] & (1 << k):
                continue
            pattern, place = 0, 1
            for j in range(NV):
                if j != source:
                    digit = next((d for d, r in enumerate(others)
                                  if values[j] == 1 << r), 2)
                    pattern += place * digit
                    place *= 3
            result[k] |= 1 << (k * NV * PAT + source * PAT + pattern)
    return result


def coefficients(table, row_index):
    return sum(1 << q for q, (k, _, row) in enumerate(OBS)
               if table[row_index[row]] & (1 << k))


def packed(values):
    return sum(value << (3 * i) for i, value in enumerate(values))


def packed_choice(owner, a, b, low):
    """Coordinatewise choice, independently of the coefficient recurrence."""
    aa, bb = (a >> owner) & low, (b >> owner) & low
    for s in OWNERS:
        if s != owner:
            aa &= ~(a >> s)
            bb &= ~(b >> s)
    mask = (aa | bb) & low
    return ((a | b) & ~(mask | mask << 1 | mask << 2)) | mask << owner


class FullFiberClosure:
    """Exact greatest full functions in each attainable sampled-row fiber.

    A fiber carries the union of its functions. Owned choice distributes over
    union in each argument, so pairwise products and unions within a fiber
    compute its greatest function. Starting from projections and iterating to
    a fixed point is exhaustive by induction on terms. There are finitely many
    fibers and NBITS coefficient bits, so the worklist terminates.
    """
    def __init__(self):
        self.kills = [[0] * (1 << NV) for _ in OWNERS]
        self.cache = [{} for _ in OWNERS]
        for q, (k, source, row) in enumerate(OBS):
            for owner in OWNERS:
                if owner == k:
                    continue
                coalition = sum(1 << j for j, value in enumerate(row)
                                if j != source and value == 1 << owner)
                self.kills[owner][coalition] |= 1 << q
        self.projections = []
        for source in range(NV):
            bits = sum(1 << q for q, (_, j, _) in enumerate(OBS) if j == source)
            profile = sum(1 << coalition for coalition in range(1 << NV)
                          if coalition & (1 << source))
            self.projections.append((bits, (profile, profile, profile)))

    def kill(self, owner, profile):
        if profile not in self.cache[owner]:
            bits, todo = 0, profile
            while todo:
                lowest = todo & -todo
                bits |= self.kills[owner][lowest.bit_length() - 1]
                todo ^= lowest
            self.cache[owner][profile] = bits
        return self.cache[owner][profile]

    def compose(self, owner, a, b):
        bits_a, profiles_a = a
        bits_b, profiles_b = b
        bits = (bits_a | bits_b) & ~self.kill(
            owner, profiles_a[owner] | profiles_b[owner])
        profiles = tuple((profiles_a[r] | profiles_b[r]) if r == owner
                         else (profiles_a[r] & profiles_b[r]) for r in OWNERS)
        return bits, profiles

    def maximum(self, omitted, critical, negative):
        indices = [i for i in range(len(critical)) if i != omitted]
        rows = [critical[i] for i in indices]
        m = len(rows)
        low = sum(1 << (3 * i) for i in range(m))
        states, fibers, todo, pending = [], {}, deque(), set()
        updates = 0

        def add(state, function):
            nonlocal updates
            bits, profile = function
            if state not in fibers:
                states.append(state)
                fibers[state] = function
            else:
                old_bits, old_profile = fibers[state]
                if bits & ~old_bits == 0:
                    return
                fibers[state] = (bits | old_bits,
                    tuple(a & b for a, b in zip(profile, old_profile)))
            updates += 1
            if state not in pending:
                todo.append(state)
                pending.add(state)

        for j, function in enumerate(self.projections):
            add(packed(row[j] for row in rows), function)
        while todo:
            state_a = todo.popleft()
            pending.remove(state_a)
            function_a = fibers[state_a]
            for state_b in states:
                function_b = fibers[state_b]
                for owner in OWNERS:
                    add(packed_choice(owner, state_a, state_b, low),
                        self.compose(owner, function_a, function_b))
        # Independently check the terminal closure, rather than trusting the queue.
        for state_a in states:
            for state_b in states:
                for owner in OWNERS:
                    state = packed_choice(owner, state_a, state_b, low)
                    bits, _ = self.compose(owner, fibers[state_a], fibers[state_b])
                    assert bits & ~fibers[state][0] == 0
        forbidden = sum(1 << (3 * j + OBS[negative[i]][0])
                        for j, i in enumerate(indices))
        result = 0
        for state, (bits, _) in fibers.items():
            if not state & forbidden:
                result |= bits
        assert result
        return result, len(states), updates



def subpower_closure(rows):
    """Unpruned closure; process each unordered pair exactly once.

    Every pair is processed when its later-created member reaches the worklist
    head. Newly generated tuples are appended. At termination this checks all
    owned products, independently of source coefficients or singleton profiles.
    """
    m = len(rows)
    spread = [sum(1 << (3 * i) for i in range(m) if mask >> i & 1)
              for mask in range(1 << m)]
    cleared = [~(a | a << 1 | a << 2) for a in spread]
    owner_bits = [[a << r for a in spread] for r in OWNERS]
    states, atoms, known = [], [], set()

    def add(state):
        if state in known:
            return
        known.add(state)
        states.append(state)
        masks = [0, 0, 0]
        for i in range(m):
            value = state >> (3 * i) & 7
            if value in (1, 2, 4):
                masks[value.bit_length() - 1] |= 1 << i
        atoms.append(tuple(masks))

    for j in range(NV):
        add(packed(row[j] for row in rows))
    head = 0
    while head < len(states):
        a, aa = states[head], atoms[head]
        for tail in range(head + 1):
            b, bb = states[tail], atoms[tail]
            union = a | b
            for r in OWNERS:
                mask = aa[r] | bb[r]
                add((union & cleared[mask]) | owner_bits[r][mask])
        head += 1
    return states
