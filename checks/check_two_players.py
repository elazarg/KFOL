"""The algebra at K=2: exact tests of the claims in the two-player appendix.

Values are bitmasks: TOP={a}=1, BOT={b}=2, MID={a,b}=3. These tables test the
written proofs and are not their proofs.
"""
from fractions import Fraction
from itertools import product
from random import Random

TOP, BOT, MID = 1, 2, 3
VALUES = (TOP, BOT, MID)
RANK = {BOT: 0, MID: 1, TOP: 2}
NEG = {TOP: BOT, BOT: TOP, MID: MID}


def own(owner, left, right):
    bit = 1 << owner
    return bit if left == bit or right == bit else left | right


def join(x, y):
    return own(0, x, y)


def meet(x, y):
    return own(1, x, y)


def reset(x, y):
    return y if y in (TOP, BOT) else x | y


def below(x, y):
    """Information order: the middle value lies below both atoms."""
    return x == y or x == MID


def check_chain():
    for x, y in product(VALUES, repeat=2):
        assert join(x, y) == max(x, y, key=RANK.get)
        assert meet(x, y) == min(x, y, key=RANK.get)
    assert NEG[TOP] == BOT and NEG[BOT] == TOP and NEG[MID] == MID
    for x, y in product(VALUES, repeat=2):
        q = lambda s: (s == TOP, s == BOT)
        assert q(join(x, y)) == (q(x)[0] or q(y)[0], q(x)[1] and q(y)[1])
        assert q(meet(x, y)) == (q(x)[0] and q(y)[0], q(x)[1] or q(y)[1])
        assert reset(x, y) == y
    for s in VALUES:
        assert bool(s & TOP) == (s != BOT) and bool(s & BOT) == (s != TOP)
    print("Two players: chain, forcing homomorphism, reset as a projection.")


def closure(arity, constants):
    points = list(product(VALUES, repeat=arity))
    start = {tuple(p[i] for p in points) for i in range(arity)}
    start |= {(c,) * len(points) for c in constants}
    seen, frontier = set(start), list(start)
    while frontier:
        new = set()
        for u in frontier:
            negated = tuple(NEG[x] for x in u)
            if negated not in seen:
                new.add(negated)
            for w in list(seen):
                for op in (join, meet):
                    made = tuple(op(x, y) for x, y in zip(u, w))
                    if made not in seen:
                        new.add(made)
        seen |= new
        frontier = list(new)
    return points, seen


def count_monotone(arity, normal):
    points = sorted(product(VALUES, repeat=arity), key=lambda p: p.count(MID))
    above = {p: [q for q in points if q != p and all(map(below, p, q))] for p in points}
    total = 0

    def extend(index, table):
        nonlocal total
        if index == len(points):
            total += 1
            return
        p = points[index]
        for c in ((TOP, BOT) if normal and MID not in p else VALUES):
            if all(below(c, table[q]) for q in above[p]):
                table[p] = c
                extend(index + 1, table)
                del table[p]

    extend(0, {})
    return total


def check_terms():
    expected = {(1, False): 6, (2, False): 84, (1, True): 11, (2, True): 197}
    for arity in (1, 2):
        for with_middle in (False, True):
            _, terms = closure(arity, (TOP, BOT, MID) if with_middle else (TOP, BOT))
            count = count_monotone(arity, not with_middle)
            assert len(terms) == count == expected[arity, with_middle]
    points, terms = closure(2, (TOP, BOT))
    assert tuple(x | y for x, y in points) not in terms
    print("Two players: term functions are the normal monotone functions "
          "(6, 84); with the middle constant, all monotone functions (11, 197).")


def random_term(rng, depth, arity):
    if depth == 0 or rng.random() < 0.2:
        return ("var", rng.randrange(arity), rng.random() < 0.5)
    op = "join" if rng.random() < 0.5 else "meet"
    return (op, random_term(rng, depth-1, arity), random_term(rng, depth-1, arity))


def evaluate(term, point):
    if term[0] == "var":
        value = point[term[1]]
        return value if term[2] else NEG[value]
    left, right = evaluate(term[1], point), evaluate(term[2], point)
    return join(left, right) if term[0] == "join" else meet(left, right)


def dnf(term):
    if term[0] == "var":
        return {frozenset({(term[1], term[2])})}
    left, right = dnf(term[1]), dnf(term[2])
    return left | right if term[0] == "join" else {x | y for x in left for y in right}


def cnf(term):
    if term[0] == "var":
        return {frozenset({(term[1], term[2])})}
    left, right = cnf(term[1]), cnf(term[2])
    return left | right if term[0] == "meet" else {x | y for x in left for y in right}


def has_pair(literals):
    return any((var, not sign) in literals for var, sign in literals)


def derivable_leq(s, t):
    return all(c & d or (has_pair(c) and has_pair(d)) for c in dnf(s) for d in cnf(t))


def check_presentation():
    rng = Random(2026)
    equal = 0
    for _ in range(40000):
        s, t = random_term(rng, 3, 3), random_term(rng, 3, 3)
        leq = all(RANK[evaluate(s, p)] <= RANK[evaluate(t, p)]
                  for p in product(VALUES, repeat=3))
        assert derivable_leq(s, t) == leq
        equal += leq
    for x in VALUES:
        assert (x == meet(x, NEG[x])) == (x != TOP)
        assert (x == join(x, NEG[x])) == (x != BOT)
        assert (meet(x, NEG[x]) == BOT) == (x != MID)
    print(f"Two players: normal-form criterion agrees with the three-element "
          f"order on 40000 pairs ({equal} inequalities); each value is needed.")


def lattice_term(rng, depth, arity):
    if depth == 0 or rng.random() < 0.25:
        return ("x", rng.randrange(arity))
    return (rng.randrange(2), lattice_term(rng, depth-1, arity), lattice_term(rng, depth-1, arity))


def lattice_value(term, point):
    if term[0] == "x":
        return point[term[1]]
    return own(term[0], lattice_value(term[1], point), lattice_value(term[2], point))


def check_reduct_and_failures():
    rng = Random(7)
    for _ in range(30000):
        s, t = lattice_term(rng, 4, 3), lattice_term(rng, 4, 3)
        atoms = all(lattice_value(s, p) == lattice_value(t, p) for p in product((TOP, BOT), repeat=3))
        full = all(lattice_value(s, p) == lattice_value(t, p) for p in product(VALUES, repeat=3))
        assert atoms == full
    assert all(join(x, BOT) == x for x in VALUES)
    points = list(product(VALUES, repeat=2))
    core = {tuple(p[0] for p in points), tuple(p[1] for p in points),
            tuple(join(*p) for p in points), tuple(meet(*p) for p in points)}
    idempotent = tuple(join(x, meet(y, NEG[y])) for x, y in points)
    assert all(join(x, meet(x, NEG[x])) == x for x in VALUES)
    assert idempotent not in core
    for p in product((TOP, BOT), repeat=2):
        assert join(*p) in (TOP, BOT) and meet(*p) in (TOP, BOT)
    print("Two players: reduct decided on the atoms; winner leaf and non-core idempotents; "
          "owned choice preserves atoms.")


def check_union_signature():
    """Signature {star_a, union}: equal iff supports agree and monotone formulas agree."""
    rng = Random(11)

    def term(depth):
        if depth == 0 or rng.random() < 0.25:
            return ("x", rng.randrange(3))
        return (rng.choice(("o", "u")), term(depth-1), term(depth-1))

    def value(t, p):
        if t[0] == "x":
            return p[t[1]]
        left, right = value(t[1], p), value(t[2], p)
        return join(left, right) if t[0] == "o" else left | right

    def formula(t, bits):
        if t[0] == "x":
            return bits[t[1]]
        left, right = formula(t[1], bits), formula(t[2], bits)
        return (left or right) if t[0] == "o" else (left and right)

    def support(t):
        return {t[1]} if t[0] == "x" else support(t[1]) | support(t[2])

    equal = 0
    for _ in range(20000):
        s, t = term(4), term(4)
        truth = all(value(s, p) == value(t, p) for p in product(VALUES, repeat=3))
        same = support(s) == support(t) and all(
            formula(s, b) == formula(t, b) for b in product((False, True), repeat=3))
        assert truth == same
        equal += truth
    print(f"Two players: support-and-formula criterion for star_a with union on "
          f"20000 pairs ({equal} equal).")


def serial(matrix):
    first_a = max((min(row, key=RANK.get) for row in matrix), key=RANK.get)
    first_b = min((max((row[j] for row in matrix), key=RANK.get)
                   for j in range(len(matrix[0]))), key=RANK.get)
    return first_a, first_b


def game_value(matrix):
    """Exact value of a 2-by-n matrix game: the row player's lower envelope."""
    top, bottom = matrix
    candidates = {Fraction(0), Fraction(1)}
    for j, k in product(range(len(top)), repeat=2):
        denominator = (top[j]-bottom[j]) - (top[k]-bottom[k])
        if denominator:
            p = (bottom[k]-bottom[j]) / denominator
            if 0 <= p <= 1:
                candidates.add(p)
    return max(min(p*top[j] + (1-p)*bottom[j] for j in range(len(top))) for p in candidates)


def check_rounds():
    def cls(x):
        return TOP if x == 1 else (BOT if x == 0 else MID)

    def rule(matrix):
        if any(all(x == TOP for x in row) for row in matrix):
            return TOP
        if any(all(row[j] == BOT for row in matrix) for j in range(len(matrix[0]))):
            return BOT
        return MID

    count = 0
    for rows, columns in ((1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3)):
        for entries in product(VALUES, repeat=rows*columns):
            matrix = [entries[i*columns:(i+1)*columns] for i in range(rows)]
            first_a, first_b = serial(matrix)
            assert rule(matrix) == first_a | first_b == meet(join(first_a, MID), first_b)
            count += 1
    pool = [Fraction(n, d) for n, d in ((0, 1), (1, 1), (1, 2), (1, 3), (2, 3), (1, 5), (9, 10))]
    games = 0
    for columns in (1, 2, 3):
        for entries in product(pool, repeat=2*columns):
            matrix = [entries[:columns], entries[columns:]]
            assert cls(game_value(matrix)) == rule([[cls(x) for x in row] for row in matrix])
            games += 1
    for x, y in product(pool, repeat=2):
        assert game_value([(x, y), (y, x)]) == (x+y)/2
        assert cls((x+y)/2) == cls(x) | cls(y)
    assert game_value([(Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))]) == Fraction(1, 2)
    print(f"Two players: sealed-round class is the union of the two serializations on "
          f"{count} class matrices; class rule agrees with exact values on {games} games.")


def check_three_role_contrast():
    def node(owner, left, right):
        return own(owner, left, right)

    a, b, c = 1, 2, 4
    first = node(0, node(1, a, c), node(1, b, c))
    second = node(1, node(0, a, b), c)
    assert first == a | b | c and second == a | c

    def force(tree, player):
        if isinstance(tree, int):
            return tree == 1 << player
        owner, left, right = tree
        results = (force(left, player), force(right, player))
        return any(results) if owner == player else all(results)

    trees = ((0, (1, a, c), (1, b, c)), (1, (0, a, b), c))
    assert all(not force(tree, player) for tree in trees for player in range(3))
    print("Three players: two games with no forcing player and different possible winners.")


if __name__ == "__main__":
    check_chain()
    check_terms()
    check_presentation()
    check_reduct_and_failures()
    check_union_signature()
    check_rounds()
    check_three_role_contrast()
