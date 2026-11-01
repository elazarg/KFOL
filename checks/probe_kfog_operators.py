"""Exploration: operators of the archived K-FOG manuscript, tested on winner sets.

Not part of `make check`, and nothing here is claimed in the paper. See
notes/kfog-operators.md. Git history holds the manuscript at
3ab7496^:archive/manuscript-2026-10-28.
"""
import itertools
import random
import time

# ---- games with arbitrary players and utilities -------------------------------


def outcome(tree, profile, path=()):
    if tree[0] == "l":
        return tree[1]
    return outcome(tree[2 + profile[path]], profile, path + (profile[path],))


def nodes(tree, path=()):
    if tree[0] == "l":
        return []
    return [(path, tree[1])] + nodes(tree[2], path + (0,)) + nodes(tree[3], path + (1,))


def subtree(tree, path):
    for step in path:
        tree = tree[2 + step]
    return tree


def is_spe(tree, profile, players, util, node_list):
    """Every subtree is Nash under whole-player deviations, as in Basic.lean."""
    for path, _ in node_list:
        sub = subtree(tree, path)
        inside = [(p, o) for p, o in node_list if p[: len(path)] == path]
        current = outcome(sub, {p[len(path) :]: profile[p] for p, _ in inside})
        for player in players:
            mine = [p for p, o in inside if o == player]
            base = util(player, current)
            if base == 1 or not mine:
                continue
            for choice in itertools.product((0, 1), repeat=len(mine)):
                changed = {p[len(path) :]: profile[p] for p, _ in inside}
                changed.update({p[len(path) :]: c for p, c in zip(mine, choice)})
                if util(player, outcome(sub, changed)) > base:
                    return False
    return True


def spe_outcomes(tree, players, util):
    node_list = nodes(tree)
    found = set()
    for bits in itertools.product((0, 1), repeat=len(node_list)):
        profile = {p: b for (p, _), b in zip(node_list, bits)}
        if is_spe(tree, profile, players, util, node_list):
            found.add(outcome(tree, profile))
    return frozenset(found)


def owned(upper, v, w):
    """The general rule: an owner prefers the outcomes in `upper` and is otherwise indifferent."""
    union = v | w
    return frozenset(x for x in union if x in upper) if v <= upper or w <= upper else union


def family_value(tree, upper_of):
    if tree[0] == "l":
        return frozenset({tree[1]})
    return owned(upper_of[tree[1]], family_value(tree[2], upper_of), family_value(tree[3], upper_of))


def random_tree(rng, depth, owners, leaves):
    if depth == 0 or rng.random() < 0.25:
        return ("l", rng.choice(leaves))
    return ("n", rng.choice(owners), random_tree(rng, depth - 1, owners, leaves), random_tree(rng, depth - 1, owners, leaves))


def part_general_rule():
    rng = random.Random(1)
    for k in (2, 3):
        players = list(range(k))
        outcomes = list(range(1 << k))
        upper = {r: frozenset(w for w in outcomes if w >> r & 1) for r in players}
        for _ in range(1500):
            tree = random_tree(rng, 3, players, outcomes)
            if len(nodes(tree)) > 6:
                continue
            assert spe_outcomes(tree, players, lambda p, w: w >> p & 1) == family_value(tree, upper)
    print("1. Boolean-objective leaves: the one-line rule equals brute-force SPE (K=2,3).")
    # Coalition owners with one-hot leaves, keeping the individual winner.
    for blocks in ((frozenset({0, 1}), frozenset({2})), (frozenset({0, 1}), frozenset({1, 2})), (frozenset({0, 1, 2}), frozenset({0}), frozenset({3}))):
        k = 4 if any(3 in b for b in blocks) else 3
        upper = dict(enumerate(blocks))
        for _ in range(800):
            tree = random_tree(rng, 3, list(upper), list(range(k)))
            if len(nodes(tree)) > 6:
                continue
            assert spe_outcomes(tree, list(upper), lambda b, w: int(w in upper[b])) == family_value(tree, upper)
    print("   Coalition owners keeping individual winners: same rule equals brute-force SPE.")


def part_two_player_general_sum():
    outcomes = [0, 1, 2, 3]  # none, a, b, both
    upper = {r: frozenset(w for w in outcomes if w >> r & 1) for r in (0, 1)}
    start = {frozenset({w}) for w in outcomes}
    seen, frontier = set(start), list(start)
    while frontier:
        new = set()
        for u in frontier:
            for w in list(seen):
                for r in (0, 1):
                    made = owned(upper[r], u, w)
                    if made not in seen:
                        new.add(made)
        seen |= new
        frontier = list(new)
    print(f"2. K=2 with Boolean objectives: {len(seen)} values generated, out of 15 families.")
    onehot = {frozenset({1}), frozenset({2})}
    assert all(owned(upper[r], x, y) in onehot for r in (0, 1) for x in onehot for y in onehot)
    # Not forcing: a will choose the outcome both like, yet b cannot force it.
    tree = ("n", 0, ("l", 3), ("l", 0))
    assert family_value(tree, upper) == frozenset({3})
    tree2 = ("n", 0, ("l", 3), ("l", 1))
    print("   <ab> +_a <none> has value {ab}: b surely wins but cannot force;",
          "<ab> +_a <a> has value", sorted(family_value(tree2, upper)), "(a is indifferent)")
    triples = list(itertools.product(seen, repeat=3))
    dist = sum(owned(upper[0], x, owned(upper[1], y, z)) != owned(upper[1], owned(upper[0], x, y), owned(upper[0], x, z)) for x, y, z in triples)
    abs_fail = sum(owned(upper[0], x, owned(upper[1], x, y)) != x for x, y in itertools.product(seen, repeat=2))
    print(f"   distributivity fails on {dist} of {len(triples)} triples, absorption on {abs_fail}.")
    # Who is certain to win? In this algebra that is not the same as who can force.
    def certain(v):
        return (all(w & 1 for w in v), all(w & 2 for w in v))
    groups = {}
    for v in seen:
        groups.setdefault(certain(v), []).append(sorted(v))
    print("   values by (a certain, b certain):", {k: len(g) for k, g in sorted(groups.items())})


# ---- coalition quotients -------------------------------------------------------


def partitions(k):
    def rec(i, blocks):
        if i == k:
            yield [list(b) for b in blocks]
            return
        for b in blocks:
            b.append(i)
            yield from rec(i + 1, blocks)
            b.pop()
        blocks.append([i])
        yield from rec(i + 1, blocks)
        blocks.pop()
    for blocks in rec(0, []):
        m = [0] * k
        for j, b in enumerate(blocks):
            for i in b:
                m[i] = j
        yield tuple(m), len(blocks)


def own_mask(owner_bit, s, t):
    return owner_bit if s == owner_bit or t == owner_bit else s | t


def quotient_tree_value(tree, m):
    if tree[0] == "l":
        return 1 << m[tree[1]]
    return own_mask(1 << m[tree[1]], quotient_tree_value(tree[2], m), quotient_tree_value(tree[3], m))


def can_force(tree, block):
    if tree[0] == "l":
        return tree[1] in block
    left, right = can_force(tree[2], block), can_force(tree[3], block)
    return (left or right) if tree[1] in block else (left and right)


def closure_tuples(k, parts, cap=60000, budget=240):
    t0 = time.time()
    leaves = {tuple(1 << m[i] for m, _ in parts) for i in range(k)}
    owners = [tuple(1 << m[r] for m, _ in parts) for r in range(k)]
    seen, frontier = set(leaves), list(leaves)
    while frontier:
        new = set()
        items = list(seen)
        for u in frontier:
            for w in items:
                for bit in owners:
                    made = tuple(own_mask(b, x, y) for b, x, y in zip(bit, u, w))
                    if made not in seen:
                        new.add(made)
            if time.time() - t0 > budget:
                return seen | new, False
        seen |= new
        frontier = list(new)
        if len(seen) > cap:
            return seen, False
    return seen, True


def part_coalitions():
    print("3. Coalition quotients (relabel owners and leaves by a partition of the roles):")
    d = ("n", 0, ("n", 1, ("l", 0), ("l", 2)), ("n", 1, ("l", 1), ("l", 2)))
    t = ("n", 1, ("n", 0, ("l", 0), ("l", 1)), ("l", 2))
    id3 = (0, 1, 2)
    print("   D and T, values:", bin(quotient_tree_value(d, id3)), bin(quotient_tree_value(t, id3)))
    for block in ({0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}):
        assert can_force(d, block) == can_force(t, block)
    print("   they have the same coalition forcing for every coalition, so forcing does not determine winners.")
    g1 = ("n", 0, ("l", 1), ("l", 2))
    g2 = ("n", 3, ("l", 1), ("l", 2))
    id4 = (0, 1, 2, 3)
    merge = (0, 0, 1, 2)
    assert quotient_tree_value(g1, id4) == quotient_tree_value(g2, id4)
    print("   <b>+_a<c> and <b>+_d<c>: same value", bin(quotient_tree_value(g1, id4)),
          "; after merging a with b:", bin(quotient_tree_value(g1, merge)), bin(quotient_tree_value(g2, merge)))
    rng = random.Random(5)
    for k in (3, 4, 5):
        parts = [(m, n) for m, n in partitions(k)]
        for _ in range(3000):
            tree = random_tree(rng, 5, list(range(k)), list(range(k)))
            for m, n in parts:
                v = quotient_tree_value(tree, m)
                for j in range(n):
                    block = {i for i in range(k) if m[i] == j}
                    assert (v == 1 << j) == can_force(tree, block)
    print("   in every quotient, a value is the atom {B} exactly when coalition B can force (K=3,4,5).")
    for k in (3, 4):
        parts = [(m, n) for m, n in partitions(k) if n >= 2]
        seen, complete = closure_tuples(k, parts)
        idx_id = [i for i, (m, n) in enumerate(parts) if n == k]
        idx_two = [i for i, (m, n) in enumerate(parts) if n == 2]
        idx_mid = [i for i, (m, n) in enumerate(parts) if 2 < n < k]
        project = lambda idx: {tuple(u[i] for i in idx) for u in seen}
        ids = project(idx_id)
        twos = project(idx_two)
        both = project(idx_id + idx_two)
        print(f"   K={k}: {len(parts)} partitions; closure {len(seen)}{'' if complete else ' (partial)'}; "
              f"winners only {len(ids)}; two-block only {len(twos)}; winners with two-block {len(both)}.")
        if idx_mid:
            print(f"      intermediate partitions add information: {len(seen) > len(both)}")
    print("   (two-block counts 4, 12 are the self-dual monotone functions: the forcing values.)")


# ---- coalition-owned choice ----------------------------------------------------


def star(block, s, t):
    if s & ~block == 0 or t & ~block == 0:
        return (s | t) & block
    return s | t


def part_block_choice():
    print("4. Coalition-owned choice on individual winners:")
    for k in (3, 4):
        vals = range(1, 1 << k)
        for block in range(1 << k):
            for s, t, u in itertools.product(vals, repeat=3):
                assert star(block, s, t) == star(block, t, s)
                assert star(block, star(block, s, t), u) == star(block, s, star(block, t, u))
            for s in vals:
                assert star(block, s, s) == s
    print("   every block gives a semilattice; the empty block and the full block give union.")
    print("   misere: block I-{a} is 'anyone but a'.")
    for k in (3, 4, 5):
        vals = list(range(1, 1 << k))
        points = list(itertools.product(vals, repeat=2))
        gens = [tuple(p[0] for p in points), tuple(p[1] for p in points)]
        seen, frontier = set(gens), list(gens)
        while frontier:
            new = set()
            for u in frontier:
                for w in list(seen):
                    for r in range(k):
                        made = tuple(own_mask(1 << r, x, y) for x, y in zip(u, w))
                        if made not in seen:
                            new.add(made)
            seen |= new
            frontier = list(new)
        target = {size: tuple(star((1 << size) - 1, s, t) for s, t in points) in seen for size in range(1, k)}
        print(f"   K={k}: binary terms of C: {len(seen)}; block of size n is a term: {target}")


def part_test_domains():
    print("5. How large must test inputs be, when owners are blocks? (exact, all binary terms)")

    def run(name, k, ops, budget=150):
        full = list(range(1, 1 << k))
        points = list(itertools.product(full, repeat=2))
        names = {b: "".join("abcdefg"[i] for i in range(k) if b >> i & 1) or "0" for b in ops}
        gens = {tuple(p[0] for p in points): "x", tuple(p[1] for p in points): "y"}
        seen, frontier = dict(gens), list(gens)
        t0 = time.time()
        complete = True
        while frontier and complete:
            new = {}
            items = list(seen.items())
            for u in frontier:
                for w, text in items:
                    for b in ops:
                        made = tuple(star(b, x, y) for x, y in zip(u, w))
                        if made not in seen and made not in new:
                            new[made] = f"({seen[u]} *{names[b]} {text})"
                if time.time() - t0 > budget:
                    complete = False
                    break
            seen.update(new)
            frontier = list(new)
        report = []
        witness = None
        for size in range(1, k):
            keep = [i for i, p in enumerate(points) if all(bin(v).count("1") <= size for v in p)]
            images = {}
            collisions = 0
            for u, text in seen.items():
                key = tuple(u[i] for i in keep)
                if key in images:
                    collisions += 1
                    if size == 2 and witness is None:
                        witness = (images[key], text)
                else:
                    images[key] = text
            report.append(f"<= {size} winners: {collisions}")
        status = "" if complete else " (partial)"
        print(f"   {name}, K={k}: {len(seen)} term functions{status}; undetected by inputs with {'; '.join(report)}")
        if witness:
            print(f"      passes all pair tests, yet fails: {witness[0]} = {witness[1]}")

    run("singletons", 4, [1, 2, 4, 8])
    run("partition ab|cd with union", 4, [0, 0b0011, 0b1100])
    run("partition ab|c|d with union", 4, [0, 0b0011, 0b0100, 0b1000])
    run("singletons and ab", 4, [1, 2, 4, 8, 0b0011])
    run("overlap abc,abd with union", 4, [0, 0b0111, 0b1011])
    run("all 3-sets with union", 4, [0, 0b0111, 0b1011, 0b1101, 0b1110])
    run("blocks acd,abd,abc with union", 5, [0, 0b01101, 0b01011, 0b00111])


# ---- fresh owner, serializations -----------------------------------------------


def part_fresh_owner():
    for s, t in itertools.product(range(1, 4), repeat=2):
        assert own_mask(4, s, t) == s | t
    print("6. A fresh owner who appears on no leaf gives union: at K=3, star_c on subsets of {a,b}.")


def part_serial_vs_sealed():
    """Two active roles a,b on a 2x2 round whose entries are leaves a,b,c."""
    grid = [0, 1, 2]  # probability of first action, in halves
    vals = (1, 2, 4)
    outside = 0
    missing = 0
    examples = []
    gone = []
    for m in itertools.product((0, 1, 2), repeat=4):
        table = ((m[0], m[1]), (m[2], m[3]))

        def pay(player, p, q):
            total = 0
            for i, j in itertools.product((0, 1), repeat=2):
                pi = p if i == 0 else 2 - p
                qj = q if j == 0 else 2 - q
                total += pi * qj * (table[i][j] == player)
            return total

        winners = 0
        for p, q in itertools.product(grid, repeat=2):
            if all(pay(0, p, q) >= pay(0, d, q) for d in (0, 2)) and all(pay(1, p, q) >= pay(1, p, d) for d in (0, 2)):
                for i, j in itertools.product((0, 1), repeat=2):
                    pi = p if i == 0 else 2 - p
                    qj = q if j == 0 else 2 - q
                    if pi * qj:
                        winners |= 1 << table[i][j]
        v = [[vals[x] for x in row] for row in table]
        first_a = own_mask(1, own_mask(2, v[0][0], v[0][1]), own_mask(2, v[1][0], v[1][1]))
        first_b = own_mask(2, own_mask(1, v[0][0], v[1][0]), own_mask(1, v[0][1], v[1][1]))
        serial = first_a | first_b
        if winners & ~serial:
            outside += 1
            examples.append((table, bin(winners), bin(serial)))
        if serial & ~winners:
            missing += 1
            gone.append((table, bin(winners), bin(serial)))
    print(f"7. K=3, 2x2 rounds over leaves: sealed winners outside the two serial orders in {outside} of 81; "
          f"serial winners missing from sealed in {missing}.")
    if examples:
        print("   outside, e.g.", examples[0])
    if gone:
        print("   missing, e.g. matrix", gone[0][0], "sealed", gone[0][1], "serial", gone[0][2])


# ---- products ------------------------------------------------------------------


def graft(tree, other):
    """Play `tree`, then `other`; a leaf's outcome is the union of the two outcomes."""
    if tree[0] == "l":
        return add(other, tree[1])
    return ("n", tree[1], graft(tree[2], other), graft(tree[3], other))


def add(tree, w):
    if tree[0] == "l":
        return ("l", tree[1] | w)
    return ("n", tree[1], add(tree[2], w), add(tree[3], w))


def part_products():
    print("9. Products:")
    rng = random.Random(21)
    upper = {r: frozenset(w for w in range(16) if w >> r & 1) for r in range(4)}
    for _ in range(4000):
        phi = random_tree(rng, 4, [0, 1], [1, 2])
        psi = random_tree(rng, 4, [2, 3], [4, 8])
        product = frozenset(v | w for v in family_value(phi, upper) for w in family_value(psi, upper))
        assert family_value(graft(phi, psi), upper) == product
        assert family_value(graft(psi, phi), upper) == product
    print("   disjoint roles, either order: the outcome family is the product of the two values.")
    # Cross-diagonal: physical A owns 0 in the first game and 1 in the second.
    up2 = {0: frozenset(w for w in range(4) if w & 1), 1: frozenset(w for w in range(4) if w & 2)}

    def cross(phi, psi):
        def inner(t, w1):
            if t[0] == "l":
                return ("l", (1 if w1 == 0 and t[1] == 1 else 0) | (2 if w1 == 1 and t[1] == 0 else 0))
            return ("n", 1 - t[1], inner(t[2], w1), inner(t[3], w1))

        def outer(t):
            if t[0] == "l":
                return inner(psi, t[1])
            return ("n", t[1], outer(t[2]), outer(t[3]))

        return outer(phi)

    psi = ("l", 0)
    plain = ("l", 0)
    owned_win = ("n", 0, ("l", 0), ("l", 1))
    print("   cross-diagonal with <0>: on <0> gives", sorted(family_value(cross(plain, psi), up2)),
          "; on <0>+_0<1> gives", sorted(family_value(cross(owned_win, psi), up2)),
          "(1=A, 2=B, 0=neither). Both first games have value {0}.")


# ---- admissibility -------------------------------------------------------------


def admissible_spe(tree, k):
    """SPE profiles whose restriction to each subtree is weakly undominated in that subtree."""
    node_list = nodes(tree)
    util = lambda p, w: int(w == p)
    found = set()
    undominated = {}

    def is_undominated(path, player, mine_bits):
        key = (path, player, mine_bits)
        if key in undominated:
            return undominated[key]
        sub = subtree(tree, path)
        inside = [(p[len(path):], o) for p, o in node_list if p[: len(path)] == path]
        mine = [p for p, o in inside if o == player]
        others = [p for p, o in inside if o != player]
        result = True
        for alt in itertools.product((0, 1), repeat=len(mine)):
            if alt == mine_bits:
                continue
            at_least = True
            strict = False
            for rest in itertools.product((0, 1), repeat=len(others)):
                base = dict(zip(others, rest))
                a = dict(base)
                a.update(zip(mine, alt))
                b = dict(base)
                b.update(zip(mine, mine_bits))
                ua, ub = util(player, outcome(sub, a)), util(player, outcome(sub, b))
                if ua < ub:
                    at_least = False
                    break
                if ua > ub:
                    strict = True
            if at_least and strict:
                result = False
                break
        undominated[key] = result
        return result

    players = list(range(k))
    for bits in itertools.product((0, 1), repeat=len(node_list)):
        profile = {p: b for (p, _), b in zip(node_list, bits)}
        if not is_spe(tree, profile, players, util, node_list):
            continue
        fine = True
        for path, _ in node_list:
            inside = [(p, o) for p, o in node_list if p[: len(path)] == path]
            for player in players:
                mine = tuple(profile[p] for p, o in inside if o == player)
                if mine and not is_undominated(path, player, mine):
                    fine = False
                    break
            if not fine:
                break
        if fine:
            found.add(outcome(tree, profile))
    return frozenset(found)


def admissible_rule(tree, k):
    """(winners, reachable, forcing players): the owner takes the best rank, ties by owned choice."""
    if tree[0] == "l":
        return frozenset({tree[1]}), frozenset({tree[1]}), frozenset({tree[1]})
    r = tree[1]
    s1, c1, f1 = admissible_rule(tree[2], k)
    s2, c2, f2 = admissible_rule(tree[3], k)
    rank = lambda c, f: 2 if r in f else (1 if r in c else 0)
    a, b = rank(c1, f1), rank(c2, f2)
    if a > b:
        s = s1
    elif b > a:
        s = s2
    elif s1 == frozenset({r}) or s2 == frozenset({r}):
        s = frozenset({r})
    else:
        s = s1 | s2
    forcing = frozenset(i for i in range(k) if ((i in f1 or i in f2) if i == r else (i in f1 and i in f2)))
    return s, c1 | c2, forcing


def part_admissibility():
    print("8. Admissible strategies:")
    d = ("n", 0, ("n", 1, ("l", 0), ("l", 2)), ("n", 1, ("l", 1), ("l", 2)))
    t = ("n", 1, ("n", 0, ("l", 0), ("l", 1)), ("l", 2))
    print("   D:", sorted(admissible_spe(d, 3)), "T:", sorted(admissible_spe(t, 3)), "(SPE gave D={a,b,c}, T={a,c})")
    a1 = ("n", 0, ("l", 1), ("l", 2))
    a2 = ("n", 0, ("n", 1, ("l", 0), ("l", 1)), ("l", 2))
    print("   <b>+_a<c>:", sorted(admissible_spe(a1, 3)), " (<a>+_b<b>)+_a<c>:", sorted(admissible_spe(a2, 3)),
          " while <a>+_b<b> and <b> both have value {b}, so values alone do not compose.")
    rng = random.Random(3)
    tested = empty = bad = 0
    example = None
    for _ in range(4000):
        tree = random_tree(rng, 3, [0, 1, 2], [0, 1, 2])
        if len(nodes(tree)) > 6:
            continue
        got = admissible_spe(tree, 3)
        rule = admissible_rule(tree, 3)[0]
        tested += 1
        empty += not got
        if got != rule:
            bad += 1
            example = example or (tree, sorted(got), sorted(rule))
    print(f"   rule on (winners, reachable, forcing) vs brute force: {tested} trees, {empty} empty, {bad} mismatches" + (f"; e.g. {example}" if example else ""))
    # Does the refined value distribute?
    trees = [("l", i) for i in range(3)]
    for r in range(3):
        for x, y in itertools.product(range(3), repeat=2):
            trees.append(("n", r, ("l", x), ("l", y)))
    fails = total = 0
    example = None
    sample = rng.sample(list(itertools.product(trees, repeat=3)), 3000)
    for x, y, z in sample:
        for r, s in itertools.permutations(range(3), 2):
            left = admissible_rule(("n", s, ("n", r, x, y), z), 3)[0]
            right = admissible_rule(("n", r, ("n", s, x, z), ("n", s, y, z)), 3)[0]
            total += 1
            if left != right:
                fails += 1
                example = example or (x, y, z, r, s, sorted(left), sorted(right))
    print(f"   distributing owner s over owner r: {fails} of {total} instances fail" + (f"; e.g. {example}" if example else ""))


if __name__ == "__main__":
    part_general_rule()
    part_two_player_general_sum()
    part_coalitions()
    part_block_choice()
    part_test_domains()
    part_fresh_owner()
    part_serial_vs_sealed()
    part_admissibility()
    part_products()
