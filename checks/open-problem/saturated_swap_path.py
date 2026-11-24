"""Compute the optimal number of intrinsically foreign-dependent adopted swaps.

The example is a path of m inputs with two initial endpoint demands encoded by
negative rows. Use `python3 saturated_swap_path.py --max-inputs 10`.

The solver uses the two-child row-deletion recurrence on the remaining rows.
A swap from an r-coalition to an incomparable r-coalition is charged on its
adoption branch if every eligible input of the new register still heads a row
after both of these grants:
  * saturate at the old register using the unrestricted feasibility oracle;
  * delete every remaining row with a nonempty block at r.
Thus a charged swap leaves indispensable work at another owner, even after
granting all possible same-owner coverage. The minimax cost is over all
winning strategies starting at the blank register.
"""

from argparse import ArgumentParser
from functools import cache


OWNERS = 3
BLANK = (0,) * OWNERS


def subsets(mask):
    subset = mask
    while subset:
        yield subset
        subset = (subset - 1) & mask


def insert(register, offer):
    owner, coalition = offer
    return register[:owner] + (coalition,) + register[owner + 1:]


def path_rows(size):
    def edge(index):
        return 1 << index if 0 <= index < size else 0

    vertices = [edge(j - 1) | edge(j) for j in range(size + 1)]
    rows = [(j, j % 2, vertices[j + 2]) for j in range(size - 1)]
    for endpoint in (0, 1):
        coalition = vertices[endpoint]
        rows.extend(
            (j, endpoint, coalition)
            for j in range(size) if not (edge(j) & coalition)
        )
    return rows, vertices


def check_witness(size, rows, vertices):
    """Evaluate the comb on the actual nonempty menus of the three owners."""
    def evaluate(inputs):
        value = inputs[-1]
        for j in reversed(range(size - 1)):
            atom = 1 << (j % 2)
            value = atom if atom in (inputs[j], value) else inputs[j] | value
        return value

    all_owners = (1 << OWNERS) - 1
    for head, posting_owner, block in rows:
        for observer in range(OWNERS):
            if observer == posting_owner:
                continue
            mark = 1 << observer
            inputs = [
                (1 << posting_owner) if block & (1 << j) else (all_owners ^ mark)
                for j in range(size)
            ]
            inputs[head] = mark
            assert not (evaluate(inputs) & mark), (size, head, observer, inputs)
    for observer in range(OWNERS):
        mark = 1 << observer
        inputs = [mark] + [all_owners ^ mark] * (size - 1)
        assert evaluate(inputs) & mark
    for owner in (0, 1):
        atom = 1 << owner
        inputs = [atom if vertices[owner] & (1 << j) else all_owners ^ atom
                  for j in range(size)]
        assert evaluate(inputs) == atom


def path_cost(size):
    rows, vertices = path_rows(size)
    check_witness(size, rows, vertices)

    # An offer that removes no row has an unchanged decline branch and can
    # be dropped from a strategy. Enumerate all subcoalitions of each block,
    # including those which occur in no row as a complete block.
    coverage = {}
    head_rows = [0] * size
    owner_rows = [0] * OWNERS
    for index, (head, owner, block) in enumerate(rows):
        row = 1 << index
        head_rows[head] |= row
        owner_rows[owner] |= row
        for coalition in subsets(block):
            offer = owner, coalition
            coverage[offer] = coverage.get(offer, 0) | row

    @cache
    def free(budget):
        return sum(1 << j for j, marked in enumerate(head_rows)
                   if not (marked & budget))

    @cache
    def eligible(register):
        present = [coalition for coalition in register if coalition]
        if not present:
            return 1  # the positive is input v_0
        # At a single entry the passive positive makes no postings.
        intersection = present[0]
        for coalition in present[1:]:
            intersection &= coalition
        return intersection

    @cache
    def feasible(budget, register):
        targets = eligible(register)
        if not targets:
            return False
        if targets & free(budget):
            return True
        for offer, removed in coverage.items():
            rest = budget & ~removed
            if rest != budget and feasible(rest, insert(register, offer)) and feasible(rest, register):
                return True
        return False

    @cache
    def saturate(budget, register):
        while True:
            for offer, removed in coverage.items():
                rest = budget & ~removed
                if rest != budget and feasible(rest, insert(register, offer)):
                    budget = rest
                    break
            else:
                return budget

    @cache
    def cost(budget, register):
        if eligible(register) & free(budget):
            return 0
        best = None
        parent = saturate(budget, register)
        for offer, removed in coverage.items():
            rest = budget & ~removed
            child = insert(register, offer)
            if rest == budget or not feasible(rest, register) or not feasible(rest, child):
                continue
            owner, new = offer
            old = register[owner]
            incomparable = bool((old & ~new) and (new & ~old))
            granted = parent & ~owner_rows[owner]
            charged = incomparable and not (eligible(child) & free(granted))
            value = max(cost(rest, register), int(charged) + cost(rest, child))
            best = value if best is None else min(best, value)
            if best == 0:
                return 0
        assert best is not None, (budget, register)
        return best

    full = (1 << len(rows)) - 1
    assert feasible(full, BLANK)
    result = cost(full, BLANK)
    assert result >= size - 4
    for memoized in (cost, saturate, feasible, eligible, free):
        memoized.cache_clear()
    return len(rows), result


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--max-inputs', type=int, default=10)
    args = parser.parse_args()
    for size in range(2, args.max_inputs + 1):
        row_count, rank = path_cost(size)
        print(f'{size} inputs, {row_count} rows, optimal charged-adoption depth {rank}')
