"""Audit the marked-bichain induction through a configurable finite size.

Enumerate every 312-avoiding permutation and every choice of the retained
mark c. Keep precisely those recovered joins that are semilattices and
admit distribution by both choices. For each retained algebra, replay the
induction, checking actual unitization evaluation maps, absorber product
quotients, and both interval quotients at every splitting step.

The arbitrary-size proof is separate. This checker audits its finite
constructions; it does not infer general membership from a size cutoff.
Run from the repository as:
    python checks/check_core_marked_bichains.py --max-size 7
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, permutations, product

from core_basis import marker_join, marker_own
from core_two_owner_unitization import unitize


def frozen(tables):
    return tuple(tuple(tuple(row) for row in table) for table in tables)


def is_semilattice(table):
    values = range(len(table))
    return (all(table[x][x] == x for x in values)
            and all(table[x][y] == table[y][x] for x, y in product(values, repeat=2))
            and all(table[x][table[y][z]] == table[table[x][y]][z]
                    for x, y, z in product(values, repeat=3)))


def distributes(choice, join):
    return all(choice[x][join[y][z]] == join[choice[x][y]][choice[x][z]]
               for x, y, z in product(range(len(join)), repeat=3))


def recovered_join(first, second, mark):
    return tuple(tuple(first[second[x][y]][second[mark][first[x][y]]]
                       for y in range(len(first))) for x in range(len(first)))


def chain_orders(first, second):
    """Recover and independently verify the meet and join chain orders."""
    values = range(len(first))
    meet_order = sorted(values, key=lambda x: sum(first[x][y] == y for y in values))
    join_order = sorted(values, key=lambda x: sum(second[x][y] == x for y in values))
    for i, j in product(values, repeat=2):
        assert first[meet_order[i]][meet_order[j]] == meet_order[min(i, j)]
        assert second[join_order[i]][join_order[j]] == join_order[max(i, j)]
    return meet_order, join_order


def avoids_312(meet_order, join_order):
    rank = {value: i for i, value in enumerate(join_order)}
    return not any(rank[z] < rank[x] < rank[y]
                   for x, y, z in combinations(meet_order, 3))


def restrict(tables, keep, mark):
    """Closure is checked by every lookup into the new index map."""
    index = {old: new for new, old in enumerate(keep)}
    restricted = frozen([[[index[table[x][y]] for y in keep] for x in keep]
                         for table in tables])
    return restricted, index[mark]


def check_onto_homomorphism(source, target, mapping):
    assert len(mapping) == len(source[0])
    assert set(mapping) == set(range(len(target[0])))
    entries = 0
    for source_op, target_op in zip(source, target):
        for x, y in product(range(len(mapping)), repeat=2):
            assert mapping[source_op[x][y]] == target_op[mapping[x]][mapping[y]]
            entries += 1
    return entries


def interval_quotient(tables, block):
    """Collapse one block, checking all three congruence conditions."""
    values = range(len(tables[0]))
    classes = [sorted(block)] + [[x] for x in values if x not in block]
    mapping = [next(i for i, part in enumerate(classes) if x in part) for x in values]
    quotient = []
    for table in tables:
        quotient_op = []
        for left in classes:
            row = []
            for right in classes:
                outputs = {mapping[table[x][y]] for x in left for y in right}
                assert len(outputs) == 1
                row.append(outputs.pop())
            quotient_op.append(row)
        quotient.append(quotient_op)
    quotient = frozen(quotient)
    entries = check_onto_homomorphism(tables, quotient, mapping)
    return quotient, mapping, entries


def splitting_quotients(tables, meet_order, join_order):
    """Check both interval quotients and their jointly injective product map."""
    least = meet_order[0]
    position = join_order.index(least)
    before, after = set(join_order[:position]), set(join_order[position + 1:])
    cut = len(before) + 1
    assert before and after and len(after) >= 2
    assert before == set(meet_order[1:cut])
    assert after == set(meet_order[cut:])
    quotients = []
    for block in (set(meet_order[:cut]), after):
        assert len(block) >= 2
        quotient, mapping, entries = interval_quotient(tables, block)
        assert len(quotient[0]) < len(tables[0])
        quotients.append((quotient, mapping, entries))
    first_map, second_map = quotients[0][1], quotients[1][1]
    for x, y in product(range(len(tables[0])), repeat=2):
        assert (first_map[x] == first_map[y] and second_map[x] == second_map[y]) == (x == y)
    return quotients


class InductionAudit:
    def __init__(self):
        self.checked = set()
        self.counts = Counter()

    def unit_step(self, tables, mark, unit, unit_owner):
        keep = [x for x in range(len(tables[0])) if x != unit]
        smaller, smaller_mark = restrict(tables, keep, mark)
        self.check(smaller, smaller_mark)
        # Use the established executable U_f/U_g tables, without reimplementing them.
        source = unitize(smaller, unit_owner)
        mapping = keep + [tables[0][unit][x] for x in keep] + [unit]
        self.counts['unit_map_entries'] += check_onto_homomorphism(source, tables, mapping)
        self.counts['unit_reattachments'] += 1

    def absorber_step(self, tables, mark, absorber):
        keep = [x for x in range(len(tables[0])) if x != absorber]
        smaller, smaller_mark = restrict(tables, keep, mark)
        self.check(smaller, smaller_mark)
        assert all(table[absorber][x] == absorber for table in tables
                   for x in range(len(tables[0])))
        # B x {0,1}, with join in the second coordinate, and B x {1} collapsed.
        size = 2 * len(keep)
        source = frozen([[[2 * table[x // 2][y // 2] + max(x % 2, y % 2)
                           for y in range(size)] for x in range(size)] for table in smaller])
        mapping = [keep[x // 2] if x % 2 == 0 else absorber for x in range(size)]
        self.counts['absorber_map_entries'] += check_onto_homomorphism(source, tables, mapping)
        assert {x for x, image in enumerate(mapping) if image == absorber} == set(range(1, size, 2))
        self.counts['absorber_reattachments'] += 1

    def split_step(self, tables, mark, meet_order, join_order):
        for quotient, mapping, entries in splitting_quotients(tables, meet_order, join_order):
            self.counts['quotient_map_entries'] += entries
            self.check(quotient, mapping[mark])
        self.counts['splittings'] += 1

    def check(self, tables, mark):
        key = (tables, mark)
        if key in self.checked:
            return
        join, first, second = tables
        size = len(join)
        assert join == recovered_join(first, second, mark)
        assert is_semilattice(join)
        assert distributes(first, join) and distributes(second, join)
        meet_order, join_order = chain_orders(first, second)
        assert avoids_312(meet_order, join_order)
        if size == 1:
            self.counts['singleton_bases'] += 1
        elif meet_order[0] == join_order[0]:
            common_bottom = meet_order[0]
            if common_bottom == mark:
                assert join == first and distributes(second, join)
                self.counts['one_owner_bases'] += 1
            else:
                self.unit_step(tables, mark, common_bottom, unit_owner=1)
        elif meet_order[-1] == join_order[-1]:
            common_top = meet_order[-1]
            if common_top == mark:
                assert join == second and distributes(first, join)
                self.counts['one_owner_bases'] += 1
            else:
                self.unit_step(tables, mark, common_top, unit_owner=0)
        elif meet_order[0] == join_order[-1]:
            absorber = meet_order[0]
            # A retained common absorber would make join constantly equal to it.
            if absorber == mark:
                assert all(value == mark for row in join for value in row)
                assert size == 1
            self.absorber_step(tables, mark, absorber)
        else:
            self.split_step(tables, mark, meet_order, join_order)
        self.checked.add(key)
        self.counts['distinct_induction_models'] += 1


def check(max_size=7):
    # Independently verify the semilattice factor used by absorber reattachment.
    for x, y in product((2, 3), repeat=2):
        assert marker_join(2, x, y) == max(x, y)
        assert all(marker_own(2, owner, x, y) == max(x, y) for owner in (0, 1))

    # Exercise the raw interval construction even when no admissible input
    # in the finite census reaches that branch. The raw permutation 2143
    # has disjoint interval blocks {1,2}, {3,4}. Its marked recovered joins
    # are NOT assumed to be admissible; this is only a congruence-map audit.
    split_order = (1, 0, 3, 2)
    split_first = tuple(tuple(min(x, y) for y in range(4)) for x in range(4))
    split_rank = {x: i for i, x in enumerate(split_order)}
    split_second = tuple(tuple(x if split_rank[x] >= split_rank[y] else y
                               for y in range(4)) for x in range(4))
    assert avoids_312(tuple(range(4)), split_order)
    auxiliary_entries = 0
    for mark in range(4):
        tables = (recovered_join(split_first, split_second, mark), split_first, split_second)
        quotients = splitting_quotients(tables, tuple(range(4)), split_order)
        auxiliary_entries += sum(entries for _, _, entries in quotients)
    print(f'Raw splitting construction: 4 retained marks, 8 quotients, '
          f'{auxiliary_entries} homomorphism entries and 4 kernel-intersection checks.', flush=True)

    audit = InductionAudit()
    totals = Counter()
    for size in range(1, max_size + 1):
        values = range(size)
        first = tuple(tuple(min(x, y) for y in values) for x in values)
        row = Counter()
        for order in permutations(values):
            if not avoids_312(tuple(values), order):
                continue
            row['raw_bichains'] += 1
            rank = {x: i for i, x in enumerate(order)}
            second = tuple(tuple(x if rank[x] >= rank[y] else y for y in values) for x in values)
            for mark in values:
                row['marks'] += 1
                join = recovered_join(first, second, mark)
                if not is_semilattice(join):
                    continue
                row['semilattice_joins'] += 1
                if not distributes(first, join) or not distributes(second, join):
                    continue
                row['admissible_marks'] += 1
                audit.check((join, first, second), mark)
        totals.update(row)
        print(f'Size {size}: ' + ', '.join(f'{row[name]} {name}' for name in
              ('raw_bichains', 'marks', 'semilattice_joins', 'admissible_marks')) + '.', flush=True)
    print('Marked-bichain induction: ' + ', '.join(f'{value} {name}' for name, value in sorted(totals.items()))
          + '; ' + ', '.join(f'{value} {name}' for name, value in sorted(audit.counts.items()))
          + f'; {audit.counts["splittings"]} admissible splitting steps.', flush=True)
    return totals, audit.counts


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--max-size', type=int, default=7)
    args = parser.parse_args()
    assert args.max_size >= 1
    check(args.max_size)
