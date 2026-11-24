"""The quantified-formula reduction to explicit operation and source tables.

Input JSON has a quantifier prefix ("A" and "E") and clauses of signed
one-based variable numbers. Print the arity by default, or query one menu
tuple, stream the operation table, or stream all canonical source probes.
A menu is a nonzero bit mask of players; bits 0, 1, 2 are a, b, c.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path

from addressed_rectangles import Logical, Row
from explicit_table import Target, add_private_labels, address_codes, full_table, source_table


def three_cnf(prefix, clauses):
    """Split a long clause with fresh existential variables after the prefix."""
    size = len(prefix)
    fresh = size
    short = []
    for raw in clauses:
        clause = list(raw)
        start = 0
        while len(clause) - start > 3:
            fresh += 1
            short.append((clause[start], clause[start + 1], fresh))
            start += 1
            clause[start] = -fresh
        short.append(tuple(clause[start:]))
    return prefix + "E" * (fresh - size), short


def separate_slots(prefix, clauses):
    """Give positions two and three their own existential copy of each variable."""
    n = len(prefix)
    shifted = []
    for clause in clauses:
        shifted.append(tuple(lit + (n * slot if lit > 0 else -n * slot)
                             for slot, lit in enumerate(clause)))
    for var in range(1, n + 1):
        for copy in (n + var, 2*n + var):
            shifted.extend(((-var, copy), (var, -copy)))
    return prefix + "E" * (2*n), shifted


def make_rectangles(prefix, clauses, slot_width):
    """Rectangle labels of quantified_cube_cuts, with twelve ordinary tracks."""
    n, m = len(prefix), len(clauses)
    left, right = defaultdict(int), defaultdict(int)
    marks = {}
    tracks = []

    def rectangle(track, left_vertices, right_vertices, marked_vertices=()):
        bit = 1 << len(tracks)
        tracks.append(track)
        for v in left_vertices:
            left[v] |= bit
        for v in right_vertices:
            right[v] |= bit
        for v in marked_vertices:
            assert v not in marks
            marks[v] = len(tracks) - 1

    def branches(i):
        if i == 0 or i > n:
            return [('branch', i, True)]
        return [('branch', i, False), ('branch', i, True)]

    last = n + max(m, 1) - 1
    for i, quantifier in enumerate(prefix, 1):
        if quantifier == 'E':
            for sign in (False, True):
                rectangle(2*(i % 2) + sign, branches(i-1), [('relay', i-1)],
                          [('branch', i, sign)])
        else:
            # The native finite label type also includes the unused false
            # choice label at a universal stage (no incident right vertex).
            rectangle(2*(i % 2), branches(i-1), [])
            rectangle(2*(i % 2) + 1, branches(i-1), [('relay', i-1)], branches(i))
        for sign in (False, True):
            resource = ('resource', i, sign)
            rectangle(6, [('branch', i, sign)], [resource])
            lit = i if sign else -i
            rectangle(9 + (i-1)//slot_width,
                      [('clause', c) for c, clause in enumerate(clauses) if lit in clause],
                      [('relay', j) for j in range(n, last+1)], [resource])
    for i in range(1, last+1):
        rectangle(4 + i % 2, branches(i), [('relay', i-1)], [('relay', i)])
    for c in range(max(m, 1)):
        marked = []
        if c < m:
            marked.append(('clause', c))
        if c+1 < m:
            marked.extend(branches(n+c+1))
        rectangle(7 + c % 2, branches(n+c), [('relay', n+c)], marked)

    rows = [Row(mark, 0 if v[0] in {'branch','clause'} else 1,
                left[v] if v[0] in {'branch','clause'} else right[v])
            for v, mark in marks.items()]
    return Logical(len(tracks), rows, (left[branches(0)[0]], right[('relay',0)])), tracks


def compile_qbf(prefix, clauses):
    """Compile in polynomial time; the truth value is never evaluated."""
    if not isinstance(prefix, str) or any(q not in 'AE' for q in prefix):
        raise ValueError('quantifiers must be a string of A/E')
    if any(type(lit) is not int or not 1 <= abs(lit) <= len(prefix)
           for clause in clauses for lit in clause):
        raise ValueError('unbound or invalid literal')
    prefix, clauses = three_cnf(prefix, clauses)
    slot_width = len(prefix)
    prefix, clauses = separate_slots(prefix, clauses)
    logical, ordinary = make_rectangles(prefix, clauses, slot_width)
    tracks = ordinary + [12, 13]
    _, codes = address_codes(tracks)
    return Target(add_private_labels(logical), codes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('formula', type=Path)
    parser.add_argument('--owners', type=int, default=3)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--entry', nargs='+', type=int, metavar='MASK')
    mode.add_argument('--full-table', action='store_true')
    mode.add_argument('--source-table', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.formula.read_text())
    target = compile_qbf(data['quantifiers'], data['clauses'])
    n, k = target.size + 1, args.owners
    if k < 3:
        parser.error('the reduction requires at least three owners')
    if args.entry is not None:
        if len(args.entry) != n or any(not 0 < v < 1 << k for v in args.entry):
            parser.error(f'expected {n} nonempty {k}-player menu masks')
        print(target.values(args.entry)[-1])
    elif args.full_table or args.source_table:
        values = full_table(target, k) if args.full_table else source_table(target, k)
        for row in values:
            print(json.dumps(row))
    else:
        print(json.dumps({'arity': n, 'full_entries': ((1 << k)-1)**n,
                          'source_probes': n * k**n}))


if __name__ == '__main__':
    main()
