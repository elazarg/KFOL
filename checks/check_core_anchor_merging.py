#!/usr/bin/env python3
"""Finite invariant audit of all-arity owned-unit anchor merging.

The pair closures are exact, so they test every nonempty fold length in
these models. They are evidence for the separately proved theorem, not
its proof. Standard library only; no scratch imports.
"""
import argparse
import json
from pathlib import Path


def native(k):
    n, p = k, k + 1
    def add(x, y):
        return x if x == y else p if p in (x, y) else n
    values = range(k + 2)
    join = [[add(x,y) for y in values] for x in values]
    return join, [[[i if i in (x,y) else add(x,y) for y in values]
                   for x in values] for i in range(k)]


def models(data):
    for k in (2,3,4):
        yield 'D'+str(k), *native(k)
    six = json.loads((data/'core-six-models.json').read_text())
    for i, model in enumerate(six):
        yield 'core6-'+str(i), model['join'], model['operations']
    model = json.loads((data/'core-owned-unit-depth-countermodel.json').read_text())
    yield 'core24', model['join'], model['operations']


def closure(seeds, g):
    states, seen = [], set()
    for state in seeds:
        if state not in seen:
            seen.add(state); states.append(state)
    cursor = 0
    while cursor < len(states):
        p,c = states[cursor]
        for q,d in states[:cursor+1]:
            state = (g[p][q], g[c][d])
            if state not in seen:
                seen.add(state); states.append(state)
        cursor += 1
    checks = 0
    for p,c in states:
        for q,d in states:
            assert (g[p][q],g[c][d]) in seen
            checks += 1
    return states, checks


def audit(name, add, choices):
    n = len(add)
    counts = dict(unit_presentations=0, unit_states=0, unit_conclusions=0,
                  normalization_states=0, normalization_conclusions=0,
                  closure_entries=0, erasure_guards=0)
    for fi,f in enumerate(choices):
        for gi,g in enumerate(choices):
            if fi == gi:
                continue
            # Exact conditional erasure used by the human proof.
            for c in range(n):
                for P in range(n):
                    if f[c][P] != P:
                        continue
                    for z in range(n):
                        assert g[z][f[P][g[z][c]]] == g[z][P]
                        counts['erasure_guards'] += 1
            # Includes every global unit on the whole carrier, and every
            # distinguished choice-image unit needed for normalization.
            presentations = {(a,tuple(range(n))) for a in range(n)
                             if all(f[a][x] == x for x in range(n))}
            presentations.update((a,tuple(sorted(set(f[a])))) for a in range(n))
            for a, carrier in sorted(presentations):
                assert all(f[a][x] == x for x in carrier)
                assert all(g[x][y] in carrier for x in carrier for y in carrier)
                states, checked = closure(((P,c) for P in carrier for c in carrier
                                           if f[c][P] == P),g)
                counts['unit_presentations'] += 1
                counts['unit_states'] += len(states)
                counts['closure_entries'] += checked
                for P,c in states:
                    if P == a:
                        assert add[a][c] == c, (name,fi,gi,a,P,c)
                        counts['unit_conclusions'] += 1
            # For arbitrary A, this is exactly the set of (g-fold Ui,
            # g-fold f(A,Ui)) for all nonempty sequences Ui.
            for A in range(n):
                states, checked = closure(((u,f[A][u]) for u in range(n)),g)
                counts['normalization_states'] += len(states)
                counts['closure_entries'] += checked
                for first, second in states:
                    if first == A:
                        assert second == A, (name,fi,gi,A,first,second)
                        counts['normalization_conclusions'] += 1
    return counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data-dir',type=Path,default=Path(__file__).with_name('data'))
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    results = {name:audit(name,add,choices) for name,add,choices in models(args.data_dir)}
    total = {key:sum(row[key] for row in results.values()) for key in next(iter(results.values()))}
    result = dict(status='PASS', scope='finite models; exact all-length pair closures',
                  models=results, total=total)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

