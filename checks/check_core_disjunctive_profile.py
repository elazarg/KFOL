#!/usr/bin/env python3
"""Finite invariant audit of two-choice disjunctive profile polarity.

The value/Boolean-profile closures are exact, so they test every source
arity and depth in these models. They are evidence for the separately proved theorem, not
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


def audit(name, add, choices):
    n=len(add)
    counts=dict(domains=0, domain_members=0, ideal_instances=0,
                join_choice_instances=0, profile_states=0,
                profile_entries=0, profile_conclusions=0)
    for fi,f in enumerate(choices):
        for gi,g in enumerate(choices):
            if fi==gi:
                continue
            for M in range(n):
                E={c for c in range(n) if f[M][g[M][c]]==g[M][c]}
                counts['domains']+=1
                counts['domain_members']+=len(E)
                for c in range(n):
                    intrinsic=(add[c][f[M][c]]==f[M][c]
                               and add[M][g[M][c]]==g[M][c])
                    assert (c in E)==intrinsic
                for c in E:
                    for e in range(n):
                        assert f[c][e] in E
                        counts['ideal_instances']+=1
                    for d in E:
                        assert add[c][d] in E and g[c][d] in E
                        counts['join_choice_instances']+=2
                # All qualifying variable values occur, including M itself;
                # their g-fold is exactly M. Other variables may take any
                # value independently. (value,bit) tracks the exact Boolean
                # profile at qualifying variables0 / other variables1.
                states=[]; seen=set()
                def insert(q):
                    if q not in seen:
                        seen.add(q); states.append(q)
                for c in range(n):
                    if g[M][c]==M:
                        insert((c,0))
                    insert((c,1))
                cursor=0
                tables=((add,False),(f,True),(g,False))
                while cursor<len(states):
                    c,bc=states[cursor]
                    for d,bd in states[:cursor+1]:
                        for h,selected in tables:
                            insert((h[c][d],bc & bd if selected else bc | bd))
                    cursor+=1
                counts['profile_states']+=len(states)
                for c,bc in states:
                    if bc==0:
                        assert c in E and add[c][f[M][c]]==f[M][c]
                        counts['profile_conclusions']+=1
                    for d,bd in states:
                        for h,selected in tables:
                            assert (h[c][d],bc & bd if selected else bc | bd) in seen
                            counts['profile_entries']+=1
    return counts

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data-dir',type=Path,default=Path(__file__).with_name('data'))
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    results = {name:audit(name,add,choices) for name,add,choices in models(args.data_dir)}
    total = {key:sum(row[key] for row in results.values()) for key in next(iter(results.values()))}
    result = dict(status='PASS', scope='finite models; exact all-depth two-choice profile closures',
                  models=results, total=total)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

