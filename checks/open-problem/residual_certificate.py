"""Check a four-input obstruction to keeping one residual per ordered register.

A rejecting certificate may choose a subset of the remaining rows at each
node. This SAT instance asks whether the choice can depend on the register
and the order of the last adoptions. Two slots permit two different
residuals under that same key. Requires CaDiCaL on PATH or in the Lean toolchain.
"""
from functools import cache
from pathlib import Path
import shutil
import subprocess

def bitids(bits):
    while bits:
        b = bits & -bits
        yield b.bit_length()-1
        bits ^= b

class Instance:
    def __init__(self, n, rows, i, p):
        self.n, self.rows, self.i, self.p = n, tuple(rows), i, p
        self.K = len(p)
        self.root = (0,)*self.K
        self.full = (1<<len(rows))-1
        self.head = [sum(1<<j for j,(h,_) in enumerate(rows) if h==v) for v in range(n)]
        self.offers = sorted({(r,A) for _,t in rows for r,A in enumerate(t) if A})
        self.exact, self.cover = {}, {}
        for e in self.offers:
            r,A=e
            self.exact[e] = sum(1<<j for j,(_,t) in enumerate(rows) if t[r]==A)
            self.cover[e] = sum(1<<j for j,(_,t) in enumerate(rows) if t[r]&A==A)
        self.win = cache(self._win)
    def eligible(self,a):
        dom = [r for r,A in enumerate(a) if A]
        if not dom:
            return 1<<self.i
        if len(dom)==1:
            r,=dom
            return a[r]&~self.p[r]
        z = (1<<self.n)-1
        for r in dom:
            z &= a[r]
        return z
    def update(self,a,e):
        r,A = e
        return a[:r]+(A,)+a[r+1:]
    def _win(self,S,a):
        L = self.eligible(a)
        if any(not S&self.head[v] for v in bitids(L)):
            return True
        if not L:
            return False
        for e in self.offers:
            if S & self.exact[e]:
                T = S & ~self.cover[e]
                if self.win(T,a) and self.win(T,self.update(a,e)):
                    return True
        return False
    def positional(self, sat_bin, copies=1):
        # Empty-eligibility children can always use an empty residual.
        root = (self.root, ())
        def successor(state,e):
            a,order=state
            r=e[0]
            return self.update(a,e), tuple(s for s in order if s!=r)+(r,)
        reachable = {root}
        stack = [root]
        possible = {}
        while stack:
            a = stack.pop()
            rows = self.full if self.eligible(a[0]) else 0
            for r,A in enumerate(a[0]):
                if A:
                    rows &= ~self.cover[r,A]
            possible[a] = rows
            for e in self.offers:
                if rows & self.exact[e]:
                    b = successor(a,e)
                    if b not in reachable:
                        reachable.add(b)
                        stack.append(b)
        ids = {}
        def var(k):
            if k not in ids:
                ids[k] = len(ids)+1
            return ids[k]
        clauses = [[var(('use', root,0))]]
        for a in reachable:
          for slot in range(copies):
            active = var(('use',a,slot))
            zvars = {j:var(('row',a,slot,j)) for j in bitids(possible[a])}
            for v in bitids(self.eligible(a[0])):
                clauses.append([-active]+[zvars[j] for j in bitids(possible[a]&self.head[v])])
            for e in self.offers:
                hits = possible[a]&self.exact[e]
                if not hits:continue
                b = successor(a,e)
                enable = var(('enable',a,slot,e))
                for j in bitids(hits):
                    clauses.append([-zvars[j],enable])
                dests=[var(('edge',a,slot,e,d)) for d in range(copies)] if copies>1 else [enable]
                if copies>1:
                    clauses.append([-enable,*dests])
                for d,dest in enumerate(dests):
                    clauses.append([-dest,var(('use',b,d))])
                    for j in bitids(possible[b]):
                        child=var(('row',b,d,j))
                        lits=[-dest,-child]
                        if j in zvars and not self.cover[e]>>j&1:
                            lits.append(zvars[j])
                        clauses.append(lits)
        binary_input='p cnf %d %d\n'%(len(ids),len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
        r=subprocess.run([sat_bin,'-q'],input=binary_input.encode(),capture_output=True)
        if r.returncode not in (10,20):
            raise RuntimeError(r.stderr)
        ok=r.returncode==10
        return ok


def check_two_residuals(game):
    """Validate a cut directly from its rows, without using the SAT encoding."""
    def register(text):
        result = [0, 0, 0]
        for posting in text.split():
            owner = 'pqr'.index(posting[0])
            result[owner] = sum(1 << int(head) for head in posting[1:])
        return tuple(result)

    def row_mask(letters):
        return sum(1 << 'ABCDE'.index(row) for row in letters)

    # A slash gives two possible cut nodes at the same coalition assignment.
    # A child with no eligible inputs can always use an empty subfamily.
    listed = {
        '': 'ABCDE', 'p0': 'ABCD', 'p2': 'BCD', 'p13': 'BD',
        'q0': 'ABCE', 'q1': 'BCE', 'q23': 'CE', 'p0 q0': 'A',
        'p2 q23': 'CD', 'p13 q1': 'BE', 'p13 q23': 'D/E',
    }
    cuts = {register(key): tuple(map(row_mask, choices.split('/')))
            for key, choices in listed.items()}
    assert game.root in cuts
    assert max(map(len, cuts.values())) == 2
    for assignment, choices in cuts.items():
        for rows in choices:
            assert all(rows & game.head[v] for v in bitids(game.eligible(assignment)))
            for offer in game.offers:
                if rows & game.exact[offer]:
                    child = game.update(assignment, offer)
                    remaining = rows & ~game.cover[offer]
                    children = cuts.get(child, ()) if game.eligible(child) else (0,)
                    assert any(subset & ~remaining == 0 for subset in children)
    return len(cuts)


def main():
    binary = shutil.which('cadical')
    if binary is None:
        binary = str(next(Path.home().glob('.elan/toolchains/*/bin/cadical')))
    game = Instance(4, [(0, (4, 2, 0)), (1, (0, 12, 0)), (2, (10, 0, 0)),
                        (3, (0, 1, 0)), (3, (1, 0, 0))], 0, (0, 0, 0))
    assert check_two_residuals(game) == 11
    assert not game.win(game.full, game.root)
    assert not game.positional(binary, copies=1)
    assert game.positional(binary, copies=2)
    print('Five rows: one residual per ordered register fails. '
          'Directly checked a two-residual cut on 11 eligible registers.')


if __name__ == '__main__':
    main()
