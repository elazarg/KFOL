"""Check the sharp t-slot residual construction, with t >= 2."""

from pathlib import Path
import shutil

from residual_certificate import Instance, bitids


def bits(entries):
    return sum(1 << i for i in entries)


def check(t, solver=None):
    a = range(1, t + 1)
    b = range(t + 1, 2 * t + 1)
    c = range(2 * t + 1, 3 * t + 1)
    d, h = 3 * t + 1, 3 * t + 2
    J, P, C, H = bits(a), bits([d, h]), bits(c), 1 << h
    R = [bits([b[j], c[j], d]) for j in range(t)]
    rows = [(0, (0, J, 0))]
    rows += [(a[j], (0, R[j], 0)) for j in range(t)]
    rows += [(b[j], (1 << c[j], 0, 0)) for j in range(t)]
    rows += [(v, (P, 0, 0)) for v in c]
    rows += [(d, (0, H, 0))]
    rows += [(h, (C ^ (1 << v), 0, 0)) for v in c]
    g = Instance(3 * t + 3, rows, 0, (C | P, 0, 0))
    assert all(not (posting >> head & 1) for head, row in rows for posting in row)
    table = {g.root: [g.full], (0, J, 0): [g.full ^ 1],
             (0, H, 0): [], (P, H, 0): []}
    for j in range(t):
        selector = 1 << c[j]
        B, T, D, E = (1 << i for i in [1+t+j, 1+2*t+j, 1+3*t, 2+3*t+j])
        table[0, R[j], 0] = [B | T | D | E]
        table[selector, R[j], 0] = [T | D | E]
        table[P, R[j], 0] = [D | E]
        table[0, H, 0].append(E)
        table[P, H, 0].append(E)

        # Each head requiring the next offer has exactly one source row.
        register, budget, order = g.root, g.full, ()
        for v, e in [(0, (1, J)), (a[j], (1, R[j])), (b[j], (0, selector)),
                     (c[j], (0, P)), (d, (1, H))]:
            at_head = budget & g.head[v]
            assert g.eligible(register) >> v & 1
            assert at_head.bit_count() == 1 and at_head & g.exact[e]
            budget &= ~g.cover[e]
            register = g.update(register, e)
            order = tuple(k for k in order if k != e[0]) + (e[0],)
        assert register == (P, H, 0) and order == (0, 1)
        assert g.eligible(register) == H and budget & g.head[h] == E

    # Every admitted row's posting leads to another listed subbudget.
    for register, cuts in table.items():
        for cut in cuts:
            assert all(cut & g.head[v] for v in bitids(g.eligible(register)))
            for e in g.offers:
                if cut & g.exact[e]:
                    child = g.update(register, e)
                    available = cut & ~g.cover[e]
                    if g.eligible(child):
                        assert any(s & ~available == 0 for s in table[child])
    assert max(map(len, table.values())) == t
    if solver:
        assert not g.win(g.full, g.root)
        assert not g.positional(solver, t - 1) and g.positional(solver, t)


if __name__ == '__main__':
    cadical = shutil.which('cadical') or str(next(Path.home().glob('.elan/toolchains/*/bin/cadical')))
    for t in range(2, 33):
        check(t, cadical if t <= 3 else None)
    print('Exact cut size t checked for t=2..32; independent game and SAT checks for t=2,3.')
