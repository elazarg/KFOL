"""Thirty-six identities and path certificates for the unrestricted one-owner basis.

Completeness is proved in appendix-owner-basis.tex. The variables and map
notations here expand to the original reset/H signature; no new operations
or constants are part of the basis.
"""

from fragments import var,reset,h
from one_owner import normal
from check_owner_presentation import equations,variables

r,a,b,c,d,u,v=map(var,range(7))
p=lambda x:reset(x,r)
J=lambda x,y:reset(p(x),p(y))
F=lambda x,y,t:h(0,r,reset(t,x),y)
G=lambda x,t:reset(reset(t,x),r)
K=lambda x,t:h(0,r,t,x)
C=lambda x,y:h(0,r,x,y)
c0=lambda x:reset(x,r)
X=p(u);Y=p(v)
BASIS = list(equations()[:6])
# Native structural laws and root-cone linearity.
BASIS += [
 ('h_sym',h(0,r,a,b),h(0,r,b,a)),
 ('h_minor',h(0,r,a,a),reset(a,r)),
 ('h_root',p(h(0,r,a,b)),h(0,r,a,b)),
 ('h_expand',h(0,p(u),a,b),reset(p(u),h(0,r,a,b))),
 ('h_split',h(0,r,reset(u,a),reset(v,b)),J(h(0,r,reset(u,a),b),h(0,r,a,reset(v,b)))),
 ('h_back',h(0,r,reset(u,a),b),h(0,r,reset(p(u),a),b)),
 ('h_reroot',p(h(0,a,u,b)),G(a,h(0,r,u,b))),
 ('h_insert',h(0,r,a,b),h(0,r,reset(r,a),b)),
 ('project_join',p(reset(reset(u,a),reset(v,a))),J(p(reset(u,a)),p(reset(v,a)))),
 ('reset_split',reset(u,reset(v,a)),reset(reset(u,a),reset(v,a))),
 ('root_preserve',p(reset(u,p(v))),reset(u,p(v))),
]
# All action laws have their argument in U_r via X=u delta r.
BASIS += [
 ('F_closed',p(F(a,b,X)),F(a,b,X)),
 ('F_join',F(a,b,J(X,Y)),J(F(a,b,X),F(a,b,Y))),
 ('F_contract',J(F(a,b,X),J(F(a,b,r),X)),J(F(a,b,r),X)),
 ('F_idem',F(a,b,F(a,b,X)),F(a,b,X)),
 ('F_band',F(a,b,F(c,d,F(a,b,X))),F(a,b,F(c,d,X))),
 ('F_Ga',F(a,b,G(a,X)),F(a,b,X)),
 ('F_Ka',F(a,b,K(a,X)),F(a,b,X)),
 ('F_Kb',F(a,b,K(b,X)),F(a,b,X)),
 ('F_ca',F(a,b,c0(a)),F(a,b,r)),
 ('F_cb',F(a,b,c0(b)),F(a,b,r)),
 ('capture',G(a,K(b,F(a,b,X))),G(a,K(b,X))),
 ('weak_gate',G(a,F(a,b,X)),G(a,K(b,X))),
 ('terminal',K(b,C(a,b)),K(b,c0(a))),
 ('terminal_bound',J(C(a,b),J(c0(a),c0(b))),J(c0(a),c0(b))),
 ('terminal_weak',J(C(a,b),K(b,c0(a))),K(b,c0(a))),
 ('G_def',G(a,X),F(a,a,X)),
 ('K_def',K(a,X),F(r,a,X)),
 ('G_root',G(r,X),X),
 ('K_root',K(r,X),X),
]


def root(term):
    if term.op == 'var':
        return term.args[0]
    return root(term.args[1])


def words(term, base):
    """Normalize t delta base into a join of action words, outermost first."""
    if term.op == 'var':
        j = term.args[0]
        return (((j, j),),)
    if term.op == 'reset':
        left, right = term.args
        k = root(right)
        return tuple(((k, k),) + word for word in words(left, base)) + words(right, base)
    first, left, right = term.args[1:]
    k, a, b = root(first), root(left), root(right)
    return (words(first, base)
            + tuple(((k, k), (a, b)) + word for word in words(left, base))
            + tuple(((k, k), (b, a)) + word for word in words(right, base)))


def word_term(word, base):
    out, rr = var(base), var(base)
    for a, b in reversed(word):
        out = h(0, rr, reset(out, var(a)), var(b))
    return out


def join_words(language, base):
    terms = [word_term(word, base) for word in language]
    out = var(base)
    for term in terms:
        out = reset(out, term)
    return out


def first_occurrences(language, base):
    """Source-free witnesses; every later guard of a source is covered by one."""
    witnesses = []
    for word in language:
        m, n, seen = {base}, {base}, {base}
        for i, (a, b) in enumerate(word):
            for source, companion in ((a, b), (b, a)):
                if source not in seen:
                    witnesses.append((source, frozenset(m), frozenset(n | {companion}),
                                      word[:i], companion))
            seen.update((a, b))
            m.add(a)
            n.update((a, b))
    return witnesses


def absorption_certificate(upper, lower, base):
    """Check every step of the written two-source induction.

    Records whether a covering witness supplies the source or the whole
    target pair. This is a check of the proof's finite combinatorics, not
    a replacement for its generic equational derivations.
    """
    available = first_occurrences(upper, base)
    steps = []
    for word in lower:
        m, n = {base}, {base}
        for a, b in word:
            supplied = []
            for source, companion in ((a, b), (b, a)):
                if source in n:
                    supplied.append(('prefix', source))
                    continue
                match = next((g for g in available if g[0] == source
                              and g[1] <= m and g[2] <= n | {source, companion}), None)
                assert match is not None, (base, word, (a, b), source, m, n)
                _, _, _, prefix, terminal = match
                assert all(source not in pair for pair in prefix)
                assert all(x in m and y in n | {companion} for x, y in prefix)
                assert terminal in n | {source, companion}
                exceptional = companion not in n and any(y == companion for _, y in prefix)
                whole_pair = exceptional or (terminal == companion and companion not in n)
                supplied.append(('pair' if whole_pair else 'source', source))
            steps.append((a, b, tuple(supplied)))
            m.add(a)
            n.update((a, b))
    return tuple(steps)
