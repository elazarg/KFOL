# The P4 base obstruction

Let f=ab∨ac∨bd. Its canonical D extension has no pure bichain realization.

For any pure term with Boolean function g, b/c outputs are determined by g
at the two cube corners. A marked variable essential for g on a cube forces
P: evaluate on an essential Boolean edge with that variable replaced by P,
then enlarge the other free inputs in observer-union order. The three-chain
lattice evaluation gives P on the edge, and monotonicity keeps P at its top.

Take a least-gate realization of D_f. At an OR root let g,h be the Boolean
functions of its children. They are below f. On every nonconstant f cube,
any coordinate inessential for f must be inessential for g and h; otherwise
one child gives an unwanted P, and neither child can be constantly c to mask
it because f's lower corner is 0.

Say that g owns a minterm S when g is true at its characteristic assignment.
The following four cofactor independences force ownership implications:

| Fixed coordinates | Restricted f | Inessential | Implication |
|---|---|---|---|
| b=1,d=0 | a | c | ac→ab |
| a=1,c=0 | b | d | bd→ab |
| c=1,d=0 | a | b | ab→ac |
| c=0,d=1 | b | a | ab→bd |

Each implication adds the fixed true coordinate, then deletes the
inessential coordinate. Any child owning one minterm therefore owns all
three, and hence equals f. At least one child owns a minterm. That child
itself realizes D_f: essential marked sources force every required P,
while any extra P would propagate to the root. Stable outputs are already
fixed by the Boolean function. This contradicts minimum gate count.

The Boolean dual is f*=ab∨ad∨bc, obtained by interchanging c,d in f.
Exchanging b,c in the four-valued algebra and inf,sup in the syntax fixes N,P
and turns any AND-root realization into an OR-root realization of D_f*,
which is excluded by the same argument after renaming c,d.

A leaf cannot have Boolean function f. Thus no pure term realizes D_f.
The general pure/full equivalence for canonical D extensions also excludes
full terms. The standalone checker checks the four cofactor transfers and
the dual permutation directly.
