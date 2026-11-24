# A final single-owner phase in the offer game

Fix an initial positive query `(i,p)`, any inherited remaining row set
`S`, any register `a`, and an owner `r`. Write `L(a)` for the eligible
input set in the pointed-guard-cut theorem. Each row `(v,t)` has head
`v` and block `t_r` for owner `r`. An offer `r:A` covers the rows with
`A ⊆ t_r`.

A play restricted to `r` starts by allowing either response to every
offer at that owner. Let `U` be the intersection of all currently held
non-`r` coalitions, if any. When none is held, let `U = V ∖ p_r`.
Starting at `H = U`, remove an input `v` whenever a row `(v,t)` in
`S` has `H ∩ t_r = ∅`. The final `H*` is independent of deletion order.
The restricted game wins exactly when `H* ∩ L(a) ≠ ∅`.

To prove necessity, unfold a winning strategy using the two-child
construction of the pointed-guard-cut theorem. Every gate is at `r`,
so associativity gives one nonempty `r`-fold with leaf support `H`.
Its profile at `r` is disjunction on `H`, and its profile at every
other owner is conjunction on `H`. Therefore a foreign held coalition
contains all of `H`. If no foreign coalition is held, the required
mark or the `r`-gap precludes an `r`-singleton on `p_r`; hence
`H ⊆ V ∖ p_r`. The remaining requirement in every case is that
`H` meets `L(a)`: a supplying mark uses its head, a foreign single
gap needs a leaf outside its negative coalition, and a required
`r`-win can be supplied by any leaf in its positive coalition.
On a negative row with head in `H`, the fold retains the mark unless
some leaf lies in `t_r`. Thus every supported head meets its row blocks,
and the iterative deletion retains all of `H`.

For sufficiency, offer the `r`-block of every still-uncovered row
whose head lies in `H*`. Each such block meets `H*`. Once these offers
end every input in `H*` is free. With all offers declined there is
still an eligible one by hypothesis. Otherwise the last adopted
coalition meets `H*`, and any input in this intersection is eligible:
the foreign entries contain all of `H*`, or there are none and the
one-owner negative coalition avoids `H*`. This gives an explicit
strategy using whole blocks of remaining rows. The fixed point takes
at most `n` strict deletions and polynomial time in the input table.

For a bounded mixed-owner test, delete declined offers from each
root-to-terminal play and count changes of owner in the remaining
sequence. The first adoption is free. A decline always preserves the
budget and last adopted owner; adoption changes the last owner and
charges one exactly when it differs. With last owner `r` and zero
budget, this is the restricted game above. At a blank root, zero budget
allows arbitrary offers on the all-decline spine, each adoption branch
being checked by the corresponding single-owner fixed point. Testing
one such proposal is polynomial and each productive proposal covers a
remaining row, so this entire depth-zero recognition test is polynomial.

The bounded values are monotone under deleting rows at a fixed register,
last owner, and depth budget. Ignore an offer with no effect from a
smaller starting budget by taking its decline subtree. Thus a fixed
proposal whose adoption succeeds can be accepted into the all-decline
history greedily: any previously available winning continuation still
succeeds after that deletion. The bounded solver in `phase.py` uses
this rule; a second recursion tests both replies directly.

The original row-block alphabet suffices for this metric. Replace an
arbitrary productive `r:A` with a batch offering each as-yet-uncovered
`r`-block containing `A`. The batch deletes exactly the same rows.
All declines preserve the original register. After any adoptions, the
last register holds a superset of `A`; the remaining continuation can
be replayed by monotonicity of eligibility under enlarging a nonblank
entry. The number of owner changes between adoptions is unaffected.

The scalar depth-zero test grants no general polynomial time bound for
constant positive depth: a free same-owner adoption can change the
register used by later foreign tests, and these tests inherit all earlier
deletions. Their histories need not coincide.
