# Atomic agreement and all ghost residuals do not glue

This four-input operation is a counterexample to the proposed criterion

> admissible singleton profiles + core ghost residuals + one common core
> realizer on all atomic inputs imply a global core realization.

It also satisfies passive guard monotonicity, whole-input provenance, and full
omission independence. These are research results, not Lean/report claims.

Use exactly three owners `b=0`, `c=1`, `a=2`. Write `⋆r` for owner `r`'s choice,
`N={b,c}`, and use capital `A,B,C,D` for the four input menus. Put

```
H = ((D ⋆1 A) ⋆0 B) ⋆1 ((C ⋆1 B) ⋆0 A).
```

Define `F=H` except on these two regions, where `F=N`:

```
A=N, a∈B, C={c}, D={b};
B=N, a∈A, C={b}, D={c}.
```

There are exactly eight modified valuations. In each, `H={a,b,c}`. Neither
region contains an atomic valuation, so **the single displayed term H realizes
F on every atomic input**, including rows with several occurrences of one
owner.

The complete singleton profiles are those of `H`. For
`φ(x)=x_A x_B ∨ x_A x_C ∨ x_B x_D`, they are

```
Φ_b(E) = ¬φ(V\E),    Φ_c(E) = φ(E),    Φ_a(E) = [E=V].
```

Thus the profiles are admissible. The checker verifies the singleton
characterization on all 2,401 winner-valued inputs, not only on atoms.

For a deleted coordinate `j`, define the ghost residual winnerwise:

```
k∈δ_j F(v)  iff  k∈F(v[j := {b,c,a}\{k}]).
```

In each term below, `x,y,z` denote the three remaining inputs in their original
order. The four residuals have these **explicit core witnesses**:

```
δ_A F = (z ⋆0 x) ∪ (y ⋆1 x),
δ_B F = (z ⋆1 x) ∪ (y ⋆0 x),
δ_C F = ((z ⋆1 x) ⋆0 y) ⋆1 ((y ⋆0 x) ⋆2 x),
δ_D F = ((z ⋆0 x) ⋆1 y) ⋆0 ((y ⋆1 x) ⋆2 x).
```

Union is core-definable with three owners. The checker also supplies explicit
witnesses for all six two-coordinate residuals. Every three-coordinate
residual is the remaining projection; deleting all four gives zero. Hence
checking all proper iterated residuals does not repair the criterion.

Observe owner `a`: menus containing `a` map to `P`, the atoms `{b},{c}` map
to `b,c`, and `N` maps to `N`. The resulting operation is the canonical
essential-source extension `D_φ`. The checker verifies this identity on all
full inputs. The seven-row argument below proves that **F is not core**.

Run the independent standard-library checker:

```
python3 notes/research/core-functions/face-gluing/check.py
```

[certificate.json](certificate.json) contains all four residual terms, `H`,
the 324 canonical source-guard bits, the full 2,401-entry table, and the profile
truth tables. The checker derives every entry from the two-region definition,
then verifies the witnesses and structural laws. It has no `/tmp` dependencies.

The guard formula uses the usual canonical probe: mark source `j` with `{r}`;
assign each other input either a rival-owner atom or the neutral complement
of `r`. Record whether the output contains `r`. At an arbitrary valuation,
`r` is present exactly when some input containing `r` has a positive guard at
the corresponding rival-atom/neutral passive pattern. All 648 atom-to-neutral
monotonicity edges pass. Thus the failure is compatibility between the jointly
realizable atomic boundary and jointly realizable neutral faces, rather than
missing source additivity or separate-owner amalgamation on the atomic rows.

The obstruction uses only **seven rows**: E=(c,c,b,b), followed by

```
(N,c,P,b), (c,N,b,P), (N,P,c,b),
(P,N,b,c), (N,b,c,P), (b,N,P,c).
```

For any full bichain term, absence of P at the last six rows forces all seven
outputs to be equal in {b,c,N}. F gives c at E and N at the other six.
The analytic proof and row matrix are in [noncore.md](noncore.md).
[seven-relation.json](seven-relation.json) independently certifies the pure
part using 231 states: the checker verifies the variable columns, both
lattice-operation closures, and that only the two constant endpoint tuples
omit P on the last six rows. Observer-union expansion gives the full law.
