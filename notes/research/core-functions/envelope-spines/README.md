# Greatest-profile siblings do not linearize core terms

This is a finite research certificate, not yet a Lean theorem. It refutes the proposed envelope-spine normal form even with unbounded owner repetitions.

Let E(phi,S) be the greatest core completion on a nonempty variable support S of an admissible full singleton-profile tuple phi. On a valuation it returns the unique prescribed singleton, if there is one, and otherwise the union of the inputs in S. A proposed envelope spine starts at a variable or at one such completion and repeatedly combines its current result with another greatest completion by an arbitrary owned choice. Owners may repeat. Also allow arbitrary finite unions, including unions between these actions.

## An explicit core counterexample

Use owners 0,1,2 and variables X,Y,Z. Set

    A = X star_2 (Z star_2 Y),
    H = Z star_1 Y,
    B = (X star_0 H) star_1 (H union Y),
    x = Y star_0 A,
    y = X star_0 B,
    F = x star_1 y.

Both A and B are themselves greatest profile completions with full support:

| Completion | owner 0 profile | owner 1 profile | owner 2 profile |
|---|---|---|---|
| A | XYZ | XYZ | X OR Y OR Z |
| B | YZ | Y OR XZ | XYZ |

The standalone checker verifies their complete 343-entry winner tables against these greatest-completion formulas. Thus the counterexample is a literal core word, with derived core union, rather than a function supplied by a search oracle.

The following five singleton-input rows suffice:

| Row | X | Y | Z | F | observation |
|---|---|---|---|---|---|
| A0 | 1 | 0 | 1 | {1} | owner 0 absent |
| A1 | 2 | 1 | 0 | {1,2} | owner 0 absent |
| A2 | 1 | 0 | 0 | {0} | owner 1 absent |
| A3 | 0 | 2 | 1 | {0,2} | owner 1 absent |
| Q | 0 | 1 | 2 | {0,1,2} | owner 2 present |

Every function in the proposed envelope-spine/union language satisfies the persistence clause

    2 in output(Q) implies
      0 in output(A0) or 0 in output(A1)
      or 1 in output(A2) or 1 in output(A3).

F violates it. Consequently no union of envelope spines bounded by F can cover its positive owner-2 observation at Q.

## A small closed certificate

There are exactly 18 normalized monotone Boolean functions on three inputs. Enumerating the admissible triples by rainbow common-source intersection, and all nonempty supports on which they depend, gives 625 greatest profile completions. Their restrictions to the five rows above give exactly 100 different five-tuples of nonempty winner masks.

The certificate is an explicit relation R of 416 five-tuples. It contains the three projection columns and all 100 envelope tuples. It is closed under:

* coordinatewise union;
* x -> x star_r E for every owner r and every one of the 100 envelope tuples E.

Every tuple in R satisfies the displayed persistence clause. In fact the only tuples satisfying all four negative observations are, in winner masks 1=owner0, 2=owner1, 4=owner2,

    (2,2,1,5,2), (2,6,1,1,1), (2,6,1,5,3).

None has owner 2 at Q. The counterexample tuple is (2,6,1,5,7).

Thus certificate soundness needs only the stated inclusions and finite closure checks, followed by induction on the proposed normal form. It does not require proving that a term enumeration or relation-generation search was exhaustive. The standalone standard-library checker regenerates the relation, then independently verifies every inclusion and closure obligation. It also enumerates all admissible full profiles and supports directly; no SAT solver, auxiliary clone data, or external package is used.

Files:

* `envelope-spine-counter-check.py`: self-contained checker (about 0.2 seconds).
The checker constructs its finite relation directly and verifies every inclusion, closure and separation condition; no external certificate file is needed.

## Direct failure of the proposed profile-extension step

The profile tuples of x and y are

    x: (Y, XYZ, Y),
    y: (X OR YZ, X(Y OR Z), XYZ).

At the atomic row (X,Y,Z)=(2,1,0), both x and y output {1,2}, while both greatest profile completions E(x),E(y) output {0,1,2}. Hence

    E(x) star_1 y != F,
    x star_1 E(y) != F,

and both enlarged outputs introduce the forbidden owner 0 at the same row.

The obstruction is simultaneous branch dependence. At (2,1,0), both children suppress the extra owner 0, but replacing either child by its greatest profile completion restores it. A description with only one recursively nonmaximal branch loses this interaction.
