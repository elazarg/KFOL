# Read-once upper bounds, extension rigidity, and a sharp completion failure

Mathematical research, without Lean claims. Pure-owner source probes give
an upper-bound theorem complementary to the positive-profile lower bound.
Together with free profile persistence, they determine the unique
term-induced free extension of a primitive read-once operation. They also
exclude the greatest monotone observer-face
completion as a general solution, sharply at arity 2K in this regime.

Fix a finite owner set I of size K>=3. Words use variables and I-owned
choices only. An ambient extension may add arbitrary unowned roles, but
introduces no gates owned by those roles. Let T be a primitive read-once
word with finite nonempty support V.

## Pure-owner probes bound every occurrence

For an occurrence o of variable j in a word S and an old owner r, let

    B_(o,r)(E)=AND over r-owned ancestors of o
                  NOT Phi_(sibling,r)(E),

where E is a subset of V\{j}. At this source observation, j is not the
r singleton, even if other j occurrences appear in a sibling. This is
the full factor type from [source-type-pruning.md](source-type-pruning.md).
In particular B_(o,r)(empty)=true. It records the absence of any absorbing
r-singleton sibling on the marked path.

At observer k, an occurrence supplies k when its input contains k and
all factors B_(o,r)(E_r) with r!=k hold. A source coefficient is the OR
over the occurrences carrying that source label. In T, variable j has
one occurrence; write its factor B_(j,r)^T.

**Upper-bound theorem.** If S(w) subseteq T(w) on the old winner algebra
A_I, then, for every occurrence o of j in S and every old owner r,

    B_(o,r)^S(E) implies B_(j,r)^T(E).                     (1)

Choose k!=r. Give j the menu {k}, every position in E the menu {r}, and
every other position the ambiguous menu N_k=I\{k}. Only j contains k.
The only rival singleton inputs have owner r, so the source coefficients
at this probe are respectively

    OR_(o labeled j) B_(o,r)^S(E),     B_(j,r)^T(E).

All other rival-owner factors have empty atomic input sets and equal true.
Operation inclusion therefore implies inclusion of these two bits, proving
(1) for each occurrence separately. Ambiguity of N_k is where K>=3 is used.

It follows that S's independent-status free source coefficients are below
T's: compare each factor in every occurrence product using (1), then take
the OR. This holds even when independent owner flags are incompatible
with an actual winner valuation. In particular,

    S_J(w) subseteq T_J(w)                                (2)

on every ambient role set J containing I. The same occurrence-path formula
applies there; a fresh observer includes every old-owner factor, while an
old observer omits only its own factor.

## Minimality and uniqueness of ambient extensions

**Minimality.** No core operation is strictly below a primitive read-once
operation in the pointwise inclusion order.

Indeed S subseteq T retains every positive singleton-profile bit of T:
at a probe where T={r}, S is a nonempty subset of {r} and hence equals
{r}. The [read-once profile lower bound](read-once-profile-minimum.md)
then gives T subseteq S. Thus S=T on A_I.

**Extension rigidity.** If S=T on A_I, then S=T on every ambient role
extension in the fixed I-owned signature, at every finite input arity.

The upper inclusion follows from (2). For the reverse first adjoin just
one fresh role omega. Equality on A_I gives equality of all old singleton
profiles. The variable supports also agree: every variable of T is essential,
and every occurring variable of a core word is essential when K>=3. Both
omega-profiles are therefore conjunction of all variables in V, since no
gate is owned by omega. The read-once lower-bound theorem on the finite
owner set I union {omega} now gives T subseteq S.

Consequently their operations on B_I agree, by the coarse omega-observer
quotient from [unowned-observer.md](unowned-observer.md). This also proves
equality on arbitrary, even infinite, J: every old membership bit factors
through an old omitted-atom observer face, and every fresh membership bit
through B_I. This step avoids assuming an infinite-owner version of the
finite profile theorem.

In particular, the greatest term-induced free independent-status extension
of the old operation F=T is exactly the free extension of T itself. Every
other realizer's occurrence factors lie below T's by (1), and T attains
the bound. The canonical cotree in
[read-once-recognition.md](read-once-recognition.md) computes it without
choosing among occurrence realizations. This is an exact result for the
read-once regime, not a classification of extensions of arbitrary core F.

In fact this is the only term-induced free extension. The
[exact read-once free certificate](free-profile-persistence.md) gives the
opposite inequality: every word retaining T's positive profile bits has
free coefficients at least T's, even at overlapping independent flags.
Every realizer of F=T retains those bits. Combined with (1), the two
inequalities give equality at every free source observation. Thus ordinary
ambient extension rigidity strengthens to full independent-status rigidity.

## The greatest monotone face completion

Order B_I by flat union: each old atom is below N, which is below P.
Let U subseteq B_I^V be the union of the omitted-atom faces: a tuple is
in U exactly when at least one old atom does not occur in it. The original
operation F=T on A_I determines the restriction g=T_B|U.

Define the greatest monotone completion of this face data by

    M(v)=MEET {g(w): w in U and v<=w}.                     (3)

The set is nonempty because the all-P tuple is in U. It has a lower bound
T_B(v). Every nonempty lower-bounded subset of the flat order has a meet:
if it contains an atom, that unique atom is the meet; otherwise N is the
meet if present, and P otherwise. Thus (3) is well-defined.

The map M is monotone because increasing v removes upper constraints.
It agrees with g on U: the constraint w=v gives the upper bound g(v),
while monotonicity of T_B gives the reverse bound. Every monotone extension
of g lies below M, and T_B lies below M.

Moreover M has precisely T_B's singleton profiles. If T_B(v)=r, erase
all atoms of any owner s!=r by increasing them to N. The resulting tuple
is in U and has exactly the same r-singleton input positions, hence still
has output r. It is an upper constraint witnessing M(v)=r. Conversely,
T_B(v)<=M(v) prevents a nonatom from becoming an atom.

## Sharp agreement below arity 2K

**Theorem.** For a primitive read-once T on fewer than 2K inputs,
M=T_B. At 2K inputs this can fail, and the completion need not be term-induced.

The maps can differ only at a tuple v outside U with T_B(v)=N and
M(v)=P: atom profiles already agree, and P is maximal. Such a v contains
all K old atoms. For each r let w_r increase every r-atom position of
v to N, leaving all other positions unchanged. This is the least tuple
above v in the face omitting atom r. Equation (3) forces T_B(w_r)=P.

For each P-input j of v, let D_j be the set of failed old-owner factors
on its unique occurrence path. It is nonempty because T_B(v) is not P.
Passing from v to w_r leaves every other owner's singleton input set
unchanged, and removes all r-singleton inputs. Thus only the r-factor can
change, and it is now true; every other factor is unchanged. No new input
becomes P.
Consequently

    T_B(w_r)=P iff some P-input j has D_j={r}.              (4)

There must be a distinct such P-input for each owner r. Together with
the K old atoms already occurring at v, this requires at least 2K input
positions. This proves agreement below 2K.

For sharpness choose distinct a,b,c and 2K distinct variables X_r,Z_r.
Put L_r=X_r choice_r Z_r. Define H on the L_r by starting with
L_a choice_c L_b and appending every remaining L_r using choice_a.
Each L_r occurs once, so

    T=H((L_r)_(r in I))                                  (5)

is primitive read-once. At v given by X_r=P and Z_r=atom r, all L_r
absorb to r, and H returns N. At w_r, only L_r changes to P, and H
returns P. To check the latter, a P in either initial branch survives
choice_c; a P in a later branch meets an already ambiguous prefix.
Each later singleton branch has owner different from a, so no later
choice_a absorbs it.

Every face tuple w>=v is above some w_r, so its output is P by monotonicity.
Therefore M(v)=P while T_B(v)=N. The completion agrees with every original
face, is monotone, and has the correct singleton profiles, but cannot be
term-induced: extension rigidity makes T_B the only term-induced extension
of F. Thus even the greatest monotone face completion is insufficient;
the earlier semantic-dependence completion supplies a distinct lower-bound
failure. Neither extremum removes the full compatibility problem.
