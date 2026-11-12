Research arguments and exploratory counts, not new audited paper claims.
The mixed-type characterization remains unresolved.

# Full source-type pruning: drift and owner-shadow tests

## Definitions

For source j, a full factor type is a vector (B_r)_r of antitone predicates on sets of rival-r atomic inputs among V\{j}, with B_r(empty)=true. At observer k the type contributes exactly AND_(r!=k) B_r(E_r). A type is sound when all these contributions lie in the given canonical source coefficients.

## Causal drift (necessary)

Suppose a marked j occurrence supplies k and survives at v. Change only s-singleton statuses to obtain w, leaving all other owner-singleton statuses fixed. Assume no input is the k singleton. If its s factor becomes false at w, then the term output at w contains s.

Proof: the first newly absorbing s sibling introduces s. At every other rival-owner ancestor the singleton blocker is unchanged from v, where the chosen k occurrence survived. Own-k absorption is impossible because no input is the k singleton. Therefore s persists to the root.

This has a finite source-array form with no v quantifier. Fix k!=s. In a passive pattern with no k atom, put the source and every neutral input equal to I\{s}. If B_s(E_s)=false and every B_q(E_q) with q notin{k,s} is true, then s must belong to the target output. The corresponding v erases all s atoms to neutral; B_s(empty)=true and every other factor is unchanged. Conversely the minimal s-membership valuation suffices by passive/source monotonicity.

## Owner-shadow incidence (necessary)

Let G be any prime avoidance guard of B_r and put E=G∪{j}. Then, for every i∈E, the target pure-r source coefficient at i must be true when exactly V\E are r atoms and all other passive variables are neutral.

Proof: prime G is realized by a maximal r clique through the chosen occurrence whose label set is exactly E. Any i-labeled vertex in that same clique supplies the test observer k!=r, using the clique to avoid all r atoms. There are no other rival-owner atoms, so all its other owner factors are automatically true.

Equivalently, define the canonical permitted r-hyperedges E by this source-incidence condition. Every prime hyperedge of every actual occurrence factor must be permitted. This extends the familiar one-owner prime-hyperedge compatibility to arbitrary mixed-owner terms.

## A small active-variable counterexample

Already for three variables, let

    F=(X star_r Y) union Z.

All variables are essential. Source Z is unconditional, so the type B_r=[Y!={r}], all other factors true, is globally sound. It passes every causal-drift test. It cannot occur in an F term: its prime r hyperedge {Y,Z} would contain a Y occurrence in a maximal r clique with no X label, whereas every Y occurrence's pure-r factor must exclude X={r}. Owner-shadow incidence detects this immediately.

The earlier drift counterexample also simplifies to the same F: at source Z take B_s=[X!={s}], with every other factor true. This sound type fails causal drift at

    v=(D,{r},D), w=({s},{r},D), D={r,t},

for distinct r,s,t. Thus even active-variable globally sound types cannot all be imposed as actual vertices of a canonical occurrence graph.

## Exact computations

Binary, K=3: all 20 core operations and every decorated term can be exhausted. For each distinguished source there are 103 sound types and 96 actual types. Causal drift removes exactly the seven spurious weakened projection types and leaves exactly all actual types, even before restricting to active variables.

Ternary sample F=(X star_r Y) union Z:

* Sources X,Y: 50 sound, 50 drift-safe, 50 shadow-safe, and all 50 actually realized. The X-context search exhausts 1,086,439 states; Y follows by symmetry.
* Source Z: 125 sound, 51 drift-safe, 29 drift-and-shadow-safe.
* All 29 remaining Z types have explicit decorated term realizations found by contextual closure. That search used every binary core operation on every variable pair, plus F, as a sibling. Its 1,097,087 decorated states exhausted under these 58 contexts. Necessity excludes the other 96 types, so the actual Z-type count is exactly 29; no claim that the restricted contextual search covers arbitrary terms is needed.

The source-Z factor at r is either B_r=1 (requires both X,Y non-r, 25 types) or B_r=15 (unconditional, four types). All 22 drift-safe types with intermediate B_r values 3,5,7 fail owner-shadow incidence.

For a three-variable r fold, every source has 25 sound types and all pass drift and shadow.

## The known nonterms still pass

For both the complete-view AtomicAmalgamation operation and the three-variable cyclic crown operation, every source has 80 globally sound types. All 80 pass both causal drift and owner-shadow incidence, and together cover all 78 positive canonical source coefficients. Thus these necessary individual-type conditions do not characterize joint guard realizability.

A clique-member coverage condition using only the r factor does not add information here: for each r and each source, the 80-type family includes sound types with unconditional r factor, so another clique member can always be assigned an r-enabled type. Mixed-owner factors must be coupled across the same occurrence selections, including missing/maximal cliques and the forbidden Gallai/P4 patterns. No sound closed formulation of that stronger coupling has been obtained.

Even conditional on the target being an actual core operation, soundness,
drift and shadow do not characterize its actual types. The
[all-owner side-effect law](actual-type-side-effects.md) gives a stronger
necessary condition: at an ambiguous marked source, the target must contain
one of the owners whose path factor fails. An explicit K+1-variable core
target has a proposed type passing the old tests and violating this law.
The example concerns exact types, rather than an overestimate of their
combined free coefficients.

## Uniform realization of the ternary sample's remaining types

The exact counts for F=H union Z, H=X star_r Y, also have constructive proofs independent of exhaustive term search.

Every factor vector B can be realized at one marked source leaf in a spine u_B: for each nontrivial B_q choose a core sibling G_q on the other variables whose q-singleton profile is NOT B_q, and attach it by star_q. Such G_q exists by the monotone singleton-profile construction. Omit the node if B_q is identically true.

A useful marked-union lemma is: if a marked type B in T is sound for F, then some marked copy in unionTerm(F,T) has exactly type B. Indeed B_q implies both F and T are not q singletons on the source-not-q probe. This follows by testing only q atoms (all other rival factors are true at the empty set). Every subtree of the outer union implementation is built from F,T and therefore also is not the q singleton whenever B_q holds. Thus no outer node adds a stricter q factor.

For a source-X or source-Y sound type, its r factor already excludes the partner's r singleton. For a source-Z type with B_r=1, its r factor excludes both X and Y being r singletons. In either case attach H by star_r to u_B. This gives a term below F: when H is the r singleton the result is r; otherwise X,Y are both non-r singletons/sets, and F is the union of all inputs. The extra r factor is already implied by B_r. Union with F restores F and retains the marked type. This realizes all 50 X types, 50 Y types, and 25 Z types with B_r=1.

The four remaining Z types have B_r=true and, for q!=r, B_q either true or NOT(X_q AND Y_q). Start at Z and attach H by star_q exactly for the nontrivial factors. Each resulting term lies below F because each attachment is a subset of the union of Z and H. Its q factor is exactly NOT(X_q AND Y_q), since H is a q singleton precisely when both X,Y are q singletons. Union with F restores F without changing the type.

Thus every one of the 50+50+29 surviving types has an explicit uniform realization. Drift and owner-shadow exclude all other full types for this sample.
