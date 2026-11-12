# Canonical prime boxes need not be occurrence boxes

Research note, 12 November 2026; these results are not yet Lean statements.

Let the distinct owners be 0,1,2 and write star_r for owned choice: a singleton r absorbs, otherwise take set union. Consider the genuine three-variable core operation

    F(a,b,c) = (a star_0 b) star_2 (a star_1 (b star_1 c)).

The argument below uses this four-gate term directly; no minimality claim or term enumeration is needed.

## Canonical source-a coefficients

On an isolated source-a probe, a is the observer k singleton; every other input is either a rival singleton or neutral ambiguity omitting k. Directly from the operation:

    C_(a,0) = true,
    C_(a,1) = true,
    C_(a,2) = [b != {0}] OR ([b != {1}] AND [c != {1}])
            = [b != {0}] OR [c != {1}].

The last identity holds because b cannot be both the 0 and the 1 singleton. Thus the canonical prime guard family at (observer 2, source a) consists of the two singleton guards

    {(b,0)} and {(c,1)}.

Both are indispensable in the canonical prime cover. The input b={0}, c=neutral is covered only by the second.

## Maximal globally sound full types

For a source-a occurrence, let B_r(E_r) be its antitone owner-r factor, true at the empty set of rival-r atomic inputs. Order full types by coordinatewise implication: a larger type permits more source survival.

The maximal globally sound types are exactly

    T_left:  B_0=[b != {0}], B_1=B_2=true;
    T_prime: B_1=[c != {1}], B_0=B_2=true.

Indeed the only negative source-a probe is a={2}, b={0}, c={1}. A sound type must fail B_0 at {b} or B_1 at {c}. Antitonicity then places it below T_left or T_prime. Both displayed types are sound by the coefficient identities above.

## T_prime is impossible in every representation of F

Suppose an a occurrence has owner-1 factor [c != {1}]. In a finite occurrence graph, its factor is the disjunction of the avoidance guards of maximal 1-cliques through that occurrence. Hence some such maximal clique has label set exactly {a,c}. In particular it contains a c occurrence and no b occurrence.

Evaluate at

    a={1,2}, b={1}, c={0}.

The clique through that c occurrence avoids all 1-singleton inputs. There are no 2-singleton inputs anywhere, so every maximal 2-clique through the c occurrence also avoids 2 atoms. Therefore the occurrence supplies winner 0 to the root by the clique source law.

But direct evaluation gives

    a star_0 b = {1,2},
    a star_1 (b star_1 c) = {1},
    F(a,b,c) = {1,2},

which excludes 0. Contradiction. This proof only uses the owner-1 factor and excludes T_prime even if its other factors are strengthened arbitrarily.

In fact the single-observer prime box [c != {1}] cannot be the observer-2 contribution of any a occurrence. Equality to this box forces B_0=true (test b=c={0}) and B_1=[c != {1}] (then vary the 1-atom set), giving the same contradiction.

## The actual occurrence boxes and their exact maxima

The two a occurrences in the displayed term have types

    T_left:  B_0=[b != {0}], all other factors true;
    T_right: B_1=[b != {1}] AND [c != {1}], all other factors true.

The root's owner-2 factor is true at both a occurrences: its sibling contains another a occurrence and therefore cannot be the 2 singleton on a pure-2 factor probe with source a non-2.

These are exactly the maximal *realizable* source-a types among all terms representing F. To see necessity, every sound type lies below T_left or T_prime. If it is not below T_left, its B_1 factor excludes the c atom. With only b,c available, that factor is either [c != {1}] or [b != {1}] AND [c != {1}]. The first has just been ruled out; hence the type lies below T_right. Both maxima occur in the displayed term.

Thus the exact maximal-realizable types are strictly different from the canonical maximal-sound types. The change is essential to covering the source coefficient.

## Consequences for the current characterization route

1. A carrier containing one occurrence for every canonical prime box, or every maximal globally sound full type, rejects this genuine core operation. It cannot serve as a universal occurrence carrier.
2. Keeping an irredundant prime cover does not repair this: the unrealizable box is indispensable in that cover.
3. Taking globally maximal boxes first and then pruning by owner-shadow incidence also fails: it deletes T_prime and loses valid positive probes. One must refine a prime box into strictly smaller occurrence boxes before, or while, imposing clique laws.
4. Taking maxima *after* the shadow test recovers the two exact realizable maxima in this example. This is an example, not a general sufficiency theorem: AtomicAmalgamation and the cyclic crown pass both drift and shadow tests and remain nonterms.
5. The lost information is a consensus step across mutually exclusive statuses of the *same variable*. The raw occurrence guard {(b,1),(c,1)} combines with {(b,0)} to create canonical prime {(c,1)}. Exact maximal-clique obligations apply to the raw guards and do not survive taking semantic prime guards literally.

The proof is uniform in any ambient owner set containing three distinct owners; no additional-owner singleton occurs in its decisive probe.

## Checkable evidence

`canonical-prime-occurrence-counterexample.py` independently checks all source probes, all 125 ternary factor types, both maximal sound types, the owner-shadow failure, the two maximal shadow-safe types, the two marked occurrence factors, and the explicit output contradiction. It uses only Python's standard library and no clone enumeration.

`maximal-types-minimize.py` is separate discovery evidence for the four-gate minimality check, not needed for the theorem.
