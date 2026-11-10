# Algebra prior-art sweep (2026-11-10)

The question was whether published work, under any name, already proves or
subsumes the report's algebraic results:

1. no finite basis for the core;
2. owned choice with union generates the dissemilattices;
3. reset, antimatroids and canonical tables;
4. the one-owner basis and the policy dichotomy;
5. coNP-completeness of the core;
6. congruences.

These notes are outside the paper. Nothing in `main.tex` or `tr.tex` was changed.

**Method.** A deep-research workflow covered five search angles. It fetched 18
sources and extracted 76 claims. It verified 25 of them with three independent
refutation votes each: 24 survived and 1 was refuted. I then read the decisive
sources myself and ran a few searches on the angles where it was thin.

- **Full text, read by me:**
  - Kearnes–Willard 1999.
  - Freese et al. 2002 (author preprint).
  - Berman–Blok (preprint).
  - Olde Loohuis's MoL thesis and LC2009 slides.
- **Abstract or review only:** Hunt–Rosenkrantz–Bloniarz 1987, Gorazd–Krzaczkowski
  2011, Jackson 2008, Knoebel–Romanowska 1991 (zbMATH review).
- **Not opened by me:** Ham–Jackson, and the choice-function papers.

## Verdict

No published result found proves or subsumes any of (1)–(6). Two parts
were already known:

- congruence meet-semidistributivity in (6);
- the basis and residual largeness in (3), which come from Freese et al. 2002.

The TR treats both correctly. Negative verdicts reflect search coverage, not
proof of absence. The gaps are listed at the end.

| Result | Verdict | Closest work, and why it does not apply |
|---|---|---|
| (1) No finite basis for the core and for V(D_K) | No prior art found | Jackson 2008 needs a bottom that absorbs *every* operation; in D_K each atom absorbs only its own. Knoebel–Romanowska 1991 treats *distributive* multisemilattices, but ⋆_r does not distribute over ⋆_s. |
| (2) {⋆_a, ∪} gives the dissemilattices | Covered by Harding–Romanowska 2017 (cited) | — |
| (3) Reset | Basis and residual largeness: Freese et al. 2002 (cited). Antimatroid bijection and polynomial tables: no prior art found | Freese et al. Lemmas 3.5–3.6 give normal forms. A full-text grep finds no "antimatroid", "polynomial" or "word problem", and no free spectrum of P_{2+1}. |
| (4) Basis for {◁,H_a}, and P/coNP split for policy pairs | No prior art found | Gorazd–Krzaczkowski 2011 split P/coNP only for two-element algebras, and for algebras generating the variety of one. Reset's variety is not such a variety: a two-element idempotent operation is a projection or a semilattice operation. |
| (5) Core coNP-complete without constants | No prior art found | Hunt–Rosenkrantz–Bloniarz 1987 show constant-free coNP-hardness for lattices only. Owned choice with union is not a lattice: x⋆_a(x∪y)=x fails at x={b}, y={c}. |
| (6) Subdirect structure and the uniform-matroid chain | No prior art found | Knoebel–Romanowska's subdirectly irreducibles have 2 or 3 elements. |
| (6) Meet-semidistributivity | Classical | See below. |

## Points worth acting on

**An infinite subdirectly irreducible algebra.**
`sections/appendix-core-basis.tex:435-441` derives that the core variety has no
finite residual bound and no finite critical depth. The core variety is
congruence meet-semidistributive, of finite type and not finitely based. So it
has unboundedly large subdirectly irreducibles. By Kearnes–Willard, *Proc. AMS*
127 (1999) 2841–2850, Theorem 4.1, it then contains an *infinite* subdirectly
irreducible algebra. The same argument applies to V(D_K).

Residual largeness does not follow. The workflow's claim that it does was
refuted 3–0. Whether the core is residually large is still the open question
at `:1002`.

**Meet-semidistributivity is classical.**
Kearnes–Willard 1999, §1, says that V(A) is congruence meet-semidistributive
"whenever the operations of A include a semilattice operation". They point to
Hobby–McKenzie 1988, Theorem 9.10, for the general case. The TR instead derives
this from Willard's condition C₂(T) at `:435` and `:996-998`. That derivation
is correct, but a citation would do.

**The atomic subvariety already has a finite basis by Baker's theorem.**
The TR shows that A_K^at and its K two-element images generate the same
variety (`:818-822`). It also shows that this variety has a (K+1)-ary
near-unanimity term (`:836-856`). A finitely generated, congruence-distributive
variety of finite type is finitely based by Baker, *Adv. Math.* 24 (1977)
207–243. So the existence of a finite basis in `core:thm:atomic-basis` is
classical. What the TR adds is:

- the explicit three-variable basis of K²+3K+4 equations;
- the equation V(A^at) = V(C_K) ∩ Mod{x◁y=y};
- the optimal arity of the near-unanimity term.

Citing Baker 1977 there would keep a reader from crediting the wrong part.

**MPL_R adds no citation obligation.**
The workflow recommended citing Olde Loohuis's "rational" semantics MPL_R
(LC2009 slides, joint with Venema). It is defined there as follows.

- **Values:** vectors in {0,1}^I, read as "the value player i can guarantee
  given common knowledge of rationality".
- **Choice by j:** take the branch j strictly prefers, or the componentwise
  minimum if j is indifferent.
- **Stated results:** tableau completeness, functional completeness, and
  i-satisfiability in P. There are no equational results.

I checked that on single-winner valuations (the paper's atoms) MPL_R and plain
MPL forcing compute the same function: e_j if one branch is e_j, e_k if both
branches are e_k, and 0 otherwise. That function is the atomic quotient, which
the TR already identifies with Olde Loohuis–Venema's guarantee algebra
(`sections/algebra-perspectives.tex:18-19`). The MoL thesis (ILLC MoL-2008-07,
pp. 68–69) mentions common knowledge of rationality and backward induction only
as future work. MPL_R would fit at most as historical motivation, and slides
are not archival.

## Other sources found (context only; no current result needs them)

- **Berman and Blok, "Algebras defined from ordered sets and the varieties they
  generate", *Order* (2006), doi:10.1007/s11083-006-9032-2.** A follow-up to
  Freese et al. It studies the operations a→b and a·b on posets with a top. Its
  varieties H and J are finitely based, and J = HSP of a three-element algebra.
  Its §5 describes free-algebra elements by quasi-orders on the variables plus
  the rightmost variable. This is the closest published analogue to reset's
  root plus antimatroid tables. It is not reset, and it gives no complexity
  bound.
- **Additively idempotent semirings.** Jackson–Ren–Zhao (2022) give a
  three-element NFB semiring S7 with commutative multiplication. Later
  flat-semiring papers (arXiv 2506.23047, 2608.12284) continue the line. S7's
  multiplication is not idempotent, so S7 is not a dissemilattice. This is
  relevant only as a source of NFB techniques for two-operation algebras.
- **Ham and Jackson, arXiv:2212.02653, Cor. 6.6.** Flat extensions of lattices
  whose universal Horn theory has no finite basis are NFB. The same
  absorbing-bottom obstruction as Jackson 2008 applies.
- **Path-independent choice functions and convex geometries:** Koshevoy 1999;
  Johnson–Dean; Monjardet–Raderanirina 2001; Danilov–Koshevoy 2005. These are
  background for "choice operators as antimatroids". They contain no clones,
  bases or complexity results.
- **Lévai and Pálfy, "On binary minimal clones", *Acta Cybernetica* 12 (1996)
  279–294.** They classify the binary minimal clones with 3, 4 or 6 binary
  operations. This would matter only if the TR said more about minimal clones
  than its Waldhauser citation does.
- **Bergman–Juedes–Slutzki, *IJAC* 9 (1999).** Deciding whether two finite
  algebras are term-equivalent is EXPTIME-complete. That is a different problem
  from identity checking in a fixed algebra.

## Coverage gaps

- **Identity checking for non-semigroup multi-operation algebras.** No general
  criterion was found that would imply (5) or the hard half of (4). The search
  turned up mostly semigroup, group and ring results. The papers by Seif–Szabó,
  Kisielewicz, Klíma and Kompatscher were not opened.
- **Forward citations of Freese et al. 2002 and Waldhauser 2006.** Only
  Berman–Blok was found. No systematic "cited by" crawl was done.
- **Non-distributive finite bisemilattices or multisemilattices.** No
  finite-basis results were found, but the search was not exhaustive.
- **Sources read only through abstracts or reviews.** Their theorem numbers
  should be checked against the full text before citing. The Freese et al.
  theorem numbers come from the 33-page preprint; the journal version has 36
  pages.
