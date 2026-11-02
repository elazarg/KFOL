# Research source check

Before using mixed open-game composition, read the known-source refutation
in README and the technical report's "Finite obstructions to the proposed
mixed open-game category" appendix in sections/appendix-open-games.tex.

Ghani--Kupke--Lambert--Nordvall Forsberg (arXiv:2009.06831v1), Definitions
11--12, do not satisfy the claimed unit law or canonical associativity.
The pinned GameTheory v1 proofs also refute the convex-closing repairs.
Do not cite those category laws as established composition results.
This is a scoped refutation, not a general impossibility for mixed games.

Keep the layout of one paper (main.tex) with its technical report (tr.tex).
After a change that renumbers anything in either, run make paper and commit
the label snapshots it updates. Do not modify ../GameTheory.

# Adding results to the paper

A new result is not finished until the text around it still reads well.

New results go in the technical report, placed where they belong in the
appendix's argument rather than at its end. Update the appendix's opening if
the picture changes, and merge or drop what the result supersedes.

Evidence (Lean modules, checks, counts) goes in the verification appendix, not
next to the proof, unless the computation is itself the proof. State a limit
only where a reader would otherwise draw the wrong conclusion, and don't repeat
that a question stays open.

The main text stays at 15 pages or fewer and uses only terms it defines. Change
it only when a stated result or open question changes, and then rewrite the
affected sentences instead of adding new ones. Most results don't belong there.
