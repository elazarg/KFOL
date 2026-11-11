module

import Paper
import Report

open KFOL

/- Absorption may erase no member of the union: duplicated owner atoms lose
one unit through overlap. The stronger budget still charges one choice. -/
example :
    let t : Term (Fin 3) Empty := .choice 0 (.winner 0) (.winner 0)
    t.overlapLoss Empty.elim = 1 ∧ t.absorptionLoss Empty.elim = 0 ∧
      t.absorbingCount Empty.elim = 1 := by
  simp [Term.overlapLoss, Term.absorptionLoss, Term.absorbingCount, Term.eval]

/- A variable occurrence supplies its entire winner set, even with no choices. -/
example (ν : Unit → WinnerSet (Fin 3)) (hν : (ν ()).val = Set.univ) :
    let t : Term (Fin 3) Unit := .var ()
    t.choiceCount = 0 ∧ (t.eval ν).val.ncard = 3 ∧ t.leafMass ν = 3 := by
  simp [Term.choiceCount, Term.eval, Term.leafMass, hν]

/- Intermediate permutations matter to overlap. Two copies of one atomic
input become disjoint after one is renamed. -/
example :
    let ν : Unit → WinnerSet (Fin 3) := fun _ => WinnerSet.singleton 0
    let t : Term (Fin 3) Unit :=
      .choice 2 (.var ()) (.rename (Equiv.swap 0 1) (.var ()))
    t.DisjointChoices ν ∧ (t.eval ν).val.ncard = 2 := by
  dsimp
  have h : (Term.choice 2 (Term.var ())
      (Term.rename (Equiv.swap 0 1) (Term.var ())) : Term (Fin 3) Unit).DisjointChoices
      (fun _ => WinnerSet.singleton 0) := by
    simp [Term.DisjointChoices, Term.eval]
  refine ⟨h, ?_⟩
  rw [(Term.winner_budget_eq_iff _ _).mpr h]
  simp [Term.leafMass]

/- Both extreme absorption counts and saturation at K are covered for every n. -/
example (n : ℕ) : ∃ G : Strategic.Tree (Fin 3),
    G.choiceCount = n ∧ G.absorbingCount = n ∧ (Strategic.value G).val.ncard = 1 := by
  obtain ⟨_, G, hc, ha, hv⟩ :=
    Report.public_sharp_absorbing_budget (Function.Embedding.refl (Fin 3)) n n (Nat.le_refl _)
  exact ⟨G, hc, ha, by simpa [Nat.card_fin] using hv⟩

example (n : ℕ) : ∃ G : Strategic.Tree (Fin 3),
    G.choiceCount = n ∧ (Strategic.value G).val.ncard = min 3 (n + 1) := by
  obtain ⟨_, G, hc, hv⟩ :=
    Report.public_sharp_winner_budget (Function.Embedding.refl (Fin 3)) n
  exact ⟨G, hc, by simpa [Nat.card_fin] using hv⟩
