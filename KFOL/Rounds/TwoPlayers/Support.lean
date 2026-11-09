module

public import KFOL.Rounds.TwoPlayers.Endpoints
public import KFOL.Algebra.Semilattice
public import KFOL.Algebra.TwoPlayers.Algebra

/-! # Literal public folds compute all two-role round possible winners -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.TwoPlayers

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

/-- The literal public serialization in which player zero commits first. -/
def serialZero (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) : WinnerSet (Fin 2) :=
  WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
    WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
      g (matrixAction sizes row col)

/-- The literal public serialization in which player one commits first. -/
def serialOne (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) : WinnerSet (Fin 2) :=
  WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
    WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
      g (matrixAction sizes row col)

theorem serialZero_eq_zero_iff (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) :
    serialZero sizes g = WinnerSet.singleton 0 ↔
      ∃ row, ∀ col, g (matrixAction sizes row col) = WinnerSet.singleton 0 := by
  simp only [serialZero,WinnerSet.choiceFold_eq_owner_iff,
    WinnerSet.choiceFold_eq_other_iff (1:Fin 2) 0 (by decide),Finset.mem_univ,true_and,forall_const]

theorem serialOne_eq_one_iff (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) :
    serialOne sizes g = WinnerSet.singleton 1 ↔
      ∃ col, ∀ row, g (matrixAction sizes row col) = WinnerSet.singleton 1 := by
  simp only [serialOne,WinnerSet.choiceFold_eq_owner_iff,
    WinnerSet.choiceFold_eq_other_iff (0:Fin 2) 1 (by decide),Finset.mem_univ,true_and,forall_const]

theorem serialZero_eq_one_iff (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) :
    serialZero sizes g = WinnerSet.singleton 1 ↔
      ∀ row, ∃ col, g (matrixAction sizes row col) = WinnerSet.singleton 1 := by
  simp only [serialZero,WinnerSet.choiceFold_eq_other_iff (0:Fin 2) 1 (by decide),
    WinnerSet.choiceFold_eq_owner_iff,Finset.mem_univ,true_and,forall_const]

theorem serialOne_eq_zero_iff (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) :
    serialOne sizes g = WinnerSet.singleton 0 ↔
      ∀ col, ∃ row, g (matrixAction sizes row col) = WinnerSet.singleton 0 := by
  simp only [serialOne,WinnerSet.choiceFold_eq_other_iff (1:Fin 2) 0 (by decide),
    WinnerSet.choiceFold_eq_owner_iff,Finset.mem_univ,true_and,forall_const]

/-- The two endpoint implications of the finite max-min inequality follow
from the actual nonempty finite menu quantifiers. -/
theorem serial_extremes (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) :
    (serialZero sizes g = WinnerSet.singleton 0 → serialOne sizes g = WinnerSet.singleton 0) ∧
    (serialOne sizes g = WinnerSet.singleton 1 → serialZero sizes g = WinnerSet.singleton 1) := by
  constructor
  · rw [serialZero_eq_zero_iff,serialOne_eq_zero_iff]
    rintro ⟨row,hrow⟩ col
    exact ⟨row,hrow col⟩
  · rw [serialOne_eq_one_iff,serialZero_eq_one_iff]
    rintro ⟨col,hcol⟩ row
    exact ⟨col,hcol row⟩

/-- In the proved three-value carrier, endpoint equivalences determine the
winner class and its strong-Kleene union expression. -/
theorem support_of_endpoints (winner A B : WinnerSet (Fin 2))
    (hzero : winner = WinnerSet.singleton 0 ↔ A = WinnerSet.singleton 0)
    (hone : winner = WinnerSet.singleton 1 ↔ B = WinnerSet.singleton 1)
    (hab0 : A = WinnerSet.singleton 0 → B = WinnerSet.singleton 0)
    (hab1 : B = WinnerSet.singleton 1 → A = WinnerSet.singleton 1) :
    winner = A.union B ∧ A.union B =
      WinnerSet.choice 1 (WinnerSet.choice 0 A
        ((WinnerSet.singleton 0).union (WinnerSet.singleton 1))) B := by
  obtain ⟨i,rfl⟩ := KFOL.TwoPlayers.value_surjective (Equiv.refl (Fin 2)) winner
  obtain ⟨j,rfl⟩ := KFOL.TwoPlayers.value_surjective (Equiv.refl (Fin 2)) A
  obtain ⟨k,rfl⟩ := KFOL.TwoPlayers.value_surjective (Equiv.refl (Fin 2)) B
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp_all [KFOL.TwoPlayers.value,WinnerSet.choice,
    WinnerSet.union_eq_singleton_iff,WinnerSet.singleton_inj]
  all_goals first | (constructor <;> apply Subtype.ext) | apply Subtype.ext
  all_goals ext who
  all_goals fin_cases who <;> simp [WinnerSet.union]

private theorem possibleWinners_singleton (law : PMF (Fin 2)) :
    possibleWinners {law} = law.support := by
  ext who
  simp only [possibleWinners,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,
    PMF.mem_support_iff]

/-- An exact nonempty-set readout of one law is an atom exactly when that
actual probability law is the corresponding pure distribution. -/
private theorem representative_pure_iff (g : WinnerSet (Fin 2)) (law : PMF (Fin 2))
    (hg : g.val = possibleWinners {law}) (who : Fin 2) :
    g = WinnerSet.singleton who ↔ law = PMF.pure who := by
  constructor
  · intro he
    apply pmf_eq_pure_of_support_subset_singleton
    intro i hi
    have hm : i ∈ g.val := by rw [hg,possibleWinners_singleton]; exact hi
    simpa only [he,WinnerSet.val_singleton,Set.mem_singleton_iff] using hm
  · intro he
    apply Subtype.ext
    rw [hg,he,possibleWinners_singleton]
    ext i
    simp only [PMF.mem_support_pure_iff,WinnerSet.val_singleton,Set.mem_singleton_iff]

/-- Exact child winner-set representatives always exist for the actual
canonical SE values; callers need supply no finite certificate. -/
theorem exists_child_winnerSets (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Game (Fin 2))
    (order : ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      ∀ actions, (g actions).val = possibleWinners ((next actions).sequentialValues order) := by
  choose law _ values using fun actions =>
    observedValues_singleton (0:Fin 2) 1 (by decide) (next actions) (finTwo_usesOnly _)
  refine ⟨(fun actions => ⟨(law actions).support,(law actions).support_nonempty⟩),?_⟩
  intro actions
  rw [sequentialValues_eq_observedValues,values actions,possibleWinners_singleton]

/-- The full report round formula for every actual child-winner readout.
The public serializations are literal nonempty folds of actual finite menus. -/
theorem round_support_folds (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Game (Fin 2))
    (order : ExplicitOrder (Fin 2))
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2))
    (hg : ∀ actions, (g actions).val = possibleWinners ((next actions).sequentialValues order)) :
    let Sa := WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
      WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
        g (matrixAction sizes row col)
    let Sb := WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
      WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
        g (matrixAction sizes row col)
    possibleWinners ((Game.round sizes next).sequentialValues order) = (Sa.union Sb).val ∧
      Sa.union Sb = WinnerSet.choice 1 (WinnerSet.choice 0 Sa
        ((WinnerSet.singleton 0).union (WinnerSet.singleton 1))) Sb := by
  change possibleWinners ((Game.round sizes next).sequentialValues order) =
      ((serialZero sizes g).union (serialOne sizes g)).val ∧ _
  choose p _ child using fun actions =>
    observedValues_singleton (0:Fin 2) 1 (by decide) (next actions) (finTwo_usesOnly _)
  have childSeq (actions) : (next actions).sequentialValues order = {p actions} := by
    rw [sequentialValues_eq_observedValues,child actions]
  have childPure (actions) (who : Fin 2) :
      g actions = WinnerSet.singleton who ↔ p actions = PMF.pure who :=
    representative_pure_iff (g actions) (p actions) (by rw [← childSeq actions]; exact hg actions) who
  obtain ⟨profile,nash⟩ := Observed.stage_exists_nash sizes p
  change ((i : Fin 2) → PMF (Fin (sizes i+1))) at profile
  let law : PMF (Fin 2) := (independentProduct profile).bind p
  have member : law ∈ (Game.round sizes next).sequentialValues order := by
    rw [sequentialValues_round]
    exact ⟨p,(fun actions => by dsimp only; rw [childSeq actions]; exact Set.mem_singleton _),profile,nash,rfl⟩
  obtain ⟨root,_,hroot⟩ := observedValues_singleton (0:Fin 2) 1 (by decide)
    (Game.round sizes next) (finTwo_usesOnly _)
  have parent : (Game.round sizes next).sequentialValues order = {law} := by
    rw [sequentialValues_eq_observedValues,hroot] at member ⊢
    have he : law = root := member
    rw [he]
  let winner : WinnerSet (Fin 2) := ⟨law.support,law.support_nonempty⟩
  have hwinner : winner.val = possibleWinners {law} := (possibleWinners_singleton law).symm
  have hzero : winner = WinnerSet.singleton 0 ↔ serialZero sizes g = WinnerSet.singleton 0 := by
    rw [representative_pure_iff winner law hwinner]
    dsimp only [law]
    rw [nash_pure_zero_iff sizes p profile nash,serialZero_eq_zero_iff]
    exact exists_congr fun row => forall_congr' fun col => (childPure _ 0).symm
  have hone : winner = WinnerSet.singleton 1 ↔ serialOne sizes g = WinnerSet.singleton 1 := by
    rw [representative_pure_iff winner law hwinner]
    dsimp only [law]
    rw [nash_pure_one_iff sizes p profile nash,serialOne_eq_one_iff]
    exact exists_congr fun col => forall_congr' fun row => (childPure _ 1).symm
  obtain ⟨hwin,hunion⟩ := support_of_endpoints winner (serialZero sizes g) (serialOne sizes g)
    hzero hone (serial_extremes sizes g).1 (serial_extremes sizes g).2
  refine ⟨?_,hunion⟩
  rw [parent,← hwinner,hwin]

/-- The actual finite-menu round formula comes with proved existence of its
exact child winner sets, closing the report proposition without hypotheses
about a separately computed or certified evaluator. -/
theorem exists_round_support_folds (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Game (Fin 2))
    (order : ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      (∀ actions, (g actions).val = possibleWinners ((next actions).sequentialValues order)) ∧
      let Sa := WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
        WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
          g (matrixAction sizes row col)
      let Sb := WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
        WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
          g (matrixAction sizes row col)
      possibleWinners ((Game.round sizes next).sequentialValues order) = (Sa.union Sb).val ∧
        Sa.union Sb = WinnerSet.choice 1 (WinnerSet.choice 0 Sa
          ((WinnerSet.singleton 0).union (WinnerSet.singleton 1))) Sb := by
  obtain ⟨g,hg⟩ := exists_child_winnerSets sizes next order
  exact ⟨g,hg,round_support_folds sizes next order g hg⟩

/-- With exactly two roles the possible-winner observation itself is a
congruence for every actual round context, including independent repeated
holes. This is derived from the complete fold theorem, not assumed by a
separately defined recursive three-value evaluator. -/
theorem possibleWinners_context_congr (context : Context (Fin 2))
    (left right : Game (Fin 2)) (order : ExplicitOrder (Fin 2))
    (heq : possibleWinners (left.sequentialValues order) =
      possibleWinners (right.sequentialValues order)) :
    possibleWinners ((context.fill left).sequentialValues order) =
      possibleWinners ((context.fill right).sequentialValues order) := by
  induction context with
  | hole => exact heq
  | leaf who => rfl
  | round sizes next ih =>
    obtain ⟨g,hg⟩ := exists_child_winnerSets sizes (fun actions => (next actions).fill left) order
    have hgRight (actions) : (g actions).val =
        possibleWinners (((next actions).fill right).sequentialValues order) :=
      (hg actions).trans (ih actions)
    exact (round_support_folds sizes _ order g hg).1.trans
      (round_support_folds sizes _ order g hgRight).1.symm

end KFOL.Rounds.Game.TwoPlayers
