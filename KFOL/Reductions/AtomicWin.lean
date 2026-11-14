module

public import KFOL.Definitions.AtomicDecision
public import KFOL.Definitions.Reductions
public import KFOL.Algebra.Atomic.Boolean

/-! # SAT as one player's possible win under atomic valuations

A fixed atomic unary test reads an input as true precisely at the chosen
truth role. Renaming interchanges true and false; two owned choices then
implement the Boolean connectives. Every compiled formula is atom-preserving.
-/

@[expose] public section

namespace KFOL.Reductions.AtomicWin

universe u

open Classical

variable {Role : Type u}

/-- Correctness of a fixed unary atomic Boolean test. -/
def Tests (a b : Role) (test : Term Role Unit) : Prop :=
  ∀ value, test.eval (fun _ => WinnerSet.singleton value) =
    WinnerSet.singleton (if value = a then a else b)

theorem exists_test [Finite Role] (a b : Role) :
    ∃ test : Term Role Unit, Tests a b test := by
  obtain ⟨test, correct⟩ := Term.atomic_realization_unary ()
    (fun value : Role => if value = a then a else b)
  exact ⟨test, fun value => correct (fun _ => value)⟩

def positive (test : Term Role Unit) (name : ℕ) : Term Role ℕ :=
  test.subst (fun _ => .var name)

noncomputable def negation (a b : Role) : Equiv.Perm Role :=
  Equiv.swap a b

noncomputable def literal (a b : Role) (test : Term Role Unit)
    (input : Literal) : Term Role ℕ :=
  if input.2 then positive test input.1
  else .rename (negation a b) (positive test input.1)

noncomputable def clause (a b : Role) (test : Term Role Unit)
    (input : Clause) : Term Role ℕ :=
  input.foldr (fun item rest => .choice a (literal a b test item) rest) (.winner b)

noncomputable def formula (a b : Role) (test : Term Role Unit)
    (input : CNF) : Term Role ℕ :=
  input.foldr (fun item rest => .choice b (clause a b test item) rest) (.winner a)

theorem positive_eval (a b : Role) (test : Term Role Unit) (correct : Tests a b test)
    (valuation : ℕ → Role) (name : ℕ) :
    (positive test name).eval (fun j => WinnerSet.singleton (valuation j)) =
      WinnerSet.singleton (if valuation name = a then a else b) := by
  rw [positive, Term.eval_subst]
  exact correct (valuation name)

theorem literal_eval (a b : Role) (test : Term Role Unit) (correct : Tests a b test)
    (valuation : ℕ → Role) (input : Literal) :
    (literal a b test input).eval (fun j => WinnerSet.singleton (valuation j)) =
      WinnerSet.singleton (if decide (valuation input.1 = a) = input.2 then a else b) := by
  classical
  rcases input with ⟨name, sign⟩
  cases sign <;> by_cases h : valuation name = a <;>
    simp [literal, negation, Term.eval, positive_eval a b test correct, h]

theorem clause_eval (a b : Role) (test : Term Role Unit) (correct : Tests a b test)
    (valuation : ℕ → Role) (input : Clause) :
    (clause a b test input).eval (fun j => WinnerSet.singleton (valuation j)) =
      WinnerSet.singleton (if ∃ item ∈ input, decide (valuation item.1 = a) = item.2
        then a else b) := by
  classical
  induction input with
  | nil => simp [clause, Term.eval]
  | cons item rest ih =>
    change WinnerSet.choice a
      ((literal a b test item).eval _) ((clause a b test rest).eval _) = _
    rw [literal_eval a b test correct, ih, WinnerSet.choice_boolean_or]
    simp

theorem formula_eval (a b : Role) (test : Term Role Unit) (correct : Tests a b test)
    (valuation : ℕ → Role) (input : CNF) :
    (formula a b test input).eval (fun j => WinnerSet.singleton (valuation j)) =
      WinnerSet.singleton (if ∀ item ∈ input,
        ∃ lit ∈ item, decide (valuation lit.1 = a) = lit.2 then a else b) := by
  classical
  induction input with
  | nil => simp [formula, Term.eval]
  | cons item rest ih =>
    change WinnerSet.choice b
      ((clause a b test item).eval _) ((formula a b test rest).eval _) = _
    rw [clause_eval a b test correct, ih, WinnerSet.choice_boolean_and]
    simp

theorem formula_atomPreserving (a b : Role) (test : Term Role Unit)
    (correct : Tests a b test) (input : CNF) :
    (formula a b test input).AtomPreserving :=
  fun valuation => ⟨_, formula_eval a b test correct valuation input⟩

theorem formula_possible_iff (a b : Role) (different : a ≠ b)
    (test : Term Role Unit) (correct : Tests a b test) (input : CNF) :
    (formula a b test input).AtomicPossibleWin a ↔ Satisfiable input := by
  classical
  constructor
  · rintro ⟨valuation, wins⟩
    rw [formula_eval a b test correct] at wins
    refine ⟨fun name => decide (valuation name = a), ?_⟩
    split at wins
    · assumption
    · exact False.elim (different (Set.mem_singleton_iff.mp wins))
  · rintro ⟨assignment, satisfies⟩
    refine ⟨fun name => if assignment name then a else b, ?_⟩
    rw [formula_eval a b test correct]
    have hread (name : ℕ) :
        decide ((if assignment name then a else b) = a) = assignment name := by
      cases assignment name <;> simp [Ne.symm different]
    have hs : ∀ item ∈ input,
        ∃ lit ∈ item, decide ((if assignment lit.1 then a else b) = a) = lit.2 := by
      simpa only [hread] using satisfies
    change a ∈ (WinnerSet.singleton (if _ then a else b)).val
    rw [ite_eq_left hs]
    exact Set.mem_singleton a

end KFOL.Reductions.AtomicWin
