module

public import KFOL.Algebra

/-!
Boundary cases for common-source separation: switches must be retained in the
source action, overlap can prevent any common input, and an empty family must
not require an inhabited winner-set carrier.
-/

@[expose] public section

namespace KFOLTest.CommonSource

open KFOL

private def switched : Term (Fin 2) Unit := .rename (Equiv.swap 0 1) (.var ())
private def inputs (e : Bool) (_ : Unit) : WinnerSet (Fin 2) :=
  WinnerSet.singleton (if e then 1 else 0)
private def regions (e : Bool) : Set (Fin 2) := {if e then 0 else 1}

example : ∃ (x : Unit) (p : Equiv.Perm (Fin 2)), (x, p) ∈ switched.inputOccurrences ∧
    ∀ e, (WinnerSet.rename p (inputs e x)).val ⊆ regions e := by
  refine switched.exists_common_input inputs regions ?_ false true (by decide) ?_
  · intro i j hij
    cases i <;> cases j <;> simp_all [regions]
  · intro e
    cases e <;> simp [switched, inputs, regions, Term.eval]

-- The corresponding unpermuted input does not fit even the first region.
example : ¬∀ e, (inputs e ()).val ⊆ regions e := by
  intro h
  have hf : (0 : Fin 2) ∈ regions false := h false rfl
  simp [regions] at hf

private def overlap : Term (Fin 2) Bool := .choice 0 (.var false) (.var true)
private def crossed (e x : Bool) : WinnerSet (Fin 2) :=
  WinnerSet.singleton (if e = x then 0 else 1)

-- Without disjointness the output can always fit the common region while
-- neither child supplies a single source that fits all valuations.
example : (∀ e, (overlap.eval (crossed e)).val ⊆ ({0} : Set (Fin 2))) ∧
    ¬(∀ e, (crossed e false).val ⊆ ({0} : Set (Fin 2))) ∧
    ¬(∀ e, (crossed e true).val ⊆ ({0} : Set (Fin 2))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    cases e <;> simp [overlap, crossed, Term.eval, WinnerSet.choice]
  · intro h
    have hf : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := h true rfl
    simp at hf
  · intro h
    have hf : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := h false rfl
    simp at hf

-- No valuations need to exist. In particular, this applies even if Role is
-- empty and thus WinnerSet Role has no inhabitant.
example {Role Var : Type} (t : Term Role Var) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf, p) ∈ t.sourceOccurrences := by
  obtain ⟨leaf, p, hp, _⟩ := t.exists_common_source
    (Index := Empty) (fun e => nomatch e) (fun e => nomatch e)
    (by intro e; exact e.elim) (by intro e; exact e.elim)
  exact ⟨leaf, p, hp⟩

-- A single region permits a ground source; the two-region hypothesis in the
-- variable clause is necessary even for a singleton output.
example : ∃ t : Term (Fin 2) Empty,
    (∀ v : Empty → WinnerSet (Fin 2), t.eval v = WinnerSet.singleton 0) ∧
      t.inputOccurrences = [] :=
  ⟨.winner 0, fun _ => rfl, rfl⟩

end KFOLTest.CommonSource
