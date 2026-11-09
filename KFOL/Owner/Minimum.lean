module

public import KFOL.Owner.SmallCarriers

/-! # No algebra on fewer than four elements generates the owner theory -/

@[expose] public section

namespace KFOL.Owner

universe u

private def mul (M : Type u) [(Equational.language (Symbol Unit)).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language (Symbol Unit)) .reset
    (fun i => if i = 0 then x else y)

private def tri (M : Type u) [(Equational.language (Symbol Unit)).Structure M] (x y z : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language (Symbol Unit)) (.guarded ())
    (fun i => if i = 0 then x else if i = 1 then y else z)

private theorem realize_step {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    {Var : Type*} (s t : Term Unit Var) (v : Var → M) :
    (Term.step s t).realize v = mul M (s.realize v) (t.realize v) := by
  simp only [Term.step, FirstOrder.Language.Term.realize, mul]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

private theorem realize_guarded {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    {Var : Type*} (s t q : Term Unit Var) (v : Var → M) :
    (Term.guarded () s t q).realize v = tri M (s.realize v) (t.realize v) (q.realize v) := by
  simp only [Term.guarded, FirstOrder.Language.Term.realize, tri]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi]
  · by_cases hj : i = 1 <;> simp [hi, hj]

/-- Four generates a theory which no algebra with fewer than four elements
can generate. The comparison uses all finite-arity identities in the
independent equational semantics, not a selected finite checklist. -/
theorem four_minimum_generator {M : Type u} [Fintype M]
    [(Equational.language (Symbol Unit)).Structure M]
    (hTheory : ∀ e : Equational.Identity (Symbol Unit),
      (letI := fourStructure (Role := Unit); e.Holds Four) ↔ e.Holds M) :
    4 ≤ Fintype.card M := by
  classical
  by_contra hcard
  have hc : Fintype.card M ≤ 3 := by omega
  let f := mul M
  let h := tri M
  let X : Term Unit (Fin 3) := .var 0
  let Y : Term Unit (Fin 3) := .var 1
  let Z : Term Unit (Fin 3) := .var 2
  have transfer (s t : Term Unit (Fin 3))
      (ht : ∀ v : Fin 3 → Four, s.evalFour v = t.evalFour v) :
      ∀ v : Fin 3 → M, s.realize v = t.realize v := by
    exact (hTheory ⟨3, s, t⟩).mp ht
  have law_idem : ∀ x : M, (f x x) = x := by
    have hh := transfer (Term.step X X) X (by
      intro v
      change (Four.reset (v 0) (v 0)) = (v 0)
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x
    simpa [realize_step, X, FirstOrder.Language.Term.realize_var] using hh ![x, x, x]
  have law_absorb : ∀ x y : M, (f (f x y) x) = (f y x) := by
    have hh := transfer (Term.step (Term.step X Y) X) (Term.step Y X) (by
      intro v
      change (Four.reset (Four.reset (v 0) (v 1)) (v 0)) = (Four.reset (v 1) (v 0))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y
    simpa [realize_step, X, Y, FirstOrder.Language.Term.realize_var] using hh ![x, y, x]
  have law_repeat_right : ∀ x y : M, (f (f x y) y) = (f x y) := by
    have hh := transfer (Term.step (Term.step X Y) Y) (Term.step X Y) (by
      intro v
      change (Four.reset (Four.reset (v 0) (v 1)) (v 1)) = (Four.reset (v 0) (v 1))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y
    simpa [realize_step, X, Y, FirstOrder.Language.Term.realize_var] using hh ![x, y, x]
  have law_nested : ∀ x y z : M, (f x (f (f x y) z)) = (f x (f y z)) := by
    have hh := transfer (Term.step X (Term.step (Term.step X Y) Z)) (Term.step X (Term.step Y Z)) (by
      intro v
      change (Four.reset (v 0) (Four.reset (Four.reset (v 0) (v 1)) (v 2))) = (Four.reset (v 0) (Four.reset (v 1) (v 2)))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y z
    simpa [realize_step, X, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![x, y, z]
  have law_exchange : ∀ x y z : M, (f (f (f x y) z) y) = (f (f x z) y) := by
    have hh := transfer (Term.step (Term.step (Term.step X Y) Z) Y) (Term.step (Term.step X Z) Y) (by
      intro v
      change (Four.reset (Four.reset (Four.reset (v 0) (v 1)) (v 2)) (v 1)) = (Four.reset (Four.reset (v 0) (v 2)) (v 1))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y z
    simpa [realize_step, X, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![x, y, z]
  have law_left_comm : ∀ x y z : M, (f x (f y z)) = (f y (f x z)) := by
    have hh := transfer (Term.step X (Term.step Y Z)) (Term.step Y (Term.step X Z)) (by
      intro v
      change (Four.reset (v 0) (Four.reset (v 1) (v 2))) = (Four.reset (v 1) (Four.reset (v 0) (v 2)))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y z
    simpa [realize_step, X, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![x, y, z]
  have law_minor1 : ∀ x y : M, (h x y y) = (f y x) := by
    have hh := transfer (Term.guarded () X Y Y) (Term.step Y X) (by
      intro v
      change (Four.guarded (v 0) (v 1) (v 1)) = (Four.reset (v 1) (v 0))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y
    simpa [realize_step, realize_guarded, X, Y, FirstOrder.Language.Term.realize_var] using hh ![x, y, x]
  have law_minor2 : ∀ y z : M, (h y y z) = (f z y) := by
    have hh := transfer (Term.guarded () Y Y Z) (Term.step Z Y) (by
      intro v
      change (Four.guarded (v 1) (v 1) (v 2)) = (Four.reset (v 2) (v 1))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro y z
    simpa [realize_step, realize_guarded, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![y, y, z]
  have law_minor3 : ∀ x y : M, (h x y x) = (f y x) := by
    have hh := transfer (Term.guarded () X Y X) (Term.step Y X) (by
      intro v
      change (Four.guarded (v 0) (v 1) (v 0)) = (Four.reset (v 1) (v 0))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y
    simpa [realize_step, realize_guarded, X, Y, FirstOrder.Language.Term.realize_var] using hh ![x, y, x]
  have law_abs1 : ∀ x y z : M, (f (h x y z) x) = (h x y z) := by
    have hh := transfer (Term.step (Term.guarded () X Y Z) X) (Term.guarded () X Y Z) (by
      intro v
      change (Four.reset (Four.guarded (v 0) (v 1) (v 2)) (v 0)) = (Four.guarded (v 0) (v 1) (v 2))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y z
    simpa [realize_step, realize_guarded, X, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![x, y, z]
  have law_abs2 : ∀ x y z : M, (f x (h x y z)) = (h x y z) := by
    have hh := transfer (Term.step X (Term.guarded () X Y Z)) (Term.guarded () X Y Z) (by
      intro v
      change (Four.reset (v 0) (Four.guarded (v 0) (v 1) (v 2))) = (Four.guarded (v 0) (v 1) (v 2))
      generalize v 0 = a
      generalize v 1 = b
      generalize v 2 = c
      cases a <;> cases b <;> cases c <;> rfl)
    intro x y z
    simpa [realize_step, realize_guarded, X, Y, Z, FirstOrder.Language.Term.realize_var] using hh ![x, y, z]
  have hf : Reset.Laws f := ⟨law_idem, law_absorb, law_repeat_right, law_nested, law_exchange, law_left_comm⟩
  have hm : ∀ x y z, h x y y = f y x ∧ h y y z = f z y ∧ h x y x = f y x :=
    fun x y z => ⟨law_minor1 x y, law_minor2 y z, law_minor3 x y⟩
  have ha : ∀ x y z, f (h x y z) x = h x y z ∧ f x (h x y z) = h x y z :=
    fun x y z => ⟨law_abs1 x y z, law_abs2 x y z⟩
  rcases small_expansion_obstruction f h hc hf hm ha with hassoc | hfirst | hsecond
  · have heM : (⟨3, (Term.step (Term.step X Y) Z), (Term.step X (Term.step Y Z))⟩ : Equational.Identity (Symbol Unit)).Holds M := by
      intro v
      simpa [realize_step, X, Y, Z, FirstOrder.Language.Term.realize_var] using hassoc (v 0) (v 1) (v 2)
    have heF := (hTheory ⟨3, (Term.step (Term.step X Y) Z), (Term.step X (Term.step Y Z))⟩).mpr heM
    have hf : (Term.step (Term.step X Y) Z).evalFour ![Four.winning, Four.owner, Four.ambiguous] = (Term.step X (Term.step Y Z)).evalFour ![Four.winning, Four.owner, Four.ambiguous] := heF ![Four.winning, Four.owner, Four.ambiguous]
    simp [Term.evalFour_step, Term.evalFour_var, X, Y, Z, Four.reset] at hf
  · have heM : (⟨3, (Term.step (Term.guarded () X Y Z) (Term.step (Term.step Z Y) X)), (Term.step (Term.step Z Y) X)⟩ : Equational.Identity (Symbol Unit)).Holds M := by
      intro v
      simpa [realize_step, realize_guarded, X, Y, Z, FirstOrder.Language.Term.realize_var] using hfirst (v 0) (v 1) (v 2)
    have heF := (hTheory ⟨3, (Term.step (Term.guarded () X Y Z) (Term.step (Term.step Z Y) X)), (Term.step (Term.step Z Y) X)⟩).mpr heM
    have hf : (Term.step (Term.guarded () X Y Z) (Term.step (Term.step Z Y) X)).evalFour ![Four.ambiguous, Four.other, Four.winning] = (Term.step (Term.step Z Y) X).evalFour ![Four.ambiguous, Four.other, Four.winning] := heF ![Four.ambiguous, Four.other, Four.winning]
    simp [Term.evalFour_step, Term.evalFour_guarded, Term.evalFour_var, X, Y, Z, Four.reset, Four.guarded] at hf
  · have heM : (⟨3, (Term.step (Term.step Z X) (Term.guarded () X Y Z)), (Term.guarded () X Y Z)⟩ : Equational.Identity (Symbol Unit)).Holds M := by
      intro v
      simpa [realize_step, realize_guarded, X, Y, Z, FirstOrder.Language.Term.realize_var] using hsecond (v 0) (v 1) (v 2)
    have heF := (hTheory ⟨3, (Term.step (Term.step Z X) (Term.guarded () X Y Z)), (Term.guarded () X Y Z)⟩).mpr heM
    have hf : (Term.step (Term.step Z X) (Term.guarded () X Y Z)).evalFour ![Four.ambiguous, Four.owner, Four.winning] = (Term.guarded () X Y Z).evalFour ![Four.ambiguous, Four.owner, Four.winning] := heF ![Four.ambiguous, Four.owner, Four.winning]
    simp [Term.evalFour_step, Term.evalFour_guarded, Term.evalFour_var, X, Y, Z, Four.reset, Four.guarded] at hf

end KFOL.Owner
