module

public import KFOL.Owner.Four
public import KFOL.Equational.Locality

/-! A four-element algebra satisfying every three-variable owner identity,
but failing the four-variable root-expansion identity. -/

@[expose] public section

namespace KFOL.Owner.BasisObstruction

@[simp] theorem realize_step {Var : Type*} (s t : Term Unit Var) (v : Var → Carrier) :
    (Term.step s t).realize v = reset (s.realize v) (t.realize v) := rfl

@[simp] theorem realize_guarded {Var : Type*} (s t q : Term Unit Var) (v : Var → Carrier) :
    (Term.guarded () s t q).realize v = guarded (s.realize v) (t.realize v) (q.realize v) := rfl

theorem conservative (x y z : Carrier) :
    (reset x y = x ∨ reset x y = y) ∧
    (guarded x y z = x ∨ guarded x y z = y ∨ guarded x y z = z) := by
  cases x <;> cases y <;> cases z <;> decide

theorem embed_injective (e x y : Carrier) (hx : x ≠ e) (hy : y ≠ e)
    (he : embed e x = embed e y) : x = y := by
  cases e <;> cases x <;> cases y <;> simp_all [embed]

theorem embed_reset (e x y : Carrier) (hx : x ≠ e) (hy : y ≠ e) :
    embed e (reset x y) =
      (Four.reset (embed e x).1 (embed e y).1, Four.reset (embed e x).2 (embed e y).2) := by
  cases e <;> cases x <;> cases y <;> simp_all [embed, reset, rank, Four.reset]

theorem embed_guarded (e x y z : Carrier) (hx : x ≠ e) (hy : y ≠ e) (hz : z ≠ e) :
    embed e (guarded x y z) =
      (Four.guarded (embed e x).1 (embed e y).1 (embed e z).1,
       Four.guarded (embed e x).2 (embed e y).2 (embed e z).2) := by
  cases e <;> cases x <;> cases y <;> cases z <;>
    simp_all [embed, guarded, reset, rank, Four.guarded]

theorem realize_ne {Var : Type*} (t : Term Unit Var) (v : Var → Carrier)
    (e : Carrier) (hv : ∀ j, v j ≠ e) : t.realize v ≠ e := by
  induction t using Term.induction_owner with
  | var j => exact hv j
  | step l r hl hr =>
    rcases (conservative (l.realize v) (r.realize v) e).1 with he | he
    · simpa only [realize_step, he] using hl
    · simpa only [realize_step, he] using hr
  | guarded a x y z hx hy hz =>
    cases a
    rcases (conservative (x.realize v) (y.realize v) (z.realize v)).2 with he | he | he
    · simpa only [realize_guarded, he] using hx
    · simpa only [realize_guarded, he] using hy
    · simpa only [realize_guarded, he] using hz

theorem embed_realize {Var : Type*} (t : Term Unit Var) (v : Var → Carrier)
    (e : Carrier) (hv : ∀ j, v j ≠ e) :
    embed e (t.realize v) =
      (t.evalFour (fun j => (embed e (v j)).1), t.evalFour (fun j => (embed e (v j)).2)) := by
  induction t using Term.induction_owner with
  | var j => rfl
  | step l r hl hr =>
    rw [realize_step, embed_reset e _ _ (realize_ne l v e hv) (realize_ne r v e hv), hl, hr]
    rfl
  | guarded a x y z hx hy hz =>
    cases a
    rw [realize_guarded, embed_guarded e _ _ _ (realize_ne x v e hv) (realize_ne y v e hv)
      (realize_ne z v e hv), hx, hy, hz]
    rfl

/-- Every identity supported on at most three variables holds in the witness,
regardless of padded arity or term depth. -/
theorem holds_of_variableCount_le (e : Equational.Identity (Symbol Unit))
    (hn : e.variableCount ≤ 3) (hvalid : letI := fourStructure (Role := Unit); e.Holds Four) :
    e.Holds Carrier := by
  classical
  intro v
  let X := e.support.image v
  have hX : X.card ≤ 3 := Finset.card_image_le.trans hn
  have hmissing : ∃ a : Carrier, a ∉ X := by
    by_contra! h
    have hc := Finset.card_le_card (show Finset.univ ⊆ X from fun a _ => h a)
    have hcard : Fintype.card Carrier = 4 := by decide
    rw [Finset.card_univ, hcard] at hc
    omega
  obtain ⟨a, ha⟩ := hmissing
  let fallback : Carrier := if a = .low then .middle else .low
  have hf : fallback ≠ a := by
    cases a <;> decide
  let w : Fin e.arity → Carrier := fun i => if i ∈ e.support then v i else fallback
  have hw : ∀ i, w i ≠ a := by
    intro i
    dsimp [w]
    split
    next hi =>
      intro he
      exact ha (he ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    next _ => exact hf
  have heq : e.lhs.realize w = e.rhs.realize w := by
    apply embed_injective a _ _ (realize_ne e.lhs w a hw) (realize_ne e.rhs w a hw)
    rw [embed_realize e.lhs w a hw, embed_realize e.rhs w a hw,
      show Term.evalFour e.lhs (fun i => (embed a (w i)).1) = Term.evalFour e.rhs (fun i => (embed a (w i)).1) from
        hvalid (fun i => (embed a (w i)).1),
      show Term.evalFour e.lhs (fun i => (embed a (w i)).2) = Term.evalFour e.rhs (fun i => (embed a (w i)).2) from
        hvalid (fun i => (embed a (w i)).2)]
  have hwl : e.lhs.realize w = e.lhs.realize v := Equational.realize_eq_of_eqOn e.lhs w v
    (fun i hi => by
      have hi' : i ∈ e.support := Finset.mem_union_left _ hi
      simp only [w, hi', ite_true])
  have hwr : e.rhs.realize w = e.rhs.realize v := Equational.realize_eq_of_eqOn e.rhs w v
    (fun i hi => by
      have hi' : i ∈ e.support := Finset.mem_union_right _ hi
      simp only [w, hi', ite_true])
  exact hwl.symm.trans (heq.trans hwr)

theorem rootExpansion_holds : letI := fourStructure (Role := Unit); rootExpansion.Holds Four := by
  intro v
  change Fin 4 → Four at v
  change Four.guarded (Four.reset (v 0) (v 1)) (v 2) (v 3) =
    Four.reset (Four.reset (v 0) (v 1)) (Four.guarded (v 1) (v 2) (v 3))
  generalize v 0 = u
  generalize v 1 = r
  generalize v 2 = a
  generalize v 3 = b
  cases u <;> cases r <;> cases a <;> cases b <;> rfl

theorem rootExpansion_fails : ¬rootExpansion.Holds Carrier := by
  intro h
  have hh := h ![.middle, .low, .high, .isolated]
  have hn : guarded (reset .middle .low) .high .isolated ≠
      reset (reset .middle .low) (guarded .low .high .isolated) := by decide
  exact hn hh

/-- No basis, even infinite, can use only three distinct variables per axiom. -/
theorem not_hasVariableBound_three (T : Equational.Theory (Symbol Unit))
    (hbasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four T) :
    ¬Equational.HasVariableBound T 3 := by
  let _ := fourStructure (Role := Unit)
  intro hbound
  have hmodels : Equational.Models T Carrier := by
    intro e he
    exact holds_of_variableCount_le e (hbound e he) (hbasis.models e he)
  exact rootExpansion_fails (((hbasis rootExpansion).mp rootExpansion_holds).sound Carrier hmodels)

/-- Every variable bound of any basis is at least four, including infinite bases. -/
theorem variableBound_ge_four (T : Equational.Theory (Symbol Unit)) (n : ℕ)
    (hbasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four T)
    (hbound : Equational.HasVariableBound T n) : 4 ≤ n := by
  by_contra hn
  apply not_hasVariableBound_three T hbasis
  intro e he
  exact (hbound e he).trans (by omega)

end KFOL.Owner.BasisObstruction
