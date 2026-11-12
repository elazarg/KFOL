module

public import KFOL.Core.AtomicBasis.Quotient
public import KFOL.Equational.Completeness
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Finite.Range

/-! # The finite displayed presentation and its semantic laws -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

variable {Role : Type u} [DecidableEq Role]

omit [DecidableEq Role] in
theorem pair_spec (p : OwnerPair Role) :
    pairFirst p ≠ pairSecond p ∧ ∀ r, r ∈ p.val ↔ r = pairFirst p ∨ r = pairSecond p := by
  classical
  have hp := (Finset.card_eq_two.mp p.property).choose_spec.choose_spec
  refine ⟨hp.1, ?_⟩
  intro r
  change r ∈ p.val ↔ r = (Finset.card_eq_two.mp p.property).choose ∨
    r = (Finset.card_eq_two.mp p.property).choose_spec.choose
  exact (Iff.of_eq (congrArg (fun s : Finset Role => r ∈ s) hp.2)).trans
    (by simp only [Finset.mem_insert, Finset.mem_singleton])

omit [DecidableEq Role] in
theorem realize_reset {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    {Var : Type*} (three : Fin 3 ↪ Role) (rs : List Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → M) :
    (resetTerm three rs s t).realize v = reset three rs (s.realize v) (t.realize v) := by
  unfold resetTerm reset
  have aux (xs : List Role) (a : Equational.Term (Equational.CoreSymbol Role) Var) :
      (xs.foldl (fun acc r => choiceTerm r t acc) a).realize v =
        xs.foldl (fun acc r => operation r (t.realize v) acc) (a.realize v) := by
    induction xs generalizing a with
    | nil => rfl
    | cons r xs ih => simp only [List.foldl_cons, ih, realize_choice]
  rw [aux, realize_union]

omit [DecidableEq Role] in
theorem models_iff {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role) (rs : List Role) :
    Equational.Models (theory three rs) M ↔
      LiftingLaws (join three) (operation (Role := Role) (M := M)) ∧ ∀ x y : M, reset three rs x y = y := by
  constructor
  · intro hm
    have ax (i : BasisIndex Role) := hm (basisAxiom three rs i) ⟨i, rfl⟩
    have lift : LiftingLaws (join three) (operation (Role := Role) (M := M)) := by
      have pairLaws (i j : Role) (hij : i ≠ j) (x y : M) :
          join three (operation i x y) (operation j x y) = join three x y ∧
          operation i x (operation j x y) = operation j x (operation i x y) := by
        classical
        let p : OwnerPair Role := ⟨{i, j}, by simp [hij]⟩
        have hp := pair_spec p
        have ha : pairFirst p = i ∨ pairFirst p = j := by
          have : pairFirst p ∈ p.val := (hp.2 _).mpr (.inl rfl)
          simpa [p] using this
        have hb : pairSecond p = i ∨ pairSecond p = j := by
          have : pairSecond p ∈ p.val := (hp.2 _).mpr (.inr rfl)
          simpa [p] using this
        have hc := ax (.inr (.inl (p, 0))) ![x, y, x]
        have he := ax (.inr (.inl (p, 1))) ![x, y, x]
        simp only [basisAxiom, Fin.val_zero, Fin.isValue, ite_true, Fin.val_one, one_ne_zero,
          ite_false, realize_union, realize_choice, FirstOrder.Language.Term.realize_var,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hc he
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact False.elim (hp.1 (ha.trans hb.symm))
        · exact ⟨by simpa [ha, hb] using hc, by simpa [ha, hb] using he⟩
        · refine ⟨?_, ?_⟩
          · have hc' : join three (operation j x y) (operation i x y) = join three x y := by
              simpa [ha, hb] using hc
            have comm (a b : M) : join three a b = join three b a := by
              simpa [basisAxiom] using ax (.inl (.inl 1)) ![a, b, a]
            rw [comm]; exact hc'
          · simpa [ha, hb] using he.symm
        · exact False.elim (hp.1 (ha.trans hb.symm))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x; simpa [basisAxiom] using ax (.inl (.inl 0)) (fun _ => x)
      · intro x y; simpa [basisAxiom] using ax (.inl (.inl 1)) ![x, y, x]
      · intro x y z; simpa [basisAxiom] using ax (.inl (.inl 2)) ![x, y, z]
      · intro i x; simpa [basisAxiom] using ax (.inl (.inr (i, 0))) (fun _ => x)
      · intro i x y; simpa [basisAxiom] using ax (.inl (.inr (i, 1))) ![x, y, x]
      · intro i x y z; simpa [basisAxiom] using ax (.inl (.inr (i, 2))) ![x, y, z]
      · intro i x y z; simpa [basisAxiom] using ax (.inl (.inr (i, 3))) ![x, y, z]
      · intro i j hij x y; exact (pairLaws i j hij x y).1
      · intro i j hij x y; exact (pairLaws i j hij x y).2
    refine ⟨lift, ?_⟩
    intro x y
    simpa [basisAxiom, realize_reset] using ax (.inr (.inr ())) ![x, y, x]
  · rintro ⟨h, hr⟩ e ⟨i, rfl⟩ v
    change Fin 3 → M at v
    cases i with
    | inl i =>
      cases i with
      | inl k =>
        fin_cases k
        · simpa [basisAxiom] using h.add_idem (v 0)
        · simpa [basisAxiom] using h.add_comm (v 0) (v 1)
        · simpa [basisAxiom] using h.add_assoc (v 0) (v 1) (v 2)
      | inr ik =>
        obtain ⟨i, k⟩ := ik
        fin_cases k
        · simpa [basisAxiom] using h.op_idem i (v 0)
        · simpa [basisAxiom] using h.op_comm i (v 0) (v 1)
        · simpa [basisAxiom] using h.op_assoc i (v 0) (v 1) (v 2)
        · simpa [basisAxiom] using h.op_add i (v 0) (v 1) (v 2)
    | inr i =>
      cases i with
      | inl pk =>
        obtain ⟨p, k⟩ := pk
        fin_cases k
        · simpa [basisAxiom] using h.cover _ _ (pair_spec p).1 (v 0) (v 1)
        · simpa [basisAxiom] using h.birkhoff _ _ (pair_spec p).1 (v 0) (v 1)
      | inr k => simpa [basisAxiom, realize_reset] using hr (v 0) (v 1)

omit [DecidableEq Role] in
theorem theory_finite [Finite Role] (three : Fin 3 ↪ Role) (rs : List Role) :
    (theory three rs).Finite := by
  classical
  let _ := Fintype.ofFinite Role
  exact Set.finite_range _

omit [DecidableEq Role] in
theorem theory_variableBound (three : Fin 3 ↪ Role) (rs : List Role) :
    Equational.HasVariableBound (theory three rs) 3 := by
  rintro e ⟨i, rfl⟩
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 3)

omit [DecidableEq Role] in
theorem ownerPair_card [Fintype Role] : Fintype.card (OwnerPair Role) = (Fintype.card Role).choose 2 := by
  classical
  let e : OwnerPair Role ≃ {s // s ∈ (Finset.univ : Finset Role).powersetCard 2} := {
    toFun := fun s => ⟨s.val, by simp [s.property]⟩
    invFun := fun s => ⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]

omit [DecidableEq Role] in
/-- Cardinality counts the explicitly indexed displayed family. -/
theorem basisIndex_card [Fintype Role] :
    Fintype.card (BasisIndex Role) = (Fintype.card Role)^2 + 3 * Fintype.card Role + 4 := by
  have hc (n : ℕ) : 2 * n.choose 2 + n = n * n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  simp only [BasisIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, ownerPair_card]
  nlinarith [hc (Fintype.card Role)]

end KFOL.Core.AtomicBasis
