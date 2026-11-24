module

public import KFOL.Core.AddressedTableQuantified
public import KFOL.Core.QuantifiedThreeCNF

/-! # From encoded quantified CNF to both explicit core tables

The addressed rectangle produces one candidate winner-set table for every
quantified input. Its values on canonical source probes also determine it,
including on inputs for which there is no realizing core word.
-/

@[expose] public section
namespace KFOL.Core.ExplicitTableReduction

open Bichain Bichain.Quantified AddressedRails AddressedRectangle AddressedQuantified
open AddressedRecognition AddressedTableExtraction ProfileBudgets Sources WinnerSet
open Cslib.Logic.PL
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Label Track Bit : Type*} [DecidableEq Role] [Fintype Role]

omit [Fintype Role] in
private theorem supplied [Fintype Bit] [Nonempty Bit] (three : Fin 3 ↪ Role)
    (B : Book Label Track Bit) (l r : CoreTerm Role Label) (z : WinnerSet Role)
    (v : Rail Track Bit → WinnerSet Role)
    (yes : cap B (fun i => decide (v i = singleton (three 2))) = true) :
    three 2 ∈ (baseline three B l r z v).val := by
  have all (f : Label) : B.read (three 2) v f = singleton (three 2) := by
    apply (B.read_aux _ _ _).mpr
    simpa only [decide_eq_true_eq] using (of_decide_eq_true yes f)
  have atom (t : CoreTerm Role Label) : t.realize (B.read (three 2) v) = singleton (three 2) := by
    rw [winnerSet_eq_singleton_iff_profile]
    simpa only [all, decide_true] using (admissibleProfiles_profile t).top (three 2)
  by_cases h : z = singleton (three 1)
  · have other : z ≠ singleton (three 0) := by simp [h, singleton_inj]
    exact Or.inr (by simp only [OneOwnerSelector.mask_eq, ite_eq_right other, atom,
      val_union, val_singleton, Set.mem_union, Set.mem_singleton_iff, or_true])
  · exact Or.inl (by simp only [OneOwnerSelector.mask_eq, ite_eq_right h, atom,
      val_union, val_singleton, Set.mem_union, Set.mem_singleton_iff, or_true])

private theorem cap_mono (B : Book Label Track Bit) (A D : Rail Track Bit → Bool)
    (h : ∀ i, A i = true → D i = true) (a : cap B A = true) : cap B D = true := by
  apply decide_eq_true
  intro f
  obtain ⟨i,hi⟩ := of_decide_eq_true a f
  exact ⟨i,h _ hi⟩

/-- Before testing realizability, the addressed cap has both its raw source
decomposition and its finite canonical prime reconstruction. -/
theorem source_presentation [Fintype Bit] [Nonempty Bit] [Fintype Track] [Nonempty Label]
    (three : Fin 3 ↪ Role) (B : Book Label Track Bit) (l r : CoreTerm Role Label) :
    let F := fun v : Option (Rail Track Bit) → WinnerSet Role =>
      AddressedTableExtraction.operation three B l r (v none) (fun i => v (some i))
    (∀ t : CoreTerm Role (Option (Rail Track Bit)), (∀ v, t.realize v = F v) ↔
      ∀ k j p, k ∈ (t.realize (probe three k j p)).val ↔ k ∈ (F (probe three k j p)).val) ∧
    (∀ v, meaning (normalForm three F) v = (F v).val) := by
  obtain ⟨b,hb⟩ := AddressedTableConstruction.realizes_baseline three B l r
  let ψ := cap B
  have eq (v : Option (Rail Track Bit) → WinnerSet Role) :
      AddressedSelectorCap.operation (three 2) ψ b v =
        AddressedTableExtraction.operation three B l r (v none) (fun i => v (some i)) := by
    rw [AddressedSelectorCap.operation_eq_target]
    unfold AddressedTableExtraction.operation AddressedSelectorCap.target
    simp only [hb]
    rfl
  have keeps (v : Option (Rail Track Bit) → WinnerSet Role)
      (hc : ψ (fun i => decide (v (some i) = singleton (three 2))) = true) :
      three 2 ∈ (b.realize v).val := by
    have eta : (fun j : Option (Rail Track Bit) => j.elim (v none) (fun i => v (some i))) = v := by
      funext j; cases j <;> rfl
    rw [← eta, hb]
    exact supplied three B l r _ _ hc
  constructor
  · intro t
    simpa only [eq] using
      AddressedSelectorCap.realizes_iff_probe_agreement three (three 2) ψ b t keeps
  · intro v
    have e := funext eq
    simpa only [e] using AddressedSelectorCap.normalForm_correct three (three 2) ψ
      (cap_empty B) (cap_mono B) b keeps v

abbrev Input := List (ℕ × ℕ) × CNF ℕ

abbrev Variables (u : Input) :=
  Option (Rail (Palette (Fin 3) ⊕ Bool) (Fin (AddressSize.width (labelBound (ThreeCNF.fromTQBFCNF u)))))

/-- The table of the closed stage formula, or the fixed false formula on
an unclosed source input. -/
noncomputable def target (three : Fin 3 ↪ Role) (u : Input) (v : Variables u → WinnerSet Role) :
    WinnerSet Role :=
  let F := ThreeCNF.translate (Recognition.Lists.formulaOf u)
  let G := translated_geometry F (ThreeCNF.wf_translate _) (ThreeCNF.width _)
  table three G.rectangle Finset.univ (Geometry.initialLeft (ThreeCNF.fromTQBFCNF u) (fun _ => false))
    (Geometry.initialRight (ThreeCNF.fromTQBFCNF u)) v

/-- The complete explicit winner-set table recognizes quantified CNF truth. -/
theorem winner_table_iff (three : Fin 3 ↪ Role) (u : Input) :
    (∃ t : CoreTerm Role (Variables u), ∀ v, t.realize v = target three u v) ↔
      u ∈ Cslib.Complexity.TQBFCNF :=
  (AddressedTableQuantified.three_cnf_iff_table three _ (ThreeCNF.wf_translate _)
    (ThreeCNF.width _) (fun _ => false)).trans
    ((ThreeCNF.sat_translate_iff _ (Recognition.Lists.formulaOf_wf u) _).trans
      (Recognition.Lists.mem_TQBFCNF_iff u).symm)

/-- Both source presentations of this target, independently of its truth value. -/
theorem target_source_presentation (three : Fin 3 ↪ Role) (u : Input) :
    (∀ t : CoreTerm Role (Variables u), (∀ v, t.realize v = target three u v) ↔
      ∀ k j p, k ∈ (t.realize (probe three k j p)).val ↔ k ∈ (target three u (probe three k j p)).val) ∧
    (∀ v, meaning (normalForm three (target three u)) v = (target three u v).val) := by
  unfold target table
  apply source_presentation

/-- The raw isolated-source entries of the same table recognize quantified CNF truth. -/
theorem source_table_iff (three : Fin 3 ↪ Role) (u : Input) :
    (∃ t : CoreTerm Role (Variables u), ∀ k j p, k ∈ (t.realize (probe three k j p)).val ↔
      k ∈ (target three u (probe three k j p)).val) ↔ u ∈ Cslib.Complexity.TQBFCNF :=
  (exists_congr fun t => ((target_source_presentation three u).1 t).symm).trans (winner_table_iff three u)

open Turing.MultiTapeTM Cslib.Complexity

/-- Size in the bit encoding used for the PSPACE-complete source language. -/
def inputBits (u : Input) : ℕ := (encPrenexCNF u).length

private theorem matrix_size (cs : CNF ℕ) : cs.length + cs.vars.length ≤ (encCNF cs).length := by
  rw [CNF.length_vars, encCNF, length_encList]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have size := length_le_length_encList (encPair encNat encBool) c
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem stage_size (u : Input) :
    let F := Recognition.Lists.formulaOf u
    F.n + F.cls.length + (CNF.vars F.cls).length ≤ inputBits u := by
  have rounds := length_le_length_encList (encPair encNat encNat) u.1
  have matrix := matrix_size u.2
  simp only [Recognition.Lists.formulaOf, inputBits, encPrenexCNF, length_encPair]
  split
  · simp only [QBF.length_roundVars, List.length_map, CNF.length_vars, List.map_map,
      Function.comp_def, List.length_map]
    rw [CNF.length_vars] at matrix
    change 2*u.1.length + u.2.length + (u.2.map List.length).sum ≤ _
    omega
  · simp only [CNF.length_vars, List.length_cons,List.length_nil,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
    omega

/-- The address range is linear in encoded input length after clausification
and slot separation. -/
theorem labels_le (u : Input) : labelBound (ThreeCNF.fromTQBFCNF u) ≤ 176 * (inputBits u + 1) := by
  let F := Recognition.Lists.formulaOf u
  let T := ThreeCNF.translate F
  have start : F.n + F.cls.length + (CNF.vars F.cls).length ≤ inputBits u := stage_size u
  obtain ⟨rows, stages⟩ := ThreeCNF.size_bound F
  obtain ⟨width, clauses⟩ := ThreeSlot.size T
  change 8 * ((ThreeSlot.translate T).n + (ThreeSlot.translate T).cls.length + 1) ≤ _
  change T.cls.length ≤ _ at rows
  change T.n ≤ _ at stages
  omega

/-- Number of variables of either table. -/
theorem arity (u : Input) : Fintype.card (Variables u) =
    1 + 28 * AddressSize.width (labelBound (ThreeCNF.fromTQBFCNF u)) :=
  table_arity _

/-- Number of possible input tuples of the winner-set table, polynomial in
the encoded source length at each fixed owner count. -/
theorem winner_entries_bound (k : ℕ) (u : Input) :
    (2^k - 1) ^ Fintype.card (Variables u) ≤
      2^k * (4 * (176 * (inputBits u + 1) + 1)) ^ (28*k) := by
  rw [arity]
  exact (AddressSize.table_length_bound k 14 _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (labels_le u) 1)) _))

omit [DecidableEq Role] in
/-- Number of Boolean entries of the source table, with its variable and
owner indices counted. -/
theorem source_entries_bound (u : Input) :
    let k := Fintype.card Role
    let h := 176 * (inputBits u + 1)
    Fintype.card (Variables u) * k ^ Fintype.card (Variables u) ≤
      (1 + 28 * (h + 3)) * (2^k * (4 * (h + 1))^(28*k)) := by
  classical
  dsimp only
  apply Nat.mul_le_mul
  · rw [arity,AddressSize.width]
    have log := Nat.log2_le_self (labelBound (ThreeCNF.fromTQBFCNF u) + 1)
    have labels := labels_le u
    omega
  · have owners : Fintype.card Role ≤ 2 ^ Fintype.card Role - 1 := by
      have := Nat.lt_two_pow_self (n := Fintype.card Role)
      omega
    exact (Nat.pow_le_pow_left owners _).trans (winner_entries_bound _ u)

end KFOL.Core.ExplicitTableReduction
