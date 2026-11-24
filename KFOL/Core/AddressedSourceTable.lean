module

public import KFOL.Core.AddressedSelectorCap
public import KFOL.Core.SourceNormalForm
public import KFOL.Core.SingleSourceCompletion
import KFOL.Equational.Native

/-! # The source table of a selector cap before realizability is known -/

@[expose] public section
namespace KFOL.Core.AddressedSelectorCap

open Sources
open scoped Classical

variable {Role Var : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

/-- The cap reads the internal rails and the baseline reads all inputs. -/
noncomputable def operation (c : Role) (ψ : (Var → Bool) → Bool)
    (b : Word Role (Option Var)) (v : Option Var → WinnerSet Role) : WinnerSet Role :=
  if ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) then WinnerSet.singleton c
  else b.realize v

omit [DecidableEq Role] in
/-- This is the same reset as the two-argument selector target. -/
theorem operation_eq_target (c : Role) (ψ : (Var → Bool) → Bool)
    (b : Word Role (Option Var)) (v : Option Var → WinnerSet Role) :
    operation c ψ b v = target c ψ
      (fun z w => b.realize (fun j => j.elim z w)) (v none) (fun i => v (some i)) := by
  have e : (fun j : Option Var => j.elim (v none) (fun i => v (some i))) = v := by
    funext j
    cases j <;> rfl
  simp only [operation, target, e]

omit [DecidableEq Role] in
private theorem probe_flags (three : Fin 3 ↪ Role) (k c : Role) (diff : c ≠ k)
    (j : Option Var) (v : Option Var → WinnerSet Role) (source : k ∈ (v j).val) :
    (fun i : Var => decide (probe three k j (pattern k j v) (some i) = WinnerSet.singleton c)) =
      fun i => decide (v (some i) = WinnerSet.singleton c) := by
  classical
  funext i
  by_cases same : some i = j
  · rw [same, probe_source]
    have no : v j ≠ WinnerSet.singleton c := by
      intro h
      exact diff ((by simpa [h] using source : k = c).symm)
    simp [WinnerSet.singleton_inj, Ne.symm diff, no]
  · rw [probe_other three k j _ (some i) same]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      (representative_atom_iff three k (pattern k j v ⟨some i,same⟩) ⟨c,diff⟩).trans
        (passive_eq_atom_iff k (v (some i)) ⟨c,diff⟩)

/-- A cap that keeps a winner already supplied by the baseline has the exact
canonical source decomposition even when the capped operation is not core. -/
theorem membership_iff_source (three : Fin 3 ↪ Role) (c : Role)
    (ψ : (Var → Bool) → Bool) (b : Word Role (Option Var))
    (supplied : ∀ v : Option Var → WinnerSet Role,
      ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true → c ∈ (b.realize v).val)
    (v : Option Var → WinnerSet Role) (k : Role) :
    k ∈ (operation c ψ b v).val ↔
      ∃ j, k ∈ (v j).val ∧ k ∈ (operation c ψ b (probe three k j (pattern k j v))).val := by
  classical
  let t := Equational.Core.decode b
  have base (w : Option Var → WinnerSet Role) (s : Role) :
      s ∈ (b.realize w).val ↔
        ∃ j, s ∈ (w j).val ∧ s ∈ (b.realize (probe three s j (pattern s j w))).val := by
    simpa only [t, Equational.Core.eval_decode] using
      Sources.membership_iff_source three t (Equational.Core.isCore_decode b) w s
  by_cases same : k = c
  · subst k
    have keep (w : Option Var → WinnerSet Role) :
        c ∈ (operation c ψ b w).val ↔ c ∈ (b.realize w).val := by
      unfold operation
      split_ifs with h
      · simp [supplied w h]
      · rfl
    simpa only [keep] using base v c
  · have equal (j : Option Var) (hj : k ∈ (v j).val) := probe_flags three k c (Ne.symm same) j v hj
    by_cases cap : ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true
    · constructor
      · simp [operation, cap, same]
      · rintro ⟨j,hj,hk⟩
        simp only [operation, equal j hj, cap, ite_true, WinnerSet.val_singleton,
          Set.mem_singleton_iff] at hk
        exact (same hk).elim
    · rw [operation, ite_eq_right cap, base v k]
      apply exists_congr
      intro j
      apply and_congr_right
      intro hj
      simp only [operation, equal j hj, ite_eq_right cap]

/-- For a core word, matching all entries of the isolated-source table is
equivalent to realizing every entry of the winner-set table. -/
theorem realizes_iff_probe_agreement (three : Fin 3 ↪ Role) (c : Role)
    (ψ : (Var → Bool) → Bool) (b t : Word Role (Option Var))
    (supplied : ∀ v : Option Var → WinnerSet Role,
      ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true → c ∈ (b.realize v).val) :
    (∀ v, t.realize v = operation c ψ b v) ↔
      ∀ k j p, k ∈ (t.realize (probe three k j p)).val ↔
        k ∈ (operation c ψ b (probe three k j p)).val := by
  constructor
  · intro agrees k j p
    rw [agrees]
  · intro agrees v
    apply Subtype.ext
    ext k
    have source := Sources.membership_iff_source three (Equational.Core.decode t)
      (Equational.Core.isCore_decode t) v k
    simp only [Equational.Core.eval_decode] at source
    rw [source, membership_iff_source three c ψ b supplied v k]
    exact exists_congr (fun j => and_congr_right (fun _ => agrees k j _))

open ProfileSourceFiber SingleSourceCompletion

/-- The flags seen by the cap among the actual off-head postings. -/
noncomputable def postedFlags (c : Role) {j : Option Var} (q : Observation Role j)
    (i : Var) : Bool :=
  if off : some i ≠ j then decide ((⟨some i, off⟩, c) ∈ postings q) else false

omit [DecidableEq Role] in
private theorem flags_without_owner (c : Role) {j : Option Var} (q : Observation Role j)
    (owns : q.1 = c) : postedFlags c q = fun _ => false := by
  funext i
  unfold postedFlags
  split_ifs with off
  · apply Bool.eq_false_iff.mpr
    rintro h
    obtain ⟨s, _, hs⟩ := of_decide_eq_true h
    exact s.property (hs.trans owns.symm)
  · rfl

omit [DecidableEq Role] in
private theorem flags_at_foreign_probe (three : Fin 3 ↪ Role) (c : Role) {j : Option Var}
    (q : Observation Role j) (foreign : q.1 ≠ c) :
    (fun i : Var => decide (probe three q.1 j q.2 (some i) = WinnerSet.singleton c)) =
      postedFlags c q := by
  funext i
  unfold postedFlags
  split_ifs with off
  · rw [probe_other three q.1 j _ (some i) off]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro atom
      exact ⟨⟨c,Ne.symm foreign⟩, (representative_atom_iff three q.1 _ ⟨c,Ne.symm foreign⟩).mp atom, rfl⟩
    · rintro ⟨s,hs,eq⟩
      exact ((representative_atom_iff three q.1 _ s).mpr hs).trans (congrArg WinnerSet.singleton eq)
  · rw [not_ne_iff.mp off, probe_source]
    simp [WinnerSet.singleton_inj, foreign]

/-- The capped coefficient is the baseline coefficient with the cap postings
excluded, including on overlaps between different observers' facets. -/
theorem coefficient_iff (three : Fin 3 ↪ Role) (c : Role) (ψ : (Var → Bool) → Bool)
    (empty : ψ (fun _ => false) = false) (b : Word Role (Option Var))
    (supplied : ∀ v : Option Var → WinnerSet Role,
      ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true → c ∈ (b.realize v).val)
    {j : Option Var} (q : Observation Role j) :
    q.1 ∈ (operation c ψ b (probe three q.1 j q.2)).val ↔
      q.1 ∈ (b.realize (probe three q.1 j q.2)).val ∧ ψ (postedFlags c q) = false := by
  by_cases owns : q.1 = c
  · rw [flags_without_owner c q owns, empty]
    simp only [and_true]
    unfold operation
    split_ifs with cap
    · change q.1 = c ↔ q.1 ∈ (b.realize (probe three q.1 j q.2)).val
      let out := (b.realize (probe three q.1 j q.2)).val
      have hc : c ∈ out := supplied _ cap
      exact ⟨fun _ => Eq.mp (congrArg (fun x => x ∈ out) owns.symm) hc, fun _ => owns⟩
    · rfl
  · rw [operation, flags_at_foreign_probe three c q owns]
    cases cap : ψ (postedFlags c q) <;> simp [owns]

/-- The complete table agrees across observers and is antitone in the actual
postings, regardless of whether the target has a realizer. -/
theorem coefficients_downward (three : Fin 3 ↪ Role) (c : Role)
    (ψ : (Var → Bool) → Bool) (empty : ψ (fun _ => false) = false)
    (mono : ∀ A B, (∀ i, A i = true → B i = true) → ψ A = true → ψ B = true)
    (b : Word Role (Option Var))
    (supplied : ∀ v : Option Var → WinnerSet Role,
      ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true → c ∈ (b.realize v).val)
    (j : Option Var) :
    Downward (fun q : Observation Role j =>
      q.1 ∈ (operation c ψ b (probe three q.1 j q.2)).val) := by
  intro p q inc hq
  rw [coefficient_iff three c ψ empty b supplied] at hq ⊢
  have base := supplies_downward (j := j) three (Equational.Core.decode b) (Equational.Core.isCore_decode b)
  constructor
  · simpa only [Supplies, Equational.Core.eval_decode] using base p q inc (by
      simpa only [Supplies, Equational.Core.eval_decode] using hq.1)
  · apply Bool.eq_false_iff.mpr
    intro hp
    apply Bool.eq_false_iff.mp hq.2
    apply mono _ _ _ hp
    intro i hi
    by_cases off : some i ≠ j
    · simp only [postedFlags, dite_eq_left off, decide_eq_true_eq] at hi ⊢
      exact inc hi
    · simp only [postedFlags, dite_eq_right off] at hi ⊢
      exact hi

/-- The finite canonical prime family computed from the explicit cap tables
reconstructs the supplied operation on every valuation. -/
theorem normalForm_correct [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (c : Role) (ψ : (Var → Bool) → Bool) (empty : ψ (fun _ => false) = false)
    (mono : ∀ A B, (∀ i, A i = true → B i = true) → ψ A = true → ψ B = true)
    (b : Word Role (Option Var))
    (supplied : ∀ v : Option Var → WinnerSet Role,
      ψ (fun i => decide (v (some i) = WinnerSet.singleton c)) = true → c ∈ (b.realize v).val)
    (v : Option Var → WinnerSet Role) :
    meaning (normalForm three (operation c ψ b)) v = (operation c ψ b v).val := by
  ext k
  rw [membership_iff_source three c ψ b supplied v k]
  change (∃ j, k ∈ (v j).val ∧ ∃ g ∈ normalForm three (operation c ψ b) k j,
      Enabled g (pattern k j v)) ↔ _
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  have mh := (downward_iff_facets _).mp (coefficients_downward three c ψ empty mono b supplied j)
  rw [iff_enabled_prime _ (mh.1 k)]
  simp only [mem_normalForm]

end KFOL.Core.AddressedSelectorCap
