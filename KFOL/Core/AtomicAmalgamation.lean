module

public import KFOL.Definitions.CoreAmalgamation
public import KFOL.Core.StatusModel
public import KFOL.Algebra.Views
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-! # Observer realizations without a common atomic core realization

Every role's complete view of the joint output has an explicit core witness.
A finite closed relation excludes a common core witness on three atomic rows.
-/

@[expose] public section
namespace KFOL.Core.AtomicAmalgamation

open WinnerSet WinnerSet.StatusModel

private def statusObservers (v : Fin 3 → Value (Fin 3)) : Fin 3 → Value (Fin 3) :=
  observerPolynomials Value.union Value.choice v

private def statusRaw (v : Fin 3 → Value (Fin 3)) : Finset (Fin 3) :=
  Finset.univ.filter (fun r => r ∈ (statusObservers v r).val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem finite_observer_facts : ∀ v : Fin 3 → Value (Fin 3),
    (statusRaw v).Nonempty ∧
    (∀ r : Fin 3, statusRaw v = {r} ↔ ∀ j, v j = Value.singleton r) ∧
    (∀ r k : Fin 3, statusObservers v r = Value.singleton k ↔
      ∀ j, v j = Value.singleton k) := by
  decide +kernel


private noncomputable def status (A : WinnerSet (Fin 3)) : Value (Fin 3) := by
  classical
  exact ⟨A.val.toFinset, by simpa using A.property⟩

private theorem status_toWinner (A : WinnerSet (Fin 3)) : (status A).toWinner = A := by
  apply Subtype.ext
  simp [status, Value.toWinner]

private theorem statusObservers_toWinner (v : Fin 3 → Value (Fin 3)) (r : Fin 3) :
    (statusObservers v r).toWinner =
      observerPolynomials WinnerSet.union WinnerSet.choice (fun j => (v j).toWinner) r := by
  fin_cases r <;> simp [statusObservers, observerPolynomials]

private theorem statusRaw_coe (v : Fin 3 → Value (Fin 3)) :
    (statusRaw v : Set (Fin 3)) = raw (fun j => (v j).toWinner) := by
  ext r
  change r ∈ statusRaw v ↔
    r ∈ (observerPolynomials WinnerSet.union WinnerSet.choice (fun j => (v j).toWinner) r).val
  rw [← statusObservers_toWinner]
  simp [statusRaw, Value.toWinner]


/-- The joint raw output is a genuine nonempty winner set at every valuation. -/
theorem raw_nonempty (v : Fin 3 → WinnerSet (Fin 3)) : (raw v).Nonempty := by
  have he : (fun j => (status (v j)).toWinner) = v := funext fun j => status_toWinner (v j)
  rw [← he, ← statusRaw_coe]
  simpa using (finite_observer_facts (fun j => status (v j))).1

/-- All singleton profiles of the joint output are three-variable unanimity. -/
theorem raw_eq_singleton_iff (v : Fin 3 → WinnerSet (Fin 3)) (r : Fin 3) :
    raw v = {r} ↔ ∀ j, v j = WinnerSet.singleton r := by
  have he : (fun j => (status (v j)).toWinner) = v := funext fun j => status_toWinner (v j)
  rw [← he, ← statusRaw_coe]
  simpa only [← Finset.coe_singleton, Finset.coe_inj,
    ← Value.toWinner_singleton, Value.toWinner_injective.eq_iff] using
    (finite_observer_facts (fun j => status (v j))).2.1 r

private theorem observer_eq_singleton_iff (v : Fin 3 → WinnerSet (Fin 3)) (r k : Fin 3) :
    observerPolynomials WinnerSet.union WinnerSet.choice v r = WinnerSet.singleton k ↔
      ∀ j, v j = WinnerSet.singleton k := by
  have he : (fun j => (status (v j)).toWinner) = v := funext fun j => status_toWinner (v j)
  rw [← he, ← statusObservers_toWinner, ← Value.toWinner_singleton]
  simpa only [Value.toWinner_injective.eq_iff] using
    (finite_observer_facts (fun j => status (v j))).2.2 r k

theorem observerTerm_isCore (r : Fin 3) : (observerTerm r).IsCore := by
  fin_cases r <;> simp [observerTerm, observerPolynomials, Term.unionTerm, Term.IsCore]

theorem eval_observerTerm (r : Fin 3) (v : Fin 3 → WinnerSet (Fin 3)) :
    (observerTerm r).eval v = observerPolynomials WinnerSet.union WinnerSet.choice v r := by
  fin_cases r <;> simp [observerTerm, observerPolynomials, Term.eval_unionTerm, Term.eval]

/-- The three raw outputs at the distinguishing rows are the required pairs. -/
theorem raw_atomicInput (i : Fin 3) : raw (atomicInput i) = atomicOutput i := by
  fin_cases i <;> ext r <;> fin_cases r <;>
    simp [raw, atomicInput, rows, atomicOutput, observerPolynomials, WinnerSet.choice,
      WinnerSet.val_union, WinnerSet.val_singleton, WinnerSet.singleton_inj]


/-- Binary membership masks of computable nonempty statuses. -/
private def mask (A : Value (Fin 3)) : Nat :=
  (if 0 ∈ A.val then 1 else 0) + (if 1 ∈ A.val then 2 else 0) +
    (if 2 ∈ A.val then 4 else 0)

/-- Each entry encodes the allowed third masks as seven bits. This is an
explicit closed relation certificate; no exhaustiveness or cardinality claim
about term operations is needed. -/
private def relationTable : Fin 7 → Fin 7 → Nat :=
  ![![103, 0, 0, 0, 0, 0, 0],
    ![0, 82, 0, 8, 114, 112, 114],
    ![0, 0, 118, 8, 118, 112, 118],
    ![0, 85, 85, 8, 0, 85, 85],
    ![0, 87, 119, 0, 118, 117, 119],
    ![0, 85, 85, 8, 112, 117, 117],
    ![0, 87, 119, 8, 118, 117, 119]]

private def code (A : Value (Fin 3)) : Fin 7 := Fin.ofNat 7 (mask A - 1)

private def CertifiedCode (x : Fin 3 → Fin 7) : Prop :=
  (relationTable (x 0) (x 1)).testBit (x 2).val = true

private def Certified (x : Fin 3 → Value (Fin 3)) : Prop :=
  CertifiedCode (fun i => code (x i))

private instance (x : Fin 3 → Value (Fin 3)) : Decidable (Certified x) := by
  unfold Certified CertifiedCode
  infer_instance

private instance (x : Fin 3 → Fin 7) : Decidable (CertifiedCode x) := by
  unfold CertifiedCode
  infer_instance

private def codeChoice (r : Fin 3) (x y : Fin 7) : Fin 7 :=
  if x.val + 1 = 2 ^ r.val ∨ y.val + 1 = 2 ^ r.val then Fin.ofNat 7 (2 ^ r.val - 1)
  else Fin.ofNat 7 (((x.val + 1) ||| (y.val + 1)) - 1)

private theorem code_choice : ∀ r : Fin 3, ∀ A B : Value (Fin 3),
    code (Value.choice r A B) = codeChoice r (code A) (code B) := by
  decide +kernel

private def statusInput (i j : Fin 3) : Value (Fin 3) := Value.singleton (rows i j)

set_option maxRecDepth 100000 in
private theorem certified_columns : ∀ j : Fin 3, Certified (fun i => statusInput i j) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
private theorem certifiedCode_choice : ∀ x : Fin 3 → Fin 7, CertifiedCode x →
    ∀ y : Fin 3 → Fin 7, CertifiedCode y → ∀ r : Fin 3,
      CertifiedCode (fun i => codeChoice r (x i) (y i)) := by
  decide +kernel

private theorem certified_choice (r : Fin 3) (x y : Fin 3 → Value (Fin 3))
    (hx : Certified x) (hy : Certified y) :
    Certified (fun i => Value.choice r (x i) (y i)) := by
  simpa only [Certified, code_choice] using certifiedCode_choice _ hx _ hy r

private theorem status_choice (r : Fin 3) (A B : WinnerSet (Fin 3)) :
    status (WinnerSet.choice r A B) = Value.choice r (status A) (status B) := by
  apply Value.toWinner_injective
  simp only [status_toWinner, Value.toWinner_choice]

private theorem status_singleton (r : Fin 3) :
    status (WinnerSet.singleton r) = Value.singleton r := by
  apply Value.toWinner_injective
  simp only [status_toWinner, Value.toWinner_singleton]

private theorem term_certified (t : Term (Fin 3) (Fin 3)) (ht : t.IsCore) :
    Certified (fun i => status (t.eval (atomicInput i))) := by
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var j => simpa only [Term.eval, atomicInput, status_singleton, statusInput] using certified_columns j
  | choice r s t hs ht' =>
    simpa only [Term.eval, status_choice] using certified_choice r _ _ (hs ht.1) (ht' ht.2)

private def targetStatus : Fin 3 → Value (Fin 3) :=
  ![Value.union (Value.singleton 1) (Value.singleton 2),
    Value.union (Value.singleton 0) (Value.singleton 2),
    Value.union (Value.singleton 0) (Value.singleton 1)]

private theorem targetStatus_val (i : Fin 3) :
    (targetStatus i).toWinner.val = atomicOutput i := by
  fin_cases i <;> ext r <;>
    simp [targetStatus, atomicOutput, Value.toWinner_union, Value.toWinner_singleton, or_comm]

private theorem target_not_certified : ¬Certified targetStatus := by
  decide +kernel

/-- No core term realizes the joint requirement even at the three atomic rows. -/
theorem no_core_atomic_realization :
    ¬∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧
      ∀ i, (t.eval (atomicInput i)).val = atomicOutput i := by
  rintro ⟨t, ht, he⟩
  have hc := term_certified t ht
  have hh : (fun i => status (t.eval (atomicInput i))) = targetStatus := by
    funext i
    apply Value.toWinner_injective
    rw [status_toWinner]
    apply Subtype.ext
    exact (he i).trans (targetStatus_val i).symm
  exact target_not_certified (hh ▸ hc)

/-- Each observer polynomial gives the entire corresponding player view. -/
theorem sameView_of_raw (v : Fin 3 → WinnerSet (Fin 3)) (A : WinnerSet (Fin 3))
    (hA : A.val = raw v) (r : Fin 3) :
    WinnerSet.SameView r A ((observerTerm r).eval v) := by
  constructor
  · rw [hA, eval_observerTerm]
    rfl
  · intro k _
    rw [eval_observerTerm, observer_eq_singleton_iff]
    rw [Subtype.ext_iff, hA]
    exact raw_eq_singleton_iff v k

/-- Complete view realizability by separate core terms does not imply a common
core realization: failure is already visible on three singleton-input rows. -/
theorem exists_amalgamation_failure :
    ∃ F : (Fin 3 → WinnerSet (Fin 3)) → WinnerSet (Fin 3),
      (∀ v, (F v).val = raw v) ∧
      (∀ v r, F v = WinnerSet.singleton r ↔ ∀ j, v j = WinnerSet.singleton r) ∧
      (∀ r : Fin 3, ∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧ ∀ v,
        WinnerSet.view r (F v) = WinnerSet.view r (t.eval v)) ∧
      ¬∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧
        ∀ i, t.eval (atomicInput i) = F (atomicInput i) := by
  let F (v : Fin 3 → WinnerSet (Fin 3)) : WinnerSet (Fin 3) :=
    ⟨raw v, raw_nonempty v⟩
  refine ⟨F, fun _ => rfl, ?_, ?_, ?_⟩
  · intro v r
    rw [Subtype.ext_iff]
    exact raw_eq_singleton_iff v r
  · intro r
    refine ⟨observerTerm r, observerTerm_isCore r, fun v => ?_⟩
    exact (WinnerSet.view_eq_view_iff r _ _).mpr (sameView_of_raw v (F v) rfl r)
  · rintro ⟨t, ht, he⟩
    apply no_core_atomic_realization
    exact ⟨t, ht, fun i => (congrArg Subtype.val (he i)).trans (raw_atomicInput i)⟩

end KFOL.Core.AtomicAmalgamation
