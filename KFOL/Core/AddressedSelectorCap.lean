module

public import KFOL.Core.ProfilePruning

/-! # Capping a retained selector and then eliminating it

The selector is `none` and the internal inputs are `some i`. The cap depends
only on the internal singleton flags. -/

@[expose] public section

namespace KFOL.Core.AddressedSelectorCap

open scoped Classical

variable {Role Var : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

abbrev Word (Role Var : Type*) := Equational.Term (Equational.CoreSymbol Role) Var

private theorem profile_subst {Label : Type*} (c : Role) (flags : Var → Bool)
    (helper : Label → Word Role Var) (outer : Word Role Label) :
    profile c flags (outer.subst helper) = profile c (fun f => profile c flags (helper f)) outer := by
  induction outer using induction_choice with
  | var => rfl
  | choice q x y hx hy =>
    change profile c flags (choiceTerm q (x.subst helper) (y.subst helper)) = _
    rw [profile_choice, profile_choice, hx, hy]

/-- When the outer word uses every label and has no gate at the cap owner,
substituting the addressed folds gives exactly one positive clause per address. -/
theorem profile_of_address_folds {Label : Type*} [DecidableEq Label] (c : Role)
    (first : Label → Var) (rest : Label → List Var) (outer : Word Role Label)
    (foreign : OwnersIn (· ≠ c) outer) (uses : ∀ f, f ∈ outer.varFinset) (flags : Var → Bool) :
    profile c flags (outer.subst (fun f =>
      foldTerm c ((rest f).map .var) (.var (first f)))) = true ↔
      ∀ f, flags (first f) = true ∨ ∃ i ∈ rest f, flags i = true := by
  rw [profile_subst, profile_iff_forall_mem_varFinset_of_ownersIn c outer foreign]
  simp only [uses, forall_const, profile_fold_owner, profile_var, List.mem_map,
    exists_exists_and_eq_and, profile_var]

/-- The baseline is reset exactly when the specified internal flags pass. -/
noncomputable def target (c : Role) (ψ : (Var → Bool) → Bool)
    (base : WinnerSet Role → (Var → WinnerSet Role) → WinnerSet Role)
    (z : WinnerSet Role) (v : Var → WinnerSet Role) : WinnerSet Role :=
  if ψ (fun i => decide (v i = WinnerSet.singleton c)) then WinnerSet.singleton c else base z v

/-- A bounded internal word with the prescribed cap profile realizes the
reset by a single owned choice with a word for the baseline. -/
theorem attach (c : Role) (ψ : (Var → Bool) → Bool)
    (base : WinnerSet Role → (Var → WinnerSet Role) → WinnerSet Role)
    (b : Word Role (Option Var)) (g : Word Role Var)
    (baseline : ∀ z v, b.realize (fun j => j.elim z v) = base z v)
    (bounded : ∀ z v, (g.realize v).val ⊆ (base z v).val)
    (cap : ∀ A, profile c A g = ψ A) (z : WinnerSet Role) (v : Var → WinnerSet Role) :
    (choiceTerm c b (g.relabel some)).realize (fun j => j.elim z v) = target c ψ base z v := by
  classical
  change WinnerSet.choice c (b.realize _) ((g.relabel some).realize _) = _
  rw [baseline, FirstOrder.Language.Term.realize_relabel]
  change WinnerSet.choice c (base z v) (g.realize v) = _
  have atom := (winnerSet_eq_singleton_iff_profile g c v).trans (by rw [cap])
  unfold target
  split_ifs with h
  · exact (WinnerSet.choice_eq_owner_iff _ _ c).mpr (Or.inr (atom.mpr h))
  · by_cases single : base z v = WinnerSet.singleton c
    · rw [single]
      exact (WinnerSet.choice_eq_owner_iff _ _ c).mpr (Or.inl rfl)
    · rw [WinnerSet.choice, ite_eq_right (not_or.mpr ⟨single, fun he => h (atom.mp he)⟩)]
      exact Subtype.ext (Set.union_eq_left.mpr (bounded z v))

/-- Eliminating the selector preserves the cap profile on internal inputs.
At every non-cap selector value it also preserves all omissions of observers
other than the cap owner, and every baseline singleton outside the cap. -/
theorem extract (c r : Role) (different : r ≠ c) (ψ : (Var → Bool) → Bool)
    (top : ψ (fun _ => true) = true)
    (base : WinnerSet Role → (Var → WinnerSet Role) → WinnerSet Role)
    (retain : ∀ z v, z.val ⊆ (base z v).val)
    (t : Word Role (Option Var))
    (realizes : ∀ z v, t.realize (fun j => j.elim z v) = target c ψ base z v) :
    ∃ g : Word Role Var, (∀ A, profile c A g = ψ A) ∧
      ∀ (z : WinnerSet Role) (v : Var → WinnerSet Role), z ≠ WinnerSet.singleton c →
        (∀ k, k ≠ c → k ∉ (base z v).val → k ∉ (g.realize v).val) ∧
        (ψ (fun i => decide (v i = WinnerSet.singleton c)) = false →
          ∀ k, base z v = WinnerSet.singleton k → g.realize v = WinnerSet.singleton k) := by
  classical
  let A : Option Var → Bool := Option.isSome
  let internals : Var → WinnerSet Role := fun _ => WinnerSet.singleton c
  let start (j : Option Var) := j.elim (WinnerSet.singleton r) internals
  have startFlags : (fun j => decide (start j = WinnerSet.singleton c)) = A := by
    funext j
    cases j <;> simp [A, start, internals, different, WinnerSet.singleton_inj]
  have baseWin : t.realize start = WinnerSet.singleton c := by
    rw [show t.realize start = _ from realizes (WinnerSet.singleton r) internals]
    simp [target, internals, top]
  have test : profile c A t = true := by
    rw [← startFlags]
    exact (winnerSet_eq_singleton_iff_profile t c start).mp baseWin
  obtain ⟨u,hu⟩ := exists_below_preserving_profile c A t test
  let internal (i : {j : Option Var // A j = true}) : Var := i.val.get i.property
  let g := u.relabel internal
  have smaller (z : WinnerSet Role) (v : Var → WinnerSet Role) (hz : z ≠ WinnerSet.singleton c) :
      (g.realize v).val ⊆ (target c ψ base z v).val ∧
        (g.realize v = WinnerSet.singleton c ↔ target c ψ base z v = WinnerSet.singleton c) := by
    let row (j : Option Var) := j.elim z v
    have pass (j : Option Var) (hc : row j = WinnerSet.singleton c) : A j = true := by
      cases j with
      | none => exact (hz hc).elim
      | some => rfl
    have safe := hu row pass
    have same : g.realize v = u.realize (fun j => row j.val) := by
      rw [show g = u.relabel internal from rfl, FirstOrder.Language.Term.realize_relabel]
      congr 1
      funext i
      obtain ⟨_ | j,hi⟩ := i
      · cases hi
      · rfl
    rw [same, ← realizes z v]
    exact safe
  have noncap : WinnerSet.singleton r ≠ WinnerSet.singleton c :=
    fun eq => different (WinnerSet.singleton_inj.mp eq)
  refine ⟨g, ?_, ?_⟩
  · intro B
    let v (i : Var) := if B i then WinnerSet.singleton c else WinnerSet.singleton r
    have bits : (fun i => decide (v i = WinnerSet.singleton c)) = B := by
      funext i
      cases h : B i <;> simp [v, h, noncap]
    have never : base (WinnerSet.singleton r) v ≠ WinnerSet.singleton c := by
      intro eq
      have member := retain (WinnerSet.singleton r) v (show r ∈ (WinnerSet.singleton r).val from rfl)
      exact different (by simpa [eq] using member)
    have same := (smaller (WinnerSet.singleton r) v noncap).2
    rw [winnerSet_eq_singleton_iff_profile, bits, target, bits] at same
    cases h : ψ B <;> simp_all
  · intro z v hz
    constructor
    · intro k hk quiet hit
      have membership := (smaller z v hz).1 hit
      unfold target at membership
      split_ifs at membership
      · exact hk (by simpa using membership)
      · exact quiet membership
    · intro outside k atom
      apply WinnerSet.eq_singleton_of_subset
      simpa only [target, outside, Bool.false_eq_true, ite_false, atom, WinnerSet.val_singleton]
        using (smaller z v hz).1

end KFOL.Core.AddressedSelectorCap
