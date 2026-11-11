module

public import KFOL.Definitions.CoreNormalForm
public import KFOL.Algebra.Views
public import KFOL.Algebra.PublicContexts
public import KFOL.Algebra.Monotone

/-! # Sourcewise linearity of possible-winner membership -/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

@[simp] theorem passive_eq_atom_iff (k : Role) (A : WinnerSet Role)
    (r : {r : Role // r ≠ k}) : passive k A = .atom r ↔ A = WinnerSet.singleton r.val := by
  rw [← WinnerSet.view_eq_other_iff k A r]
  unfold passive
  cases WinnerSet.view k A <;> simp

@[simp] theorem representative_omits (three : Fin 3 ↪ Role) (k : Role) (p : Passive k) :
    k ∉ (representative three k p).val := by
  cases p with
  | atom r => exact fun h => r.property h.symm
  | neutral => exact fun h => h rfl

@[simp] theorem representative_atom_iff (three : Fin 3 ↪ Role) (k : Role)
    (p : Passive k) (r : {r : Role // r ≠ k}) :
    representative three k p = WinnerSet.singleton r.val ↔ p = .atom r := by
  have hv := PlayerView.view_representative three k PlayerView.impossible
  cases p with
  | atom s => simp [representative, Subtype.ext_iff]
  | neutral =>
    have hn : PlayerView.representative three k .impossible ≠ WinnerSet.singleton r.val := by
      intro he
      have h := (WinnerSet.view_eq_other_iff k _ r).mpr he
      rw [hv] at h
      cases h
    simp [representative, hn]

@[simp] theorem passive_representative (three : Fin 3 ↪ Role) (k : Role) (p : Passive k) :
    passive k (representative three k p) = p := by
  cases p with
  | atom r => exact (passive_eq_atom_iff _ _ _).mpr rfl
  | neutral =>
    cases h : passive k (representative three k .neutral) with
    | neutral => rfl
    | atom r =>
      have he := (passive_eq_atom_iff _ _ _).mp h
      have hp := (representative_atom_iff three k .neutral r).mp he
      cases hp

@[simp] theorem probe_source (three : Fin 3 ↪ Role) (k : Role) (j : Var) (p : Pattern k j) :
    probe three k j p j = WinnerSet.singleton k := by
  classical
  simp [probe]

@[simp] theorem probe_other (three : Fin 3 ↪ Role) (k : Role) (j : Var) (p : Pattern k j)
    (i : Var) (hi : i ≠ j) : probe three k j p i = representative three k (p ⟨i, hi⟩) := by
  classical
  simp [probe, hi]

private theorem probe_tests (three : Fin 3 ↪ Role) (k : Role) (j : Var)
    (v : Var → WinnerSet Role) (hk : k ∈ (v j).val) (r : Role) (hr : r ≠ k) (i : Var) :
    v i = WinnerSet.singleton r ↔
      probe three k j (pattern k j v) i = WinnerSet.singleton r := by
  classical
  by_cases hi : i = j
  · subst i
    have hv : v j ≠ WinnerSet.singleton r := by
      intro he; rw [he] at hk; exact hr hk.symm
    simp [probe, hv, Ne.symm hr]
  · rw [probe_other three k j _ i hi]
    exact (representative_atom_iff three k _ ⟨r, hr⟩).trans
      (passive_eq_atom_iff k (v i) ⟨r, hr⟩) |>.symm

@[simp] theorem mem_probe_iff (three : Fin 3 ↪ Role) (k : Role) (j : Var)
    (p : Pattern k j) (i : Var) : k ∈ (probe three k j p i).val ↔ i = j := by
  classical
  by_cases hi : i = j
  · subst i; simp
  · simp [probe, hi]

/-- Every possible winner has one source, tested in isolation while retaining
the other inputs' nonobserver singleton tests. No finiteness is needed. -/
theorem membership_iff_source (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ (t.eval v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (t.eval (probe three k j (pattern k j v))).val := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x =>
    constructor
    · intro hx; exact ⟨x, hx, by simp [Term.eval]⟩
    · rintro ⟨j, hj, hx⟩
      by_cases hxj : x = j
      · simpa only [Term.eval, hxj] using hj
      · simp [Term.eval, probe, hxj] at hx
  | choice r s t ihs iht =>
    by_cases hr : r = k
    · subst r
      simp only [Term.eval, WinnerSet.mem_choice_owner, ihs ht.1, iht ht.2]
      constructor
      · rintro (⟨j, hj, hs⟩ | ⟨j, hj, ht⟩)
        · exact ⟨j, hj, Or.inl hs⟩
        · exact ⟨j, hj, Or.inr ht⟩
      · rintro ⟨j, hj, hs | ht⟩
        · exact Or.inl ⟨j, hj, hs⟩
        · exact Or.inr ⟨j, hj, ht⟩
    · have es (j : Var) (hj : k ∈ (v j).val) : s.eval v = WinnerSet.singleton r ↔
          s.eval (probe three k j (pattern k j v)) = WinnerSet.singleton r :=
        ht.1.isPublic.eval_singleton_iff_of_tests r _ _ (probe_tests three k j v hj r hr)
      have et (j : Var) (hj : k ∈ (v j).val) : t.eval v = WinnerSet.singleton r ↔
          t.eval (probe three k j (pattern k j v)) = WinnerSet.singleton r :=
        ht.2.isPublic.eval_singleton_iff_of_tests r _ _ (probe_tests three k j v hj r hr)
      rw [Term.eval, WinnerSet.mem_choice_other r k hr]
      constructor
      · rintro ⟨hs | ht', hns, hnt⟩
        · obtain ⟨j, hj, hs⟩ := (ihs ht.1).mp hs
          refine ⟨j, hj, ?_⟩
          exact (WinnerSet.mem_choice_other r k hr _ _).mpr
            ⟨Or.inl hs, fun h => hns ((es j hj).mpr h), fun h => hnt ((et j hj).mpr h)⟩
        · obtain ⟨j, hj, ht'⟩ := (iht ht.2).mp ht'
          refine ⟨j, hj, ?_⟩
          exact (WinnerSet.mem_choice_other r k hr _ _).mpr
            ⟨Or.inr ht', fun h => hns ((es j hj).mpr h), fun h => hnt ((et j hj).mpr h)⟩
      · rintro ⟨j, hj, h⟩
        obtain ⟨hs | ht', hns, hnt⟩ := (WinnerSet.mem_choice_other r k hr _ _).mp h
        · exact ⟨Or.inl ((ihs ht.1).mpr ⟨j, hj, hs⟩),
            fun h => hns ((es j hj).mp h), fun h => hnt ((et j hj).mp h)⟩
        · exact ⟨Or.inr ((iht ht.2).mpr ⟨j, hj, ht'⟩),
            fun h => hns ((es j hj).mp h), fun h => hnt ((et j hj).mp h)⟩

/-- Isolated membership probes determine the entire core operation. -/
theorem eq_iff_probes (three : Fin 3 ↪ Role) (s t : Term Role Var)
    (hs : s.IsCore) (ht : t.IsCore) :
    (∀ v, s.eval v = t.eval v) ↔
      ∀ (k : Role) (j : Var) (p : Pattern k j),
        (k ∈ (s.eval (probe three k j p)).val ↔ k ∈ (t.eval (probe three k j p)).val) := by
  constructor
  · intro h k j p; rw [h]
  · intro h v
    apply Subtype.ext
    ext k
    rw [membership_iff_source three s hs v k, membership_iff_source three t ht v k]
    exact exists_congr (fun j => and_congr_right (fun _ => h k j (pattern k j v)))

end KFOL.Core.Sources
