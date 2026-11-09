module

public import KFOL.Policies.Normalized

/-! Sound coverage and least atom-or-pair separating valuations for normalized
policy-family guards. The family criterion supplies the least-atom hypothesis. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

private theorem pair_ambiguous {Role : Type u} (a b : Role) (hab : a ≠ b) :
    ((WinnerSet.singleton a).union (WinnerSet.singleton b)).Ambiguous :=
  WinnerSet.ambiguous_of_two_mem _ a b hab (Or.inl rfl) (Or.inr rfl)

private theorem not_ambiguous_singleton {Role : Type u} (a : Role) :
    ¬(WinnerSet.singleton a).Ambiguous := fun h => h a rfl

namespace Guard

variable {Role : Type u} {Label : Type w} {Var : Type v} [DecidableEq Role] [DecidableEq Var]

/-- A passing label at i is contained in the accumulated blocking union at i. -/
theorem label_subset_blockingAt (D : Label → Finset Role) (g : Guard Label Var) (d : Label) (i : Var)
    (hp : (d, i) ∈ g.passes) : D d ⊆ g.blockingAt D i := by
  intro r hr
  exact (mem_blockingUnion D (g.labelsAt i) r).mpr ⟨d, (mem_labelsAt g i d).mpr hp, hr⟩

/-- Coverage implications hold at every observer, irrespective of normalization. -/
theorem dominates_sound (D : Label → Finset Role) (weak strong : Guard Label Var)
    (h : weak.Dominates D strong) (k : Role) (v : Var → WinnerSet Role)
    (hs : strong.Holds (fun i => (v i).Ambiguous)
      (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i)) (fun i => k ∈ (v i).val)) :
    weak.Holds (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
      (fun i => k ∈ (v i).val) := by
  refine ⟨fun i hi => hs.1 i (h.2.1 i hi), ?_, h.1 ▸ hs.2.2⟩
  intro p hp
  rcases h.2.2 p hp with hm | he | hsub
  · exact WinnerSet.policyPasses_of_ambiguous _ _ _ (hs.1 _ hm)
  · exact WinnerSet.policyPasses_of_mem _ _ _ (he ▸ hs.2.2)
  · exact WinnerSet.policyPasses_antitone (D p.1 : Set Role) (strong.blockingAt D p.2 : Set Role)
      hsub k (v p.2) (strong.passingAt_of_holds D k v hs p.2)

omit [DecidableEq Role] in
private theorem atomPairVal_ambiguous (k a b : Role) (hka : k ≠ a) (hab : a ≠ b)
    (atoms : Var → Role) (g : Guard Label Var) (i : Var) :
    (g.atomPairVal k a b atoms i).Ambiguous ↔ i ∈ g.many := by
  by_cases hs : i = g.source <;> by_cases hm : i ∈ g.many <;>
    simp_all [Guard.atomPairVal, pair_ambiguous, not_ambiguous_singleton]

omit [DecidableEq Role] in
private theorem atomPairVal_marker (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b)
    (atoms : Var → Role) (g : Guard Label Var)
    (hatoms : ∀ i, i ≠ g.source → i ∉ g.many → atoms i ≠ k) (i : Var) :
    k ∈ (g.atomPairVal k a b atoms i).val ↔ i = g.source := by
  by_cases hs : i = g.source
  · subst i
    by_cases hm : g.source ∈ g.many <;>
      simp [Guard.atomPairVal, hm, WinnerSet.val_union, WinnerSet.val_singleton]
  · by_cases hm : i ∈ g.many
    · simp [Guard.atomPairVal, hs, hm, WinnerSet.val_union, WinnerSet.val_singleton, hka, hkb]
    · have hk := Ne.symm (hatoms i hs hm)
      simp [Guard.atomPairVal, hs, hm, WinnerSet.val_singleton, hk]

private theorem atomPairVal_passing (D : Label → Finset Role) (k a b : Role) (hka : k ≠ a) (hab : a ≠ b)
    (atoms : Var → Role) (g : Guard Label Var)
    (hatoms : ∀ i, i ≠ g.source → i ∉ g.many → atoms i ≠ k ∧
      ∀ d, atoms i ∉ D d ↔ D d ⊆ g.blockingAt D i) (d : Label) (i : Var) :
    WinnerSet.PolicyPasses (D d : Set Role) k (g.atomPairVal k a b atoms i) ↔
      i ∈ g.many ∨ i = g.source ∨ D d ⊆ g.blockingAt D i := by
  by_cases hm : i ∈ g.many
  · exact ⟨fun _ => Or.inl hm, fun _ => WinnerSet.policyPasses_of_ambiguous _ _ _
      ((atomPairVal_ambiguous k a b hka hab atoms g i).mpr hm)⟩
  · by_cases hs : i = g.source
    · subst i
      simp [Guard.atomPairVal, hm, WinnerSet.policyPasses_singleton]
    · have hA := hatoms i hs hm
      have he : g.atomPairVal k a b atoms i = WinnerSet.singleton (atoms i) := by
        simp only [Guard.atomPairVal, hs, hm, ite_false]
      rw [he, WinnerSet.policyPasses_singleton]
      constructor
      · intro h
        exact Or.inr (Or.inr ((hA.2 d).mp (h.resolve_right hA.1)))
      · rintro (hi | hi | hsub)
        · exact False.elim (hm hi)
        · exact False.elim (hs hi)
        · exact Or.inl ((hA.2 d).mpr hsub)

/-- At the displayed valuation a guard holds exactly when it covers the
selected normalized guard. Source and ambiguity statuses are independent. -/
private theorem holds_atomPairVal_iff (D : Label → Finset Role) (k a b : Role)
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) (atoms : Var → Role) (g weak : Guard Label Var)
    (hatoms : ∀ i, i ≠ g.source → i ∉ g.many → atoms i ≠ k ∧
      ∀ d, atoms i ∉ D d ↔ D d ⊆ g.blockingAt D i) :
    weak.Holds (fun i => (g.atomPairVal k a b atoms i).Ambiguous)
      (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (g.atomPairVal k a b atoms i))
      (fun i => k ∈ (g.atomPairVal k a b atoms i).val) ↔ weak.Dominates D g := by
  simp only [Guard.Holds, atomPairVal_ambiguous k a b hka hab atoms g,
    atomPairVal_passing D k a b hka hab atoms g hatoms,
    atomPairVal_marker k a b hka hkb atoms g (fun i hi hm => (hatoms i hi hm).1), Guard.Dominates]
  tauto

/-- A normalized guard has a concrete least valuation. The selected atoms
come from the proved pattern-meet condition; the valuation itself consists
only of atoms and pairs. -/
theorem exists_least_valuation (D : Label → Finset Role) (top : Finset Role) (k a b : Role)
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) (hleast : HasLeastAtoms D top k)
    (g : Guard Label Var) (hg : g.Normalized D top) :
    ∃ v : Var → WinnerSet Role,
      (∀ weak : Guard Label Var,
        weak.Holds (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
          (fun i => k ∈ (v i).val) ↔ weak.Dominates D g) ∧
      (∀ i : Var, ∃ r s : Role, v i = (WinnerSet.singleton r).union (WinnerSet.singleton s)) := by
  classical
  let atoms : Var → Role := fun i => if hi : i ≠ g.source ∧ i ∉ g.many then
    Classical.choose (hleast (g.labelsAt i) (hg i hi.1 hi.2)) else a
  have hAtoms : ∀ i, i ≠ g.source → i ∉ g.many → atoms i ≠ k ∧
      ∀ d, atoms i ∉ D d ↔ D d ⊆ g.blockingAt D i := by
    intro i his him
    dsimp [atoms]
    rw [dite_eq_left ⟨his, him⟩]
    have hh := Classical.choose_spec (hleast (g.labelsAt i) (hg i his him))
    exact ⟨hh.1, hh.2.2⟩
  refine ⟨g.atomPairVal k a b atoms, ?_, ?_⟩
  · intro weak
    exact holds_atomPairVal_iff D k a b hka hkb hab atoms g weak hAtoms
  · intro i
    by_cases hs : i = g.source <;> by_cases hm : i ∈ g.many
    · exact ⟨k, a, by simp_all [Guard.atomPairVal]⟩
    · exact ⟨k, k, by simp_all [Guard.atomPairVal]⟩
    · exact ⟨a, b, by simp_all [Guard.atomPairVal]⟩
    · exact ⟨atoms i, atoms i, by simp_all [Guard.atomPairVal]⟩

end Guard

theorem covers_sound {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (left right : List (Guard Label Var))
    (h : Covers D left right) (k : Role) (v : Var → WinnerSet Role) :
    Eval left (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
      (fun i => k ∈ (v i).val) →
    Eval right (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
      (fun i => k ∈ (v i).val) := by
  rintro ⟨g, hg, hholds⟩
  obtain ⟨weak, hw, hdom⟩ := h g hg
  exact ⟨weak, hw, weak.dominates_sound D g hdom k v hholds⟩

/-- Complete guard comparison under the least-atom condition. The main family
criterion is connected to this condition in Policies.Patterns. -/
theorem covers_iff {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) (hleast : HasLeastAtoms D top k)
    (left right : List (Guard Label Var)) (hnormal : ∀ g ∈ left, g.Normalized D top) :
    Covers D left right ↔ ∀ v : Var → WinnerSet Role,
      Eval left (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
        (fun i => k ∈ (v i).val) →
      Eval right (fun i => (v i).Ambiguous) (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i))
        (fun i => k ∈ (v i).val) := by
  constructor
  · exact fun h v => covers_sound D left right h k v
  · intro h g hg
    obtain ⟨v, hv, _⟩ := g.exists_least_valuation D top k a b hka hkb hab hleast (hnormal g hg)
    have hself : g.Dominates D g := by
      refine ⟨rfl, (fun _ h => h), ?_⟩
      rintro ⟨d, i⟩ hp
      exact Or.inr (Or.inr (g.label_subset_blockingAt D d i hp))
    have hleft : Eval left _ _ _ := ⟨g, hg, (hv g).mpr hself⟩
    obtain ⟨weak, hw, hholds⟩ := h v hleft
    exact ⟨weak, hw, (hv weak).mp hholds⟩

end KFOL.Policies
