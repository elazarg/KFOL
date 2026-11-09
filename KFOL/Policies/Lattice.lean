module

public import KFOL.Policies.Basic

/-! Policy lattice operations, endpoints, joint-test absorption and markers.
These identities hold on the shared nonempty winner-set carrier. -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

/-- Passing stronger blocking sets implies passing weaker ones. -/
theorem policyPasses_antitone (D E : Set Role) (hDE : D ⊆ E) (k : Role) (Y : WinnerSet Role) :
    PolicyPasses E k Y → PolicyPasses D k Y := fun h r hr => h r (hDE hr)

@[simp] theorem policyPasses_union (D E : Set Role) (k : Role) (Y : WinnerSet Role) :
    PolicyPasses (D ∪ E) k Y ↔ PolicyPasses D k Y ∧ PolicyPasses E k Y := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨hd, he⟩ r (hr | hr)
    · exact hd r hr
    · exact he r hr

@[simp] theorem policyPasses_inter (D E : Set Role) (k : Role) (Y : WinnerSet Role) :
    PolicyPasses (D ∩ E) k Y ↔ PolicyPasses D k Y ∨ PolicyPasses E k Y := by
  classical
  by_cases hm : Y.Ambiguous
  · exact ⟨fun _ => Or.inl (policyPasses_of_ambiguous D k Y hm),
      fun _ => policyPasses_of_ambiguous (D ∩ E) k Y hm⟩
  · unfold Ambiguous at hm
    push Not at hm
    obtain ⟨r, rfl⟩ := hm
    simp only [policyPasses_singleton, Set.mem_inter_iff]
    tauto

@[simp] theorem policyPasses_empty (k : Role) (Y : WinnerSet Role) : PolicyPasses ∅ k Y :=
  fun _ h => False.elim h

/-- The only nonambiguous value passing all other atoms is the marker's atom. -/
theorem policyPasses_univ (k : Role) (Y : WinnerSet Role) :
    PolicyPasses Set.univ k Y ↔ Y.Ambiguous ∨ k ∈ Y.val := by
  classical
  constructor
  · intro h
    by_cases hm : Y.Ambiguous
    · exact Or.inl hm
    · unfold Ambiguous at hm
      push Not at hm
      obtain ⟨r, hY⟩ := hm
      have hr : r = k := by
        rw [hY, policyPasses_singleton] at h
        exact h.resolve_left (fun hn => hn (Set.mem_univ _))
      right
      rw [hY, hr]
      rfl
  · rintro (hm | hk)
    · exact policyPasses_of_ambiguous _ _ _ hm
    · exact policyPasses_of_mem _ _ _ hk

/-- Any blocking universe covering every other atom has exactly the joint
passing test needed by collision normalization. The observer itself is harmless. -/
theorem policyPasses_observer_cover (D : Set Role) (k : Role) (Y : WinnerSet Role)
    (hcover : D ∪ {k} = Set.univ) : PolicyPasses D k Y ↔ Y.Ambiguous ∨ k ∈ Y.val := by
  have hs : PolicyPasses {k} k Y := by
    intro r hr hne
    exact False.elim (hne (Set.mem_singleton_iff.mp hr))
  have h := policyPasses_union D {k} k Y
  rw [hcover, policyPasses_univ] at h
  exact ⟨fun hd => h.mpr ⟨hd, hs⟩, fun hm => (h.mp hm).1⟩

/-- Removing the observer from a policy preserves its passing predicate. -/
theorem policyPasses_diff_observer (D : Set Role) (k : Role) (Y : WinnerSet Role) :
    PolicyPasses (D \ {k}) k Y ↔ PolicyPasses D k Y := by
  constructor
  · intro h r hr hrk
    exact h r ⟨hr, hrk⟩ hrk
  · intro h r hr
    exact h r hr.1

/-- Every finite union/intersection of fixed policies is natively definable. -/
theorem policyReset_union (D E : Set Role) (X Y Z : WinnerSet Role) :
    policyReset (D ∪ E) X Y Z = policyReset D X Y (policyReset E X Y Z) := by
  apply Subtype.ext
  ext k
  simp only [mem_policyReset, policyPasses_union]
  tauto

theorem policyReset_inter (D E : Set Role) (X Y Z : WinnerSet Role) :
    policyReset (D ∩ E) X Y Z = (policyReset D X Y Z).reset (policyReset E X Y Z) := by
  apply Subtype.ext
  ext k
  simp only [mem_policyReset, policyPasses_inter, mem_reset, ambiguous_policyReset]
  tauto

/-- Endpoint policies require no additional operation beyond reset. -/
theorem policyReset_empty (X Y Z : WinnerSet Role) :
    policyReset ∅ X Y Z = (Y.reset X).reset (Z.reset X) := by
  apply Subtype.ext
  ext k
  simp only [mem_policyReset, policyPasses_empty, true_and, mem_reset, ambiguous_reset]
  tauto

theorem policyReset_univ (X Y Z : WinnerSet Role) :
    policyReset Set.univ X Y Z = (Z.reset Y).reset X := by
  apply Subtype.ext
  ext k
  simp only [mem_policyReset, policyPasses_univ, mem_reset]
  tauto

/-- Replacing a collision by ambiguity is valid for the whole list once
its input's unguarded root contribution is also present. -/
theorem policy_joint_absorption (D E : Set Role) (hcover : D ∪ E = Set.univ)
    (k : Role) (Y : WinnerSet Role) (Q : Prop) :
    (k ∈ Y.val ∨ (Q ∧ PolicyPasses D k Y ∧ PolicyPasses E k Y)) ↔
      k ∈ Y.val ∨ (Q ∧ Y.Ambiguous) := by
  have h := policyPasses_union D E k Y
  rw [hcover, policyPasses_univ] at h
  tauto

/-- Outside a known baseline only the continuation can contribute a marker. -/
theorem policyReset_marker (D : Set Role) (X Y Z W : WinnerSet Role) (k : Role)
    (hX : X.Ambiguous) (hXW : X.val ⊆ W.val) (hYW : Y.val ⊆ W.val) (hw : k ∉ W.val) :
    k ∈ (policyReset D X Y Z).val ↔ PolicyPasses D k Y ∧ k ∈ Z.val := by
  have hx : k ∉ X.val := fun h => hw (hXW h)
  have hy : k ∉ Y.val := fun h => hw (hYW h)
  simp only [mem_policyReset, hx, hy, hX, false_or, true_and]

end KFOL.WinnerSet
