module

public import KFOL.Core.IntervalCompletion
public import KFOL.Core.AtomicObserver

/-! # Recognition by the interval preorder

The full winner-valued interval operation is a core operation exactly when
its selected interior intervals are saturated under the generated preorder.
-/

@[expose] public section
namespace KFOL.Core.Intervals
universe u v
variable {Role : Type u} {Var : Type v} [Fintype Var]

/-- Boolean cuts constant on the generators preserve the interval preorder. -/
theorem Good.le_of_reach {selected : Set (Finset Var × Finset Var)}
    {φ : Finset Var → Bool} (hφ : Good selected φ) {S T : Finset Var}
    (h : Reach selected S T) : φ S ≤ φ T := by
  induction h with
  | refl => exact le_rfl
  | @tail T U hST hTU ih =>
    apply ih.trans
    rcases hTU with hinc | hsel
    · exact hφ.mono hinc
    · exact le_of_eq (hφ.edge U T hsel).symm

private theorem reach_empty {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) {S T : Finset Var} (h : Reach selected S T)
    (hT : T = ∅) : S = ∅ := by
  induction h with
  | refl => exact hT
  | @tail T U hST hTU ih =>
    subst U
    rcases hTU with hinc | hsel
    · exact ih (Finset.subset_empty.mp hinc)
    · exact ((hp ∅ T hsel).1.ne_empty rfl).elim

private theorem reach_from_univ {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) {T : Finset Var}
    (h : Reach selected Finset.univ T) : T = Finset.univ := by
  induction h with
  | refl => rfl
  | @tail T U hST hTU ih =>
    rcases hTU with hinc | hsel
    · exact Finset.Subset.antisymm (Finset.subset_univ _) (ih ▸ hinc)
    · exact ((hp U T hsel).2.2 ih).elim

/-- The principal upset of an uncollapsed interval is a normalized separator. -/
theorem separates_of_not_reach {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) {L U : Finset Var} (hLU : L ⊂ U)
    (hn : ¬Reach selected U L) : Separates selected L U := by
  classical
  let φ (S : Finset Var) : Bool := decide (Reach selected U S)
  have hmono : Monotone φ := by
    intro S T hST
    apply Bool.le_iff_imp.mpr
    intro hS
    have hUS : Reach selected U S := by simpa [φ] using hS
    have hUT : Reach selected U T := hUS.tail (Or.inl hST)
    simpa [φ] using hUT
  have hbot : φ ∅ = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have he := reach_empty hp (of_decide_eq_true hh) rfl
    have : L = U := Finset.Subset.antisymm
      (Finset.ssubset_iff_subset_ne.mp hLU).1 (by simp [he])
    exact (Finset.ssubset_iff_subset_ne.mp hLU).2 this
  have htop : φ Finset.univ = true := by
    apply decide_eq_true
    exact Relation.ReflTransGen.single (Or.inl (Finset.subset_univ _))
  refine ⟨φ,⟨hmono,hbot,htop,?_⟩,?_,?_⟩
  · intro S T hsel
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hS
      have hUS : Reach selected U S := by simpa [φ] using hS
      have hUT := hUS.tail (Or.inl (Finset.ssubset_iff_subset_ne.mp (hp S T hsel).2.1).1)
      change decide (Reach selected U T) = true
      exact decide_eq_true hUT
    · intro hT
      have hUT : Reach selected U T := by simpa [φ] using hT
      have hUS := hUT.tail (Or.inr hsel)
      change decide (Reach selected U S) = true
      exact decide_eq_true hUS
  · simpa [φ] using hn
  · simp [φ,Reach,Relation.ReflTransGen.refl]

/-- Saturation provides all Boolean cuts needed for full-menu completion. -/
theorem separates_of_saturated {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) (hs : Saturated selected)
    {L U : Finset Var} (hLU : L ⊂ U) (hm : (L,U) ∉ selected) :
    Separates selected L U := by
  apply separates_of_not_reach hp hLU
  intro hr
  by_cases hL : L.Nonempty
  · by_cases hU : U = Finset.univ
    · have he := reach_from_univ hp (hU ▸ hr)
      exact (Finset.ssubset_iff_subset_ne.mp hLU).2 (he.trans hU.symm)
    · exact hm (hs L U ⟨hL,hLU,hU⟩ hr)
  · have hLe : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    have hUe := reach_empty hp hr hLe
    exact (Finset.ssubset_iff_subset_ne.mp hLU).2 (hLe.trans hUe.symm)

private theorem atomic_lower (three : Fin 3 ↪ Role) (L U : Finset Var) :
    lowerInputs (three 2) (AtomicObserver.values three L U) = L := by
  classical
  ext j
  by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
    simp [lowerInputs,AtomicObserver.values,hL,hU,three.injective.eq_iff]

private theorem atomic_upper (three : Fin 3 ↪ Role) (L U : Finset Var)
    (hLU : L ⊆ U) :
    upperInputs (three 1) (AtomicObserver.values three L U) = U := by
  classical
  ext j
  have hj : j ∈ L → j ∈ U := fun h => hLU h
  by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
    simp_all [upperInputs,AtomicObserver.values,three.injective.eq_iff]

/-- The mask's atomic observer trace is exactly its unselected strict intervals. -/
theorem atomic_mem_operation [Nonempty Var] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (L U : Finset Var) (hLU : L ⊆ U) :
    three 0 ∈ (operation (three 1) (three 2) selected
      (AtomicObserver.values three L U)).val ↔ L ⊂ U ∧ (L,U) ∉ selected := by
  classical
  rw [operation,atomic_lower,atomic_upper three L U hLU]
  split_ifs with hm
  · simp [WinnerSet.union,three.injective.eq_iff,hm]
  · simp only [inputUnion,Set.mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      have hfree : j ∈ U ∧ j ∉ L := by
        by_cases hjL : j ∈ L <;> by_cases hjU : j ∈ U <;>
          simp_all [AtomicObserver.values,three.injective.eq_iff]
      refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hLU,?_⟩,hm⟩
      intro he
      exact hfree.2 (he ▸ hfree.1)
    · rintro ⟨hs,_⟩
      have hn : ¬U ⊆ L := fun hh => (Finset.ssubset_iff_subset_ne.mp hs).2
        (Finset.Subset.antisymm hLU hh)
      obtain ⟨j,hjU,hjL⟩ := Finset.not_subset.mp hn
      exact ⟨j,by simp [AtomicObserver.values,hjL,hjU]⟩

/-- A full-menu core realizer forces closure under all interval paths. -/
theorem saturated_of_realizes [Nonempty Var] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected)
    (t : Term Role Var) (ht : t.IsCore)
    (he : ∀ values, t.eval values = operation (three 1) (three 2) selected values) :
    Saturated selected := by
  let h (L U : Finset Var) : Prop := L ⊂ U ∧ (L,U) ∉ selected
  have ha : AtomicObserver.Admissible h :=
    (AtomicObserver.admissible_iff_embedding three h).mpr
      ⟨t,ht,fun L U hLU => by rw [he]; exact (atomic_mem_operation three selected L U hLU).symm⟩
  have hmap_all {A B : Finset Var} (hr : Reach selected A B) :
      AtomicObserver.Reach h A B := by
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail T V hUT hTV ih =>
      apply ih.tail
      rcases hTV with hinc | hsel
      · exact Or.inl hinc
      · exact Or.inr ⟨(Finset.ssubset_iff_subset_ne.mp (hp V T hsel).2.1).1,
          fun hh => hh.2 hsel⟩
  intro L U hI hr
  by_contra hm
  exact ha.2 L U (Finset.ssubset_iff_subset_ne.mp hI.2.1).1 ⟨hI.2.1,hm⟩ (hmap_all hr)

/-- Direct recognition of the interval-mask fragment on all winner menus. -/
theorem saturated_iff_exists_term [Fintype Role] [Nonempty Var]
    (three : Fin 3 ↪ Role) (selected : Set (Finset Var × Finset Var))
    (hp : Proper selected) :
    Saturated selected ↔ ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = operation (three 1) (three 2) selected values := by
  constructor
  · intro hs
    exact exists_completion three selected hp (fun _ _ hLU hm =>
      separates_of_saturated hp hs hLU hm)
  · rintro ⟨t,ht,he⟩
    exact saturated_of_realizes three selected hp t ht he

/-- Saturation adds only proper interior intervals. -/
theorem proper_saturation (selected : Set (Finset Var × Finset Var)) :
    Proper (saturation selected) := fun _ _ h => h.1

/-- Every selected interval belongs to its saturation. -/
theorem subset_saturation {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) : selected ⊆ saturation selected := by
  intro p hp'
  exact ⟨hp p.1 p.2 hp',Relation.ReflTransGen.single (Or.inr hp')⟩

omit [Fintype Var] in
private theorem reach_mono {selected other : Set (Finset Var × Finset Var)}
    (hsub : selected ⊆ other) {S T : Finset Var} (hr : Reach selected S T) :
    Reach other S T := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    rcases hedge with hinc | hsel
    · exact ih.tail (Or.inl hinc)
    · exact ih.tail (Or.inr (hsub hsel))

private theorem reach_of_saturation {selected : Set (Finset Var × Finset Var)}
    {S T : Finset Var} (hr : Reach (saturation selected) S T) :
    Reach selected S T := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    rcases hedge with hinc | hsat
    · exact ih.tail (Or.inl hinc)
    · exact ih.trans hsat.2

/-- The path closure is itself saturated. -/
theorem saturated_saturation (selected : Set (Finset Var × Finset Var)) :
    Saturated (saturation selected) := fun _ _ hI hr => ⟨hI,reach_of_saturation hr⟩

/-- Saturation is the least path-closed family containing the selected intervals. -/
theorem saturation_subset {selected other : Set (Finset Var × Finset Var)}
    (hsub : selected ⊆ other) (hs : Saturated other) : saturation selected ⊆ other := by
  intro p hp
  exact hs p.1 p.2 hp.1 (reach_mono hsub hp.2)

/-- Saturated proper families are exactly the fixed points of path closure. -/
theorem saturated_iff_saturation_eq {selected : Set (Finset Var × Finset Var)}
    (hp : Proper selected) : Saturated selected ↔ saturation selected = selected := by
  constructor
  · intro hs
    exact Set.Subset.antisymm (saturation_subset Set.Subset.rfl hs) (subset_saturation hp)
  · intro he
    rw [← he]
    exact saturated_saturation selected

/-- Saturating an interval family always gives a full-menu core operation. -/
theorem exists_saturation_term [Fintype Role] [Nonempty Var]
    (three : Fin 3 ↪ Role) (selected : Set (Finset Var × Finset Var)) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = operation (three 1) (three 2) (saturation selected) values :=
  (saturated_iff_exists_term three _ (proper_saturation selected)).mp
    (saturated_saturation selected)

/-- Path-saturated mask families are closed under intersection. -/
theorem Saturated.inter {selected other : Set (Finset Var × Finset Var)}
    (hs : Saturated selected) (ho : Saturated other) : Saturated (selected ∩ other) := by
  intro L U hI hr
  exact ⟨hs L U hI (reach_mono (fun _ h => h.1) hr),
    ho L U hI (reach_mono (fun _ h => h.2) hr)⟩

end KFOL.Core.Intervals
