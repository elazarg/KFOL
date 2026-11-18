module

public import KFOL.Core.CompulsoryPruning

/-! # Substitution of pruning-compatible words in disjoint blocks

A map on variable names specifies their blocks. Each occurrence of an outer
variable is replaced by its chosen inner word. Different occurrences can be
pruned independently, so the allowed inner supports must admit binary unions.
-/

@[expose] public section
namespace KFOL.Core.CompulsoryPruning

open ProfileBudgets
variable {Role B V : Type*} [DecidableEq Role] [DecidableEq B] [DecidableEq V]

omit [DecidableEq Role] in
private theorem variables_choice {U : Type*} [DecidableEq U]
    (q : Role) (s t : CoreTerm Role U) :
    (choiceTerm q s t).varFinset = s.varFinset ∪ t.varFinset := by
  simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

omit [DecidableEq Role] [DecidableEq B] [DecidableEq V] in
private theorem subst_choice (q : Role) (s t : CoreTerm Role B) (f : B → CoreTerm Role V) :
    (choiceTerm q s t).subst f = choiceTerm q (s.subst f) (t.subst f) := by
  simp only [choiceTerm, FirstOrder.Language.Term.subst]
  congr 1
  funext i
  split <;> rfl

theorem support_subset_variables (r : Role) (t : CoreTerm Role V) {H : Finset V}
    (h : H ∈ Supports r t) : H ⊆ t.varFinset := by
  induction t using induction_choice generalizing H with
  | var x => obtain rfl := (supports_var r x H).mp h; exact Finset.Subset.rfl
  | choice q s t hs ht =>
    rw [variables_choice]
    by_cases qr : q = r
    · subst q
      obtain ⟨A,hA,C,hC,rfl⟩ := owned.mp h
      exact Finset.union_subset_union (hs hA) (ht hC)
    · rcases (foreign qr).mp h with h | h
      · exact (hs h).trans Finset.subset_union_left
      · exact (ht h).trans Finset.subset_union_right

omit [DecidableEq V] in
private theorem nonempty_slice (π : V → B) (b : B) (H : Finset V) :
    (H.filter (fun x => π x = b)).Nonempty ↔ b ∈ H.image π := by
  rw [Finset.filter_nonempty_iff, Finset.mem_image]

/-- A support of the substituted term projects to an actual outer pruning.
Within each visited block its slice belongs to any binary-union-closed
family containing the inner pruning supports at that occurrence. -/
theorem supports_substitution (π : V → B) (r : Role) (inner : B → Finset V → Prop)
    (closed : ∀ b A C, A.Nonempty → C.Nonempty → inner b A → inner b C → inner b (A ∪ C))
    (t : CoreTerm Role B) (f : B → CoreTerm Role V)
    (local_ok : ∀ b ∈ t.varFinset, ∀ A ∈ Supports r (f b),
      (∀ x ∈ A, π x = b) ∧ inner b A) {H : Finset V} (h : H ∈ Supports r (t.subst f)) :
    H.image π ∈ Supports r t ∧
      ∀ b ∈ H.image π, inner b (H.filter (fun x => π x = b)) := by
  induction t using induction_choice generalizing H with
  | var b =>
    obtain ⟨fiber,good⟩ := local_ok b (Finset.mem_singleton_self _) H h
    have im : H.image π = {b} := by
      ext c
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact fiber x hx
      · rintro rfl
        obtain ⟨x,hx⟩ := support_nonempty r (f c) h
        exact ⟨x,hx,fiber x hx⟩
    refine ⟨im, ?_⟩
    intro c hc
    obtain rfl : c = b := Finset.mem_singleton.mp (im ▸ hc)
    simpa only [Finset.filter_true_of_mem fiber] using good
  | choice q s t hs ht =>
    rw [variables_choice] at local_ok
    rw [subst_choice] at h
    have ls (b) (hb : b ∈ s.varFinset) := local_ok b (Finset.mem_union_left _ hb)
    have lt (b) (hb : b ∈ t.varFinset) := local_ok b (Finset.mem_union_right _ hb)
    by_cases qr : q = r
    · subst q
      obtain ⟨A,hA,C,hC,rfl⟩ := owned.mp h
      obtain ⟨projA,legalA⟩ := hs ls hA
      obtain ⟨projC,legalC⟩ := ht lt hC
      rw [Finset.image_union]
      refine ⟨owned.mpr ⟨_,projA,_,projC,rfl⟩, ?_⟩
      intro b hb
      rw [Finset.filter_union]
      by_cases a : b ∈ A.image π
      · by_cases c : b ∈ C.image π
        · exact closed b _ _ ((nonempty_slice π b A).mpr a) ((nonempty_slice π b C).mpr c)
            (legalA b a) (legalC b c)
        · rw [Finset.not_nonempty_iff_eq_empty.mp (fun h => c ((nonempty_slice π b C).mp h)),
            Finset.union_empty]
          exact legalA b a
      · rw [Finset.not_nonempty_iff_eq_empty.mp (fun h => a ((nonempty_slice π b A).mp h)),
          Finset.empty_union]
        exact legalC b ((Finset.mem_union.mp hb).resolve_left a)
    · rcases (foreign qr).mp h with h | h
      · obtain ⟨proj,legal⟩ := hs ls h
        exact ⟨(foreign qr).mpr (Or.inl proj),legal⟩
      · obtain ⟨proj,legal⟩ := ht lt h
        exact ⟨(foreign qr).mpr (Or.inr proj),legal⟩

omit [DecidableEq Role] in
private theorem subst_variables (t : CoreTerm Role B) (f : B → CoreTerm Role V) (W : Set V)
    (ok : ∀ b ∈ t.varFinset, ((f b).varFinset : Set V) ⊆ W) :
    ((t.subst f).varFinset : Set V) ⊆ W := by
  induction t using induction_choice with
  | var b => exact ok b (Finset.mem_singleton_self _)
  | choice q s t hs ht =>
    rw [variables_choice] at ok
    rw [subst_choice, variables_choice, Finset.coe_union]
    exact Set.union_subset (hs (fun b h => ok b (Finset.mem_union_left _ h)))
      (ht (fun b h => ok b (Finset.mem_union_right _ h)))

omit [DecidableEq Role] in
private theorem variables_nonempty (t : CoreTerm Role B) : t.varFinset.Nonempty := by
  induction t using induction_choice with
  | var b => exact Finset.singleton_nonempty b
  | choice q s t hs _ => exact variables_choice q s t ▸ hs.mono Finset.subset_union_left

/-- Substitute feasible words for the visited blocks of a feasible outer word.
Only the inner families require closure under unions of nonempty supports.
Unused blocks may have no available variable or feasible word. -/
theorem feasibleOn_substitution (π : V → B) (W : Set V) (outer : Role → Finset B → Prop)
    (inner : B → Role → Finset V → Prop)
    (closed : ∀ b r A C, A.Nonempty → C.Nonempty →
      inner b r A → inner b r C → inner b r (A ∪ C))
    (feasible : FeasibleOn {b | FeasibleOn {x | x ∈ W ∧ π x = b} (inner b)} outer) :
    FeasibleOn W (fun r H => outer r (H.image π) ∧
      ∀ b ∈ H.image π, inner b r (H.filter (fun x => π x = b))) := by
  classical
  obtain ⟨t,available,good⟩ := feasible
  obtain ⟨b₀,h₀⟩ := variables_nonempty t
  obtain ⟨defaultWord,_,_⟩ := available h₀
  let f (b : B) := if hb : b ∈ t.varFinset then Classical.choose (available hb) else defaultWord
  have spec (b : B) (hb : b ∈ t.varFinset) :
      (∀ x ∈ (f b).varFinset, x ∈ W ∧ π x = b) ∧
      ∀ r H, H ∈ Supports r (f b) → inner b r H := by
    simp only [f, dite_eq_left hb]
    have h := Classical.choose_spec (available hb)
    exact ⟨fun _ hx => h.1 hx, h.2⟩
  refine ⟨t.subst f, subst_variables t f W (fun b hb x hx => ((spec b hb).1 x hx).1), ?_⟩
  intro r H h
  obtain ⟨proj,legal⟩ := supports_substitution π r (fun b => inner b r)
    (fun b => closed b r) t f (fun b hb A hA => ⟨fun x hx =>
      ((spec b hb).1 x (support_subset_variables r (f b) hA hx)).2, (spec b hb).2 r A hA⟩) h
  exact ⟨good r _ proj,legal⟩

end KFOL.Core.CompulsoryPruning
