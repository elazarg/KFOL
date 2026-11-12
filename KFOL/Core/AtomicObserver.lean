module

public import KFOL.Definitions.AtomicObserver
public import KFOL.Core.CyclicPersistence
public import KFOL.Core.CrownPatch

/-! # Closed recognition of atomic observer tables

Zero intervals and set inclusions determine a canonical directed graph.
A table is realizable exactly when this graph separates its positive intervals.
This concerns one observer on atomic three-role inputs, not full source guards.
-/

@[expose] public section
namespace KFOL.Core.AtomicObserver

open WinnerSet
universe u
variable {Var : Type u} [Fintype Var]

omit [Fintype Var] in
private theorem preserves_reach (h : Finset Var → Finset Var → Prop)
    (φ : Finset Var → Bool) (hmono : Monotone φ)
    (hz : ∀ L U, L ⊆ U → ¬h L U → φ L = φ U)
    {S T : Finset Var} (hr : Reach h S T) : φ S ≤ φ T := by
  induction hr with
  | refl => exact le_rfl
  | @tail T U hST hTU ih =>
    apply ih.trans
    rcases hTU with hinc | ⟨hinc, hzero⟩
    · exact hmono hinc
    · exact le_of_eq (hz U T hinc hzero).symm

/-- Realizability forces the canonical zero-interval graph to separate all
positive intervals. -/
theorem admissible_of_realizes (h : Finset Var → Finset Var → Prop)
    (t : Term (Fin 3) Var) (ht : t.IsCore)
    (he : ∀ L U, L ⊆ U →
      (h L U ↔ (0 : Fin 3) ∈ (t.eval (values (Function.Embedding.refl _) L U)).val)) :
    Admissible h := by
  classical
  obtain ⟨H, hH, hφ, hexp⟩ := Crown.atomic_trace_expansion t ht
  have hzero (φ : Finset Var → Bool) (hφH : φ ∈ H)
      (L U : Finset Var) (hLU : L ⊆ U) (hz : ¬h L U) : φ L = φ U := by
    have hm := (hφ φ hφH).1 hLU
    by_contra hn
    have hp : φ L = false ∧ φ U = true := by
      cases hL : φ L <;> cases hU : φ U <;> simp_all
      exact (Bool.false_ne_true (Bool.eq_true_of_true_le hm)).elim
    exact hz ((he L U hLU).mpr ((hexp L U hLU).mpr ⟨φ, hφH, hp⟩))
  constructor
  · obtain ⟨φ, hφH⟩ := hH
    apply (he ∅ Finset.univ (Finset.empty_subset _)).mpr
    apply (hexp _ _ (Finset.empty_subset _)).mpr
    exact ⟨φ, hφH, (hφ φ hφH).2⟩
  · intro L U hLU hh hr
    obtain ⟨φ, hφH, hL, hU⟩ := (hexp L U hLU).mp ((he L U hLU).mp hh)
    have hp := preserves_reach h φ (hφ φ hφH).1 (hzero φ hφH) hr
    rw [hU, hL] at hp
    exact Bool.false_ne_true (Bool.eq_true_of_true_le hp)

private theorem component_exists (φ : Finset Var → Bool) (hmono : Monotone φ)
    (hbot : φ ∅ = false) (htop : φ Finset.univ = true) :
    ∃ t : Term (Fin 3) Var, t.IsCore ∧ ∀ L U, L ⊆ U →
      ((0 : Fin 3) ∈ (t.eval (values (Function.Embedding.refl _) L U)).val ↔
        φ L = false ∧ φ U = true) := by
  classical
  obtain ⟨t, ht, hc, hb, _, hgap⟩ := Crown.exists_set_completion
    (Function.Embedding.refl (Fin 3)) 1 2 (by decide) φ hmono hbot htop
  refine ⟨t, ht, ?_⟩
  intro L U hLU
  let v := values (Function.Embedding.refl (Fin 3)) L U
  have hL : Finset.univ.filter (fun j => v j = singleton (2 : Fin 3)) = L := by
    ext j
    by_cases hjL : j ∈ L <;> by_cases hjU : j ∈ U <;>
      simp [v, values, hjL, hjU]
  have hU : Finset.univ.filter (fun j => v j ≠ singleton (1 : Fin 3)) = U := by
    ext j
    have hj : j ∈ L → j ∈ U := fun hh => hLU hh
    by_cases hjL : j ∈ L <;> by_cases hjU : j ∈ U <;>
      simp_all [v, values]
  have hc' : t.eval v = singleton 2 ↔ φ L = true := by simpa only [hL] using hc v
  have hb' : t.eval v = singleton 1 ↔ φ U = false := by simpa only [hU] using hb v
  constructor
  · intro ha
    constructor
    · cases hφL : φ L
      · rfl
      · have he := hc'.mpr hφL
        change (0 : Fin 3) ∈ (t.eval v).val at ha
        rw [he] at ha
        simp at ha
    · cases hφU : φ U
      · have he := hb'.mpr hφU
        change (0 : Fin 3) ∈ (t.eval v).val at ha
        rw [he] at ha
        simp at ha
      · rfl
  · rintro ⟨hφL, hφU⟩
    have hg := hgap v (hL ▸ hφL) (hU ▸ hφU)
    have hn : ¬U ⊆ L := by
      intro hUL
      have hm := hmono hUL
      rw [hφL, hφU] at hm
      exact Bool.false_ne_true (Bool.eq_true_of_true_le hm)
    obtain ⟨j, hjU, hjL⟩ := Finset.not_subset.mp hn
    rw [hg]
    apply Set.mem_iUnion.mpr
    exact ⟨j, by simp [v, values, hjL, hjU]⟩

private def unionTerms (xs : List (Term (Fin 3) Var)) (base : Term (Fin 3) Var) :=
  xs.foldr (Term.unionTerm (Function.Embedding.refl _)) base

omit [Fintype Var] in
private theorem unionTerms_core (xs : List (Term (Fin 3) Var)) (base : Term (Fin 3) Var)
    (hb : base.IsCore) (hs : ∀ t ∈ xs, t.IsCore) : (unionTerms xs base).IsCore := by
  induction xs with
  | nil => exact hb
  | cons t ts ih =>
    have ht := hs t (by simp)
    have hi := ih (fun s hs' => hs s (by simp [hs']))
    exact ⟨⟨ht, hi⟩, ⟨ht, hi⟩⟩

omit [Fintype Var] in
private theorem mem_unionTerms (xs : List (Term (Fin 3) Var)) (base : Term (Fin 3) Var)
    (v : Var → WinnerSet (Fin 3)) (r : Fin 3) :
    r ∈ ((unionTerms xs base).eval v).val ↔
      r ∈ (base.eval v).val ∨ ∃ t ∈ xs, r ∈ (t.eval v).val := by
  induction xs with
  | nil => simp [unionTerms]
  | cons t ts ih =>
    change r ∈ ((Term.unionTerm _ t (unionTerms ts base)).eval v).val ↔ _
    rw [Term.eval_unionTerm]
    simp only [WinnerSet.val_union, Set.mem_union, ih, List.mem_cons, exists_eq_or_imp]
    tauto

/-- The canonical graph criterion constructs a core realization of the complete
atomic observer table. Empty variable sets are rejected by the criterion. -/
theorem exists_term_of_admissible (h : Finset Var → Finset Var → Prop)
    (ha : Admissible h) :
    ∃ t : Term (Fin 3) Var, t.IsCore ∧ ∀ L U, L ⊆ U →
      (h L U ↔ (0 : Fin 3) ∈ (t.eval (values (Function.Embedding.refl _) L U)).val) := by
  classical
  let P := {p : Finset Var × Finset Var // p.1 ⊆ p.2 ∧ h p.1 p.2}
  let base : P := ⟨(∅, Finset.univ), Finset.empty_subset _, ha.1⟩
  let φ (p : P) (S : Finset Var) : Bool := decide (Reach h p.val.2 S)
  have hpmono (p : P) : Monotone (φ p) := by
    intro S T hST
    apply Bool.le_iff_imp.mpr
    intro hS
    have hr : Reach h p.val.2 S := by simpa [φ] using hS
    have hr' : Reach h p.val.2 T := hr.tail (Or.inl hST)
    simpa [φ] using hr'
  have hplower (p : P) : φ p p.val.1 = false := by
    simpa [φ] using ha.2 _ _ p.property.1 p.property.2
  have hpupper (p : P) : φ p p.val.2 = true := by simp [φ, Reach, Relation.ReflTransGen.refl]
  have hpbot (p : P) : φ p ∅ = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hr : Reach h p.val.2 ∅ := by simpa [φ] using hh
    exact ha.2 _ _ p.property.1 p.property.2 (hr.tail (Or.inl (Finset.empty_subset _)))
  have hptop (p : P) : φ p Finset.univ = true := by
    have hr : Reach h p.val.2 Finset.univ :=
      Relation.ReflTransGen.single (Or.inl (Finset.subset_univ _))
    simpa [φ] using hr
  choose e he htrace using fun p : P => component_exists (φ p) (hpmono p) (hpbot p) (hptop p)
  have hsafe (p : P) (L U : Finset Var) (hLU : L ⊆ U)
      (hm : (0 : Fin 3) ∈ ((e p).eval (values (Function.Embedding.refl _) L U)).val) : h L U := by
    obtain ⟨hL, hU⟩ := (htrace p L U hLU).mp hm
    by_contra hz
    have hr : Reach h p.val.2 U := by simpa [φ] using hU
    have hr' : Reach h p.val.2 L := hr.tail (Or.inr ⟨hLU, hz⟩)
    have hf : φ p L = true := by simpa [φ] using hr'
    exact Bool.false_ne_true (hL.symm.trans hf)
  let xs := (Finset.univ : Finset P).toList.map e
  refine ⟨unionTerms xs (e base), unionTerms_core _ _ (he base) ?_, ?_⟩
  · intro t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
    exact he p
  · intro L U hLU
    rw [mem_unionTerms]
    constructor
    · intro hh
      let p : P := ⟨(L,U), hLU, hh⟩
      right
      refine ⟨e p, List.mem_map.mpr ⟨p, by simp, rfl⟩, ?_⟩
      exact (htrace p L U hLU).mpr ⟨hplower p, hpupper p⟩
    · rintro (hb | ⟨t, ht, hm⟩)
      · exact hsafe base L U hLU hb
      · obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
        exact hsafe p L U hLU hm

/-- Closed recognition of one observer on all atomic three-owner valuations. -/
theorem admissible_iff (h : Finset Var → Finset Var → Prop) :
    Admissible h ↔ ∃ t : Term (Fin 3) Var, t.IsCore ∧ ∀ L U, L ⊆ U →
      (h L U ↔ (0 : Fin 3) ∈ (t.eval (values (Function.Embedding.refl _) L U)).val) :=
  ⟨exists_term_of_admissible h, fun ⟨t, ht, he⟩ => admissible_of_realizes h t ht he⟩

omit [Fintype Var] in
private theorem exists_embedding {Role : Type*} (three : Fin 3 ↪ Role)
    (t : Term (Fin 3) Var) (ht : t.IsCore) :
    ∃ s : Term Role Var, s.IsCore ∧ ∀ v : Var → WinnerSet (Fin 3),
      s.eval (fun j => StatusModel.expand (fun r => singleton (three r)) (v j)) =
        StatusModel.expand (fun r => singleton (three r)) (t.eval v) := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j => exact ⟨.var j, trivial, fun _ => rfl⟩
  | choice r t u iht ihu =>
    obtain ⟨s, hs, hse⟩ := iht ht.1
    obtain ⟨q, hq, hqe⟩ := ihu ht.2
    refine ⟨.choice (three r) s q, ⟨hs, hq⟩, ?_⟩
    intro v
    simp only [Term.eval, hse, hqe]
    symm
    apply StatusModel.expand_choice
    intro k
    simp only [singleton_inj, three.injective.eq_iff]

omit [Fintype Var] in
private theorem values_expand {Role : Type*} (three : Fin 3 ↪ Role)
    (L U : Finset Var) :
    values three L U = fun j => StatusModel.expand (fun r => singleton (three r))
      (values (Function.Embedding.refl (Fin 3)) L U j) := by
  classical
  funext j
  by_cases hjL : j ∈ L <;> by_cases hjU : j ∈ U <;>
    simp [values, hjL, hjU]

/-- The same closed criterion holds inside any ambient role set containing
three distinguished owners. Other owners do not add atomic observer traces. -/
theorem admissible_iff_embedding {Role : Type*} (three : Fin 3 ↪ Role)
    (h : Finset Var → Finset Var → Prop) :
    Admissible h ↔ ∃ t : Term Role Var, t.IsCore ∧ ∀ L U, L ⊆ U →
      (h L U ↔ three 0 ∈ (t.eval (values three L U)).val) := by
  constructor
  · intro ha
    obtain ⟨t, ht, he⟩ := exists_term_of_admissible h ha
    obtain ⟨s, hs, hse⟩ := exists_embedding three t ht
    refine ⟨s, hs, ?_⟩
    intro L U hLU
    rw [values_expand, hse, StatusModel.mem_expand_embedding]
    exact he L U hLU
  · rintro ⟨t, ht, he⟩
    obtain ⟨s, hs, hse⟩ := Core.exists_role_restriction three
      (Function.Embedding.refl (Fin 3)) t ht
    apply admissible_of_realizes h s hs
    intro L U hLU
    have hh := he L U hLU
    rw [values_expand, hse, StatusModel.mem_expand_embedding] at hh
    exact hh

/-- No atomic observer table is admissible without an input variable. -/
theorem not_admissible_of_isEmpty [IsEmpty Var]
    (h : Finset Var → Finset Var → Prop) : ¬Admissible h := by
  intro ha
  have hu : (Finset.univ : Finset Var) = ∅ := by
    ext j
    exact isEmptyElim j
  apply ha.2 ∅ Finset.univ (Finset.empty_subset _) ha.1
  rw [hu]
  exact Relation.ReflTransGen.refl

end KFOL.Core.AtomicObserver
