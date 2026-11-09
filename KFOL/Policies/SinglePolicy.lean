module

public import KFOL.Policies.Guards
public import KFOL.Owner.Completeness

/-! One syntax-only comparison decides every fixed nontrivial policy, with
explicit singleton-or-pair separating valuations. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

private theorem passes_minimalVal {Role : Type u} {Var : Type v} [DecidableEq Var]
    (D : Set Role) (k r c : Role) (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r)
    (g : Owner.Guard Var) (i : Var) :
    WinnerSet.PolicyPasses D k (Owner.minimalVal k r c g i) ↔
      i ∈ g.many ∨ i ∈ g.outside ∨ i = g.source := by
  have hrc : r ≠ c := fun he => hc (he ▸ hr)
  by_cases hm : i ∈ g.many
  · exact ⟨fun _ => Or.inl hm, fun _ => WinnerSet.policyPasses_of_ambiguous D k _
      ((Owner.minimalVal_ambiguous k r c hkr hrc g i).mpr hm)⟩
  · by_cases hs : i = g.source
    · subst i
      simp [Owner.minimalVal, hm, WinnerSet.policyPasses_singleton]
    · by_cases hn : i ∈ g.outside <;>
      simp [Owner.minimalVal, hm, hs, hn, WinnerSet.policyPasses_singleton, hr, hc, Ne.symm hkr]

private theorem eval_minimalVal {Role : Type u} {Var : Type v} [DecidableEq Var]
    (D : Set Role) (k r c : Role) (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c)
    (g : Owner.Guard Var) (guards : List (Owner.Guard Var)) :
    Owner.Eval guards (fun i => (Owner.minimalVal k r c g i).Ambiguous)
      (fun i => WinnerSet.PolicyPasses D k (Owner.minimalVal k r c g i))
      (fun i => k ∈ (Owner.minimalVal k r c g i).val) ↔
        ∃ h ∈ guards, h.Dominates g := by
  have hrc : r ≠ c := fun he => hc (he ▸ hr)
  simp only [Owner.Eval, Owner.Guard.Holds, Owner.minimalVal_ambiguous k r c hkr hrc,
    passes_minimalVal D k r c hr hc hkr, Owner.minimalVal_marker k r c hkr hkc]
  constructor
  · rintro ⟨h, hh, hm, hn, hs⟩
    exact ⟨h, hh, hs, hm, hn⟩
  · rintro ⟨h, hh, hs, hm, hn⟩
    exact ⟨h, hh, hm, hn, hs⟩

/-- Pairwise coverage is sound simultaneously at every observer. -/
theorem single_covers_sound {Role : Type u} {Var : Type v}
    (D : Set Role) (k : Role) (left right : List (Owner.Guard Var)) (h : Owner.Covers left right)
    (v : Var → WinnerSet Role) :
    Owner.Eval left (fun i => (v i).Ambiguous) (fun i => WinnerSet.PolicyPasses D k (v i))
      (fun i => k ∈ (v i).val) →
    Owner.Eval right (fun i => (v i).Ambiguous) (fun i => WinnerSet.PolicyPasses D k (v i))
      (fun i => k ∈ (v i).val) :=
  Owner.covers_sound left right h _ _ _
    (fun i hi => WinnerSet.policyPasses_of_ambiguous D k (v i) hi)
    (fun i hi => WinnerSet.policyPasses_of_mem D k (v i) hi)

/-- One observer is complete whenever it is distinct from a blocking atom
and a nonblocking atom. A three-role embedding provides one for every proper nonempty policy. -/
theorem single_covers_iff {Role : Type u} {Var : Type v} [DecidableEq Var]
    (D : Set Role) (k r c : Role) (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c)
    (left right : List (Owner.Guard Var)) :
    Owner.Covers left right ↔ ∀ v : Var → WinnerSet Role,
      Owner.Eval left (fun i => (v i).Ambiguous) (fun i => WinnerSet.PolicyPasses D k (v i))
        (fun i => k ∈ (v i).val) →
      Owner.Eval right (fun i => (v i).Ambiguous) (fun i => WinnerSet.PolicyPasses D k (v i))
        (fun i => k ∈ (v i).val) := by
  constructor
  · exact fun h v => single_covers_sound D k left right h v
  · intro h g hg
    let v := Owner.minimalVal k r c g
    have hl := (eval_minimalVal D k r c hr hc hkr hkc g left).mpr
      ⟨g, hg, rfl, (fun _ h => h), fun _ h => Or.inr (Or.inl h)⟩
    exact (eval_minimalVal D k r c hr hc hkr hkc g right).mp (h v hl)

/-- Failed syntax coverage supplies the concrete minimal singleton-or-pair
valuation for the fixed policy, rather than a bare existence argument. -/
theorem countervaluation_of_not_single_covers {Role : Type u} {Var : Type v} [DecidableEq Var]
    (D : Set Role) (k r c : Role) (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c)
    (left right : List (Owner.Guard Var)) (h : ¬Owner.Covers left right) :
    ∃ g ∈ left,
      Owner.Eval left (fun i => (Owner.minimalVal k r c g i).Ambiguous)
        (fun i => WinnerSet.PolicyPasses D k (Owner.minimalVal k r c g i))
        (fun i => k ∈ (Owner.minimalVal k r c g i).val) ∧
      ¬Owner.Eval right (fun i => (Owner.minimalVal k r c g i).Ambiguous)
        (fun i => WinnerSet.PolicyPasses D k (Owner.minimalVal k r c g i))
        (fun i => k ∈ (Owner.minimalVal k r c g i).val) := by
  classical
  have hn : ¬∀ g ∈ left, ∃ q ∈ right, q.Dominates g := h
  push Not at hn
  obtain ⟨g, hg, hn⟩ := hn
  refine ⟨g, hg, ?_, ?_⟩
  · exact (eval_minimalVal D k r c hr hc hkr hkc g left).mpr
      ⟨g, hg, rfl, (fun _ h => h), fun _ h => Or.inr (Or.inl h)⟩
  · intro he
    obtain ⟨q, hq, hd⟩ := (eval_minimalVal D k r c hr hc hkr hkc g right).mp he
    exact hn q hq hd

namespace Term

variable {Role : Type u} {Label : Type w} {Var : Type v}

theorem single_observation_iff [DecidableEq Var] (D : Set Role) (k r c : Role)
    (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c) (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role,
      k ∈ (left.eval (fun _ => D) v).val → k ∈ (right.eval (fun _ => D) v).val) ↔
        Owner.Covers left.singleGuards right.singleGuards := by
  rw [single_covers_iff D k r c hr hc hkr hkc]
  simp only [single_guard_semantics]

/-- The one comparison algorithm has exactly the same result for every
nontrivial policy and every role set with three distinct roles. -/
theorem single_equation_iff [DecidableEq Var] (D : Set Role) (k r c : Role)
    (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c) (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role, left.eval (fun _ => D) v = right.eval (fun _ => D) v) ↔
      Owner.Covers left.singleGuards right.singleGuards ∧ Owner.Covers right.singleGuards left.singleGuards := by
  constructor
  · intro h
    constructor
    · exact (single_observation_iff D k r c hr hc hkr hkc left right).mp (fun v hv => h v ▸ hv)
    · exact (single_observation_iff D k r c hr hc hkr hkc right left).mp (fun v hv => (h v).symm ▸ hv)
  · rintro ⟨hlr, hrl⟩ v
    apply Subtype.ext
    ext observer
    rw [single_guard_semantics, single_guard_semantics]
    exact ⟨single_covers_sound D observer _ _ hlr v, single_covers_sound D observer _ _ hrl v⟩

/-- The executable native checker is correct, with no semantic or role
parameters in the program itself. -/
theorem singleEquationB_correct [DecidableEq Var] (three : Fin 3 ↪ Role) (D : Set Role)
    (hD : D.Nonempty) (hproper : ∃ c, c ∉ D) (left right : Term Label Var) :
    singleEquationB left right = true ↔
      ∀ v : Var → WinnerSet Role, left.eval (fun _ => D) v = right.eval (fun _ => D) v := by
  obtain ⟨r, hr⟩ := hD
  obtain ⟨c, hc⟩ := hproper
  obtain ⟨k, hkr, hkc⟩ := exists_role_outside_pair three r c
  rw [single_equation_iff D k r c hr hc hkr hkc]
  simp only [singleEquationB, Bool.and_eq_true, Owner.coversB_correct]

/-- Observation at the supplied marker alone determines full equation equality. -/
theorem single_observation_equation_iff [DecidableEq Var] (D : Set Role) (k r c : Role)
    (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c) (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role, left.eval (fun _ => D) v = right.eval (fun _ => D) v) ↔
      ∀ v : Var → WinnerSet Role,
        k ∈ (left.eval (fun _ => D) v).val ↔ k ∈ (right.eval (fun _ => D) v).val := by
  constructor
  · intro he v
    rw [he v]
  · intro hobs
    apply (single_equation_iff D k r c hr hc hkr hkc left right).mpr
    exact ⟨(single_observation_iff D k r c hr hc hkr hkc left right).mp (fun v => (hobs v).mp),
      (single_observation_iff D k r c hr hc hkr hkc right left).mp (fun v => (hobs v).mpr)⟩

/-- The common nontrivial-policy equational theory is independent of the
policy and of the role carrier, subject only to the displayed three-role hypotheses. -/
theorem single_equation_policy_independent [DecidableEq Var]
    {Role' : Type u} (three : Fin 3 ↪ Role) (three' : Fin 3 ↪ Role')
    (D : Set Role) (D' : Set Role') (hD : D.Nonempty) (hD' : D'.Nonempty)
    (hproper : ∃ c, c ∉ D) (hproper' : ∃ c, c ∉ D') (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role, left.eval (fun _ => D) v = right.eval (fun _ => D) v) ↔
      ∀ v : Var → WinnerSet Role', left.eval (fun _ => D') v = right.eval (fun _ => D') v :=
  (singleEquationB_correct three D hD hproper left right).symm.trans
    (singleEquationB_correct three' D' hD' hproper' left right)

/-- Every rejected equation has the displayed atom-or-pair countervaluation,
using only the marker, one blocking role and one nonblocking role. -/
theorem single_countervaluation [DecidableEq Var] (D : Set Role) (k r c : Role)
    (hr : r ∈ D) (hc : c ∉ D) (hkr : k ≠ r) (hkc : k ≠ c)
    (left right : Term Label Var) (hfalse : singleEquationB left right = false) :
    ∃ g : Owner.Guard Var, (g ∈ left.singleGuards ∨ g ∈ right.singleGuards) ∧
      left.eval (fun _ => D) (Owner.minimalVal k r c g) ≠ right.eval (fun _ => D) (Owner.minimalVal k r c g) ∧
      ∀ i : Var, ∃ a ∈ ({k, r, c} : Set Role), ∃ b ∈ ({k, r, c} : Set Role),
        Owner.minimalVal k r c g i = (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
  classical
  have hn : ¬(Owner.Covers left.singleGuards right.singleGuards ∧ Owner.Covers right.singleGuards left.singleGuards) := by
    intro hh
    have htrue : singleEquationB left right = true := by
      simpa only [singleEquationB, Bool.and_eq_true, Owner.coversB_correct] using hh
    cases hfalse.symm.trans htrue
  have hdiff (s t : Term Label Var) (hst : ¬Owner.Covers s.singleGuards t.singleGuards) :
      ∃ g ∈ s.singleGuards, s.eval (fun _ => D) (Owner.minimalVal k r c g) ≠
        t.eval (fun _ => D) (Owner.minimalVal k r c g) := by
    obtain ⟨g, hg, hsg, htg⟩ := countervaluation_of_not_single_covers D k r c hr hc hkr hkc _ _ hst
    refine ⟨g, hg, ?_⟩
    intro he
    have hs := (s.single_guard_semantics D k _).mpr hsg
    have ht := he ▸ hs
    exact htg ((t.single_guard_semantics D k _).mp ht)
  by_cases hLR : Owner.Covers left.singleGuards right.singleGuards
  · obtain ⟨g, hg, hne⟩ := hdiff right left (fun hRL => hn ⟨hLR, hRL⟩)
    exact ⟨g, Or.inr hg, Ne.symm hne, fun i => Owner.minimalVal_pair k r c g i⟩
  · obtain ⟨g, hg, hne⟩ := hdiff left right hLR
    exact ⟨g, Or.inl hg, hne, fun i => Owner.minimalVal_pair k r c g i⟩

end Term
end KFOL.Policies
