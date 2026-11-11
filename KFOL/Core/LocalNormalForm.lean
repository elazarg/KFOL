module

public import KFOL.Core.RelationalInterpolation
public import KFOL.Core.SourceNormalForm
public import Mathlib.Tactic.Tauto

/-! # Source normal forms from three-point interpolation

Fixing the passive statuses makes every core membership predicate additive
in its sources. Three-point interpolation transfers binary additivity to an
operation. Finitely many inputs then give the isolated-source decomposition.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

private noncomputable def restrictSources (three : Fin 3 ↪ Role) (k : Role)
    (S : Finset Var) (v : Var → WinnerSet Role) : Var → WinnerSet Role := by
  classical
  exact fun j => if j ∈ S then v j else representative three k (passive k (v j))

private theorem passive_restrictSources (three : Fin 3 ↪ Role) (k : Role)
    (S : Finset Var) (v : Var → WinnerSet Role) (j : Var) :
    passive k (restrictSources three k S v j) = passive k (v j) := by
  classical
  by_cases hj : j ∈ S <;> simp [restrictSources, hj]

private theorem pattern_restrictSources (three : Fin 3 ↪ Role) (k : Role)
    (S : Finset Var) (v : Var → WinnerSet Role) (j : Var) :
    pattern k j (restrictSources three k S v) = pattern k j v := by
  funext i
  exact passive_restrictSources three k S v i.val

private theorem mem_restrictSources (three : Fin 3 ↪ Role) (k : Role)
    (S : Finset Var) (v : Var → WinnerSet Role) (j : Var) :
    k ∈ (restrictSources three k S v j).val ↔ j ∈ S ∧ k ∈ (v j).val := by
  classical
  by_cases hj : j ∈ S <;> simp [restrictSources, hj]

private theorem eval_restrictSources (three : Fin 3 ↪ Role) (k : Role)
    (S : Finset Var) (v : Var → WinnerSet Role) (t : Term Role Var) (ht : t.IsCore) :
    k ∈ (t.eval (restrictSources three k S v)).val ↔
      ∃ j ∈ S, k ∈ (v j).val ∧ k ∈ (t.eval (probe three k j (pattern k j v))).val := by
  rw [membership_iff_source three t ht]
  simp only [mem_restrictSources, pattern_restrictSources]
  tauto

private theorem eval_restrictSources_union [DecidableEq Var] (three : Fin 3 ↪ Role) (k : Role)
    (S T : Finset Var) (v : Var → WinnerSet Role) (t : Term Role Var) (ht : t.IsCore) :
    k ∈ (t.eval (restrictSources three k (S ∪ T) v)).val ↔
      k ∈ (t.eval (restrictSources three k S v)).val ∨
      k ∈ (t.eval (restrictSources three k T v)).val := by
  classical
  simp only [eval_restrictSources three k _ v t ht, Finset.mem_union]
  constructor
  · rintro ⟨j, hj | hj, hp⟩
    · exact Or.inl ⟨j, hj, hp⟩
    · exact Or.inr ⟨j, hj, hp⟩
  · rintro (⟨j, hj, hp⟩ | ⟨j, hj, hp⟩)
    · exact ⟨j, Or.inl hj, hp⟩
    · exact ⟨j, Or.inr hj, hp⟩

private theorem local_restrictSources_union [DecidableEq Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (S T : Finset Var) (v : Var → WinnerSet Role) :
    k ∈ (f (restrictSources three k (S ∪ T) v)).val ↔
      k ∈ (f (restrictSources three k S v)).val ∨
      k ∈ (f (restrictSources three k T v)).val := by
  obtain ⟨t, ht, he⟩ := hf ![restrictSources three k S v,
    restrictSources three k T v, restrictSources three k (S ∪ T) v]
  have hS : t.eval (restrictSources three k S v) = f (restrictSources three k S v) := he 0
  have hT : t.eval (restrictSources three k T v) = f (restrictSources three k T v) := he 1
  have hU : t.eval (restrictSources three k (S ∪ T) v) =
      f (restrictSources three k (S ∪ T) v) := he 2
  simpa only [hS, hT, hU] using eval_restrictSources_union three k S T v t ht

private theorem local_restrictSources_empty (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (v : Var → WinnerSet Role) :
    k ∉ (f (restrictSources three k ∅ v)).val := by
  obtain ⟨t, ht, he⟩ := hf (fun _ => restrictSources three k ∅ v)
  rw [← he 0, eval_restrictSources three k ∅ v t ht]
  simp

private theorem local_restrictSources_finset (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (S : Finset Var) (v : Var → WinnerSet Role) :
    k ∈ (f (restrictSources three k S v)).val ↔
      ∃ j ∈ S, k ∈ (f (restrictSources three k {j} v)).val := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [local_restrictSources_empty three f hf k v]
  | @insert j S _ ih =>
    rw [Finset.insert_eq, local_restrictSources_union three f hf k {j} S v, ih]
    simp only [Finset.mem_union, Finset.mem_singleton, exists_eq_or_imp]

private theorem local_restrictSources_singleton (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (j : Var) (v : Var → WinnerSet Role) :
    k ∈ (f (restrictSources three k {j} v)).val ↔
      k ∈ (v j).val ∧ k ∈ (f (probe three k j (pattern k j v))).val := by
  classical
  obtain ⟨t, ht, he⟩ := hf ![restrictSources three k {j} v,
    probe three k j (pattern k j v), probe three k j (pattern k j v)]
  have hS : t.eval (restrictSources three k {j} v) = f (restrictSources three k {j} v) := he 0
  have hP : t.eval (probe three k j (pattern k j v)) = f (probe three k j (pattern k j v)) := he 1
  simpa only [Finset.mem_singleton, exists_eq_left, hS, hP] using
    eval_restrictSources three k {j} v t ht

/-- Three-point interpolation forces the isolated-source decomposition at
all finite arities, without any finiteness assumption on roles. -/
theorem local_membership_iff_source [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ (f v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (f (probe three k j (pattern k j v))).val := by
  classical
  have hU : restrictSources three k Finset.univ v = v := by
    funext j; simp [restrictSources]
  conv_lhs => rw [← hU]
  rw [local_restrictSources_finset three f hf k Finset.univ v]
  simp only [Finset.mem_univ, true_and, local_restrictSources_singleton three f hf]

/-- A common two-point witness transfers monotonicity to each coefficient. -/
theorem local_coefficient_mono (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (j : Var) : Monotone (fun p : Pattern k j => k ∈ (f (probe three k j p)).val) := by
  intro p q hpq hp
  obtain ⟨t, ht, he⟩ := hf ![probe three k j p, probe three k j q, probe three k j p]
  have hP : t.eval (probe three k j p) = f (probe three k j p) := he 0
  have hQ : t.eval (probe three k j q) = f (probe three k j q) := he 1
  rw [← hQ]
  exact t.eval_mono (probe_mono three k j hpq) (hP.symm ▸ hp)

/-- Prime guards exactly describe every coefficient of a three-point operation. -/
theorem local_coefficient_iff_guard [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (k : Role) (j : Var) (p : Pattern k j) :
    k ∈ (f (probe three k j p)).val ↔ ∃ g ∈ normalForm three f k j, Enabled g p := by
  rw [iff_enabled_prime _ (local_coefficient_mono three f hf k j)]
  simp only [mem_normalForm]

/-- The complete prime families are canonical for their own coefficients. -/
theorem local_normalForm_canonical [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f) :
    Canonical (normalForm three f) := by
  intro k j g
  have hc : coefficients (normalForm three f) k j =
      (fun p => k ∈ (f (probe three k j p)).val) := by
    funext p
    exact propext (local_coefficient_iff_guard three f hf k j p).symm
  rw [hc]
  exact mem_normalForm three f k j g

/-- Ternary relational tests already force the canonical prime-guard form.
They need not force its realization by one core term. -/
theorem local_normalForm_correct [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f)
    (v : Var → WinnerSet Role) : meaning (normalForm three f) v = (f v).val := by
  ext k
  rw [local_membership_iff_source three f hf v k]
  change (∃ j, k ∈ (v j).val ∧ ∃ g ∈ normalForm three f k j, Enabled g (pattern k j v)) ↔ _
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  rw [iff_enabled_prime _ (local_coefficient_mono three f hf k j)]
  simp only [mem_normalForm]

/-- The full finite-arity source representation forced by ternary tests. -/
theorem local_normal_forms [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : LocallyInterpolable 3 f) :
    (∀ v k, k ∈ (f v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (f (probe three k j (pattern k j v))).val) ∧
    Canonical (normalForm three f) ∧
    ∀ v, meaning (normalForm three f) v = (f v).val :=
  ⟨local_membership_iff_source three f hf, local_normalForm_canonical three f hf,
    local_normalForm_correct three f hf⟩

end KFOL.Core.Sources
