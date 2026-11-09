module

public import KFOL.Reset.Antimatroid.Synthesis
public import KFOL.Reset.Chain

/-! # The bijection of actual reset term functions with rooted antimatroids -/

@[expose] public section

namespace KFOL.Reset

universe u v

variable {Var : Type v} [DecidableEq Var]

namespace Term

/-- The family remembers the entire selector, not just its feasible support. -/
theorem antimatroid_eq_iff_selected (s t : Term Var) :
    s.antimatroid = t.antimatroid ↔ ∀ B j, s.Selected B j ↔ t.Selected B j := by
  constructor
  · intro he B j
    rw [← ready_antimatroid, ← ready_antimatroid, he]
  · intro he
    apply RootedAntimatroid.ext
    ext A
    rw [RootedAntimatroid.feasible_iff_ready, RootedAntimatroid.feasible_iff_ready]
    simp only [ready_antimatroid, he]

/-- With three roles, equality of the independent families is exactly equality
of the original winner-set functions. -/
theorem antimatroid_eq_iff_eval {Role : Type u} (three : Fin 3 ↪ Role) (s t : Term Var) :
    s.antimatroid = t.antimatroid ↔ ∀ v : Var → WinnerSet Role, s.eval v = t.eval v :=
  ⟨fun he => s.eval_eq_of_selected t ((s.antimatroid_eq_iff_selected t).mp he),
    fun he => (s.antimatroid_eq_iff_selected t).mpr
      (s.selected_iff_of_chain_eq t three (fun v _ => he v))⟩

end Term

/-- The complete representation theorem uses actual semantic term functions.
Choice of a representing syntax tree is immaterial by the proved family criterion. -/
noncomputable def termFunctionEquiv {Role : Type u} (three : Fin 3 ↪ Role) :
    TermFunction Role Var ≃ RootedAntimatroid Var := by
  classical
  let repr (f : TermFunction Role Var) : Term Var := Classical.choose f.property
  let syn (F : RootedAntimatroid Var) : Term Var := Classical.choose F.exists_term
  let out (f : TermFunction Role Var) := (repr f).antimatroid
  let back (F : RootedAntimatroid Var) : TermFunction Role Var :=
    ⟨(syn F).eval, ⟨syn F, fun _ => rfl⟩⟩
  refine ⟨out, back, ?_, ?_⟩
  · intro f
    apply Subtype.ext
    funext v
    change (syn (out f)).eval v = f.val v
    have ha : (syn (out f)).antimatroid = (repr f).antimatroid :=
      Classical.choose_spec (out f).exists_term
    have he := ((syn (out f)).antimatroid_eq_iff_eval three (repr f)).mp ha v
    exact he.trans (Classical.choose_spec f.property v).symm
  · intro F
    change (repr (back F)).antimatroid = F
    have he : ∀ v : Var → WinnerSet Role, (repr (back F)).eval v = (syn F).eval v :=
      fun v => (Classical.choose_spec (back F).property v).symm
    exact ((repr (back F)).antimatroid_eq_iff_eval three (syn F)).mpr he |>.trans
      (Classical.choose_spec F.exists_term)

/-- The bijection sends every term to its canonical feasible family. -/
theorem termFunctionEquiv_apply {Role : Type u} (three : Fin 3 ↪ Role) (t : Term Var) :
    termFunctionEquiv three (⟨t.eval, ⟨t, fun _ => rfl⟩⟩ : TermFunction Role Var) =
      t.antimatroid := by
  let f : TermFunction Role Var := ⟨t.eval, ⟨t, fun _ => rfl⟩⟩
  change (Classical.choose f.property).antimatroid = t.antimatroid
  apply (Term.antimatroid_eq_iff_eval three _ t).mpr
  intro v
  exact (Classical.choose_spec f.property v).symm

end KFOL.Reset
