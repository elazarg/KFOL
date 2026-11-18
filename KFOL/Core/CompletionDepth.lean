module

public import KFOL.Definitions.CompletionDepth
public import KFOL.Core.ProfileEnvelope
public import KFOL.Core.Exhaustion
public import KFOL.Equational.Native

/-! # Realization of compositions of greatest singleton-profile completions -/

@[expose] public section
namespace KFOL.Core.CompletionDepth
universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v} {n : ℕ}
attribute [local instance] Equational.coreStructure

private theorem exists_complete_term [Fintype Role] (three : Fin 3 ↪ Role)
    (F : Role → (Fin (n + 1) → Bool) → Bool) (hF : AdmissibleProfiles F) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) (Fin (n + 1)),
      (∀ v r, t.realize v = WinnerSet.singleton r ↔ F r (ProfileBounds.atomicBits r v) = true) ∧
      ∀ v : Fin (n + 1) → WinnerSet Role, (t.realize v).Ambiguous →
        (t.realize v).val = ⋃ i, (v i).val := by
  classical
  refine ⟨synthesizeProfiles three F hF, ?_, val_synthesizeProfiles_of_ambiguous three F hF⟩
  intro v r
  rw [winnerSet_eq_singleton_iff_profile, profile_synthesizeProfiles]
  rfl

namespace Gate

omit [DecidableEq Role] in
/-- Any provenance-preserving operation with the same singleton outputs is
pointwise contained in the completion gate. -/
theorem greatest (g : Gate Role n)
    (f : (Fin (n + 1) → WinnerSet Role) → WinnerSet Role)
    (hsource : ∀ v, (f v).val ⊆ ⋃ j, (v j).val)
    (hsingle : ∀ v r, g.eval v = WinnerSet.singleton r → f v = WinnerSet.singleton r)
    (v : Fin (n + 1) → WinnerSet Role) : (f v).val ⊆ (g.eval v).val := by
  classical
  by_cases h : (g.eval v).Ambiguous
  · rw [g.union_of_ambiguous v h]
    exact hsource v
  · obtain ⟨r, hr⟩ : ∃ r, g.eval v = WinnerSet.singleton r := by
      simpa only [WinnerSet.Ambiguous, not_forall, not_not] using h
    rw [hsingle v r hr, hr]

/-- Every admissible tuple is the tuple of some completion gate. -/
theorem exists_of_admissible [Fintype Role] (three : Fin 3 ↪ Role)
    (F : Role → (Fin (n + 1) → Bool) → Bool) (hF : AdmissibleProfiles F) :
    ∃ g : Gate Role n, g.profiles = F := by
  obtain ⟨t, ht, hu⟩ := exists_complete_term three F hF
  exact ⟨⟨fun v => t.realize v, F, hF, ht, hu⟩, rfl⟩

/-- A completion gate is realized by one core term on all winner-set inputs. -/
theorem exists_core [Fintype Role] (g : Gate Role n) (three : Fin 3 ↪ Role) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) (Fin (n + 1)),
      ∀ v, t.realize v = g.eval v := by
  classical
  obtain ⟨t, ht, hu⟩ := exists_complete_term three g.profiles g.admissible
  refine ⟨t, fun v => ?_⟩
  by_cases h : (g.eval v).Ambiguous
  · have hamb : (t.realize v).Ambiguous :=
      fun r hr => h r ((g.singleton_iff v r).2 ((ht v r).1 hr))
    exact Subtype.ext ((hu v hamb).trans (g.union_of_ambiguous v h).symm)
  · obtain ⟨r, hr⟩ : ∃ r, g.eval v = WinnerSet.singleton r := by
      simpa only [WinnerSet.Ambiguous, not_forall, not_not] using h
    exact ((ht v r).2 ((g.singleton_iff v r).1 hr)).trans hr.symm

/-- Binary owned choice is already the greatest completion of its profiles. -/
noncomputable def choice (r : Role) : Gate Role 1 where
  eval v := WinnerSet.choice r (v 0) (v 1)
  profiles i A := profile i A (choiceTerm r (.var 0) (.var 1))
  admissible := admissibleProfiles_profile _
  singleton_iff v i := winnerSet_eq_singleton_iff_profile (choiceTerm r (.var 0) (.var 1)) i v
  union_of_ambiguous v hamb := by
    classical
    have hn : ¬(v 0 = WinnerSet.singleton r ∨ v 1 = WinnerSet.singleton r) :=
      fun h => hamb r ((WinnerSet.choice_eq_owner_iff _ _ r).2 h)
    rw [WinnerSet.choice, ite_eq_right hn]
    ext k
    change k ∈ (v 0).val ∨ k ∈ (v 1).val ↔ _
    rw [Set.mem_iUnion]
    constructor
    · exact fun h => h.elim (fun hk => ⟨0, hk⟩) (fun hk => ⟨1, hk⟩)
    · rintro ⟨j, hj⟩
      fin_cases j <;> tauto

@[simp] theorem choice_eval (r : Role) (v : Fin 2 → WinnerSet Role) :
    (choice r).eval v = WinnerSet.choice r (v 0) (v 1) := rfl

end Gate

namespace Expr

/-- Apply the binary completion gate for one owner. -/
noncomputable def choice (r : Role) (s t : Expr Role Var) : Expr Role Var :=
  .gate (Gate.choice r) (fun j => if j = 0 then s else t)

@[simp] theorem choice_eval (r : Role) (s t : Expr Role Var) (v : Var → WinnerSet Role) :
    (choice r s t).eval v = WinnerSet.choice r (s.eval v) (t.eval v) := rfl

@[simp] theorem choice_depth (r : Role) (s t : Expr Role Var) :
    (choice r s t).depth = max s.depth t.depth + 1 := by
  simp [choice, depth, Finset.univ_fin2]

/-- Every finite expression induces a core term, uniformly on all valuations. -/
theorem exists_core [Fintype Role] (e : Expr Role Var) (three : Fin 3 ↪ Role) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ v, t.realize v = e.eval v := by
  classical
  induction e with
  | var j => exact ⟨.var j, fun _ => rfl⟩
  | union s t ihs iht =>
    obtain ⟨u, hu⟩ := ihs
    obtain ⟨w, hw⟩ := iht
    exact ⟨unionTerm three u w, fun v => by rw [realize_union_winner, hu, hw]; rfl⟩
  | gate g args ih =>
    choose children hchildren using ih
    obtain ⟨t, ht⟩ := g.exists_core three
    refine ⟨t.subst children, fun v => ?_⟩
    rw [FirstOrder.Language.Term.realize_subst, ht]
    exact congrArg g.eval (funext fun j => hchildren j v)

/-- Every core term can be expressed using the binary completion gates. -/
theorem exists_of_core (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    ∃ e : Expr Role Var, ∀ v, e.eval v = t.realize v := by
  induction t using induction_choice with
  | var j => exact ⟨.var j, fun _ => rfl⟩
  | choice r s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨choice r a b, fun v => by rw [choice_eval, ha, hb, realize_choice_winner]⟩

end Expr
end KFOL.Core.CompletionDepth
