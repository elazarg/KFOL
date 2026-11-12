module

public import KFOL.Core.FivePointInterpolation
public import KFOL.Core.ProfileCompletion
public import KFOL.Core.WholeInputs

/-! # Exact pointwise profile compatibility does not give a global core term

One fixed admissible profile tuple passes the direct one-point completion
criterion at every input of a noncore operation, even though every five
inputs also have a common core interpolant.
-/

@[expose] public section
namespace KFOL.Core

variable {Role : Type*} [Fintype Role] [DecidableEq Role]
attribute [local instance] Equational.coreStructure

/-- Every exact one-point profile test can pass for one global profile tuple,
even with five-point core interpolation, without a common core realization. -/
theorem exists_pointwise_profile_obstruction (three : Fin 3 ↪ Role) :
    ∃ (Φ : Role → (Fin 5 → Bool) → Bool)
      (f : (Fin 5 → WinnerSet Role) → WinnerSet Role),
      AdmissibleProfiles Φ ∧ LocallyInterpolable 5 f ∧
      (∀ values, ProfileBounds.OnePointCondition Φ values (f values)) ∧
      ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ values, t.eval values = f values := by
  obtain ⟨s, _, f, hs, _, hlocal, _, _, hsingle, hb, hn⟩ :=
    exists_five_local_profile_fiber_nonconvex three
  let e := Equational.Core.encode s hs
  let Φ : Role → (Fin 5 → Bool) → Bool := fun r A => profile r A e
  have he (values : Fin 5 → WinnerSet Role) : e.realize values = s.eval values := by
    dsimp only [e]
    rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
  refine ⟨Φ, f, admissibleProfiles_profile e, hlocal, ?_, hn⟩
  intro values
  refine ⟨?_, ?_, ?_⟩
  · apply (ProfileBounds.profileCondition_iff three Φ values (f values).val).mpr
    refine ⟨e, fun _ _ => rfl, ?_⟩
    simpa only [he] using (hb values).1
  · intro r
    change profile r (fun j => decide (values j = WinnerSet.singleton r)) e = true ↔
      f values = WinnerSet.singleton r
    rw [← winnerSet_eq_singleton_iff_profile, he]
    exact (hsingle values r).symm
  · intro k hk
    obtain ⟨t, ht, hfit⟩ := hlocal (fun _ => values)
    have hvalue : t.eval values = f values := hfit 0
    have htk : k ∈ (t.eval values).val := by simpa only [hvalue] using hk
    obtain ⟨j, hj, hsub⟩ := whole_input_provenance_of_isCore t ht values k htk
    exact ⟨j, hj, by simpa only [hvalue] using hsub⟩

end KFOL.Core
