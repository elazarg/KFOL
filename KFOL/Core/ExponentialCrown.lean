module

public import KFOL.Core.GrayCrown
public import KFOL.Core.IntervalCrownLocality
public import KFOL.Core.IntervalCrownObstruction
public import KFOL.Algebra.Idempotent

/-! # Exponential interpolation lower bounds in the number of inputs

A reflected Gray cycle has 2^d matching intervals on only 2d paired inputs.
Every one-edge deletion is a full-winner core operation. The complete crown
is idempotent and has no realization even with constants and role switches. -/

@[expose] public section
namespace KFOL.Core.GrayCrown

/-- An exponential number of local observations can fail to detect a nonterm
operation with only twice as many inputs as Gray coordinates. -/
theorem exists_exponential_obstruction {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : ((Fin d × Bool) → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable (2 ^ d) f ∧
      ¬LocallyInterpolable (2 ^ d + 1) f ∧
      (∀ A : WinnerSet Role, f (fun _ => A) = A) ∧
      ¬∃ t : Term Role (Fin d × Bool), ∀ values, t.eval values = f values := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨g⟩ := exists_code (by omega : 0 < d)
  let G := g.frame hd
  have hm : 3 ≤ 2 ^ d := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hpow ⊢
    omega
  let f := Intervals.operation (three 1) (three 2) (G.edges Set.univ)
  have hid (A : WinnerSet Role) : f (fun _ => A) = A :=
    IntervalCrown.Frame.full_operation_idempotent three G A
  refine ⟨f, G.operation_locallyInterpolable_sharp three,
    IntervalCrown.Frame.full_operation_not_locallyInterpolable three G hm, hid, ?_⟩
  rintro ⟨t, he⟩
  have ht (A : WinnerSet Role) : t.eval (fun _ => A) = A := (he _).trans (hid A)
  obtain ⟨hcore, hvalue, _⟩ := t.idempotent_extraction three ht
  exact IntervalCrown.Frame.full_operation_not_core three G hm
    ⟨t.pushRenames 1, hcore, fun values => (hvalue values).trans (he values)⟩

end KFOL.Core.GrayCrown
