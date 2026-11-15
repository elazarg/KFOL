module

public import KFOL.Definitions.BichainEssential

/-! # A single source separates every compatible cube

The source is chosen once from a Boolean separating pair. The same occurrence
then survives every compatible marked cube, even when observer union is present.
-/

@[expose] public section
namespace KFOL.Bichain

namespace Value

private theorem compatible_inf : ∀ a a' y y' : Value,
    (a = .c → a' ≠ .b) → (y = .c → y' ≠ .b) →
    inf a y = .c → inf a' y' ≠ .b := by decide +kernel

private theorem compatible_sup : ∀ a a' y y' : Value,
    (a = .c → a' ≠ .b) → (y = .c → y' ≠ .b) →
    sup a y = .c → sup a' y' ≠ .b := by decide +kernel

private theorem compatible_union : ∀ a a' y y' : Value,
    (a = .c → a' ≠ .b) → (y = .c → y' ≠ .b) →
    union a y = .c → union a' y' ≠ .b := by decide +kernel

private theorem inf_eq_c : ∀ a y : Value, inf a y = .c ↔ a = .c ∧ y = .c :=
  by decide +kernel
private theorem inf_eq_b : ∀ a y : Value, inf a y = .b ↔ a = .b ∨ y = .b :=
  by decide +kernel
private theorem sup_eq_c : ∀ a y : Value, sup a y = .c ↔ a = .c ∨ y = .c :=
  by decide +kernel
private theorem sup_eq_b : ∀ a y : Value, sup a y = .b ↔ a = .b ∧ y = .b :=
  by decide +kernel
private theorem union_eq_c : ∀ a y : Value, union a y = .c ↔ a = .c ∧ y = .c :=
  by decide +kernel
private theorem union_eq_b : ∀ a y : Value, union a y = .b ↔ a = .b ∧ y = .b :=
  by decide +kernel

private theorem inf_possible_left : ∀ a : Value, a ≠ .b → inf .possible a = .possible :=
  by decide +kernel
private theorem inf_possible_right : ∀ a : Value, a ≠ .b → inf a .possible = .possible :=
  by decide +kernel
private theorem sup_possible_left : ∀ a : Value, a ≠ .c → sup .possible a = .possible :=
  by decide +kernel
private theorem sup_possible_right : ∀ a : Value, a ≠ .c → sup a .possible = .possible :=
  by decide +kernel

end Value

namespace Term

variable {Var : Type*}

/-- The endpoint compatibility relation is preserved by all three operations. -/
theorem endpoint_compatible (t : Term Var) (v w : Var → Value)
    (h : ∀ j, v j = .c → w j ≠ .b) : t.eval v = .c → t.eval w ≠ .b := by
  induction t with
  | var j => exact h j
  | inf s t ihs iht => exact Value.compatible_inf _ _ _ _ ihs iht
  | sup s t ihs iht => exact Value.compatible_sup _ _ _ _ ihs iht
  | union s t ihs iht => exact Value.compatible_union _ _ _ _ ihs iht

private theorem eval_ne_b (t : Term Var) (A : Var → Bool) (v : Var → Value)
    (hA : t.eval (fun j => Value.ofBool (A j)) = .c)
    (h : ∀ j, A j = true → v j ≠ .b) : t.eval v ≠ .b := by
  apply endpoint_compatible t _ v _ hA
  intro j hj
  cases ha : A j <;> simp_all [Value.ofBool]

private theorem eval_ne_c (t : Term Var) (B : Var → Bool) (v : Var → Value)
    (hB : t.eval (fun j => Value.ofBool (B j)) = .b)
    (h : ∀ j, v j = .c → B j = true) : t.eval v ≠ .c := by
  intro hv
  have hh := endpoint_compatible t v (fun j => Value.ofBool (B j)) (by
    intro j hj
    rw [h j hj]
    decide) hv
  exact hh hB

/-- One separating source works simultaneously for every compatible input.
The same source is chosen before any marked cube is presented. -/
theorem stable_separating_source (t : Term Var) (A B : Var → Bool)
    (hA : t.eval (fun j => Value.ofBool (A j)) = .c)
    (hB : t.eval (fun j => Value.ofBool (B j)) = .b) :
    ∃ j, A j = true ∧ B j = false ∧ ∀ v : Var → Value,
      (∀ i, A i = true → v i ≠ .b) →
      (∀ i, v i = .c → B i = true) → v j = .possible → t.eval v = .possible := by
  induction t with
  | var j =>
    refine ⟨j, ?_, ?_, fun _ _ _ hj => hj⟩
    · cases ha : A j <;> simp_all [eval, Value.ofBool]
    · cases hb : B j <;> simp_all [eval, Value.ofBool]
  | inf s t ihs iht =>
    obtain ⟨hsA, htA⟩ := (Value.inf_eq_c _ _).mp hA
    rcases (Value.inf_eq_b _ _).mp hB with hsB | htB
    · obtain ⟨j, hjA, hjB, hj⟩ := ihs hsA hsB
      refine ⟨j, hjA, hjB, ?_⟩
      intro v hvA hvB hvj
      change Value.inf (s.eval v) (t.eval v) = .possible
      rw [hj v hvA hvB hvj]
      exact Value.inf_possible_left _ (eval_ne_b t A v htA hvA)
    · obtain ⟨j, hjA, hjB, hj⟩ := iht htA htB
      refine ⟨j, hjA, hjB, ?_⟩
      intro v hvA hvB hvj
      change Value.inf (s.eval v) (t.eval v) = .possible
      rw [hj v hvA hvB hvj]
      exact Value.inf_possible_right _ (eval_ne_b s A v hsA hvA)
  | sup s t ihs iht =>
    obtain ⟨hsB, htB⟩ := (Value.sup_eq_b _ _).mp hB
    rcases (Value.sup_eq_c _ _).mp hA with hsA | htA
    · obtain ⟨j, hjA, hjB, hj⟩ := ihs hsA hsB
      refine ⟨j, hjA, hjB, ?_⟩
      intro v hvA hvB hvj
      change Value.sup (s.eval v) (t.eval v) = .possible
      rw [hj v hvA hvB hvj]
      exact Value.sup_possible_left _ (eval_ne_c t B v htB hvB)
    · obtain ⟨j, hjA, hjB, hj⟩ := iht htA htB
      refine ⟨j, hjA, hjB, ?_⟩
      intro v hvA hvB hvj
      change Value.sup (s.eval v) (t.eval v) = .possible
      rw [hj v hvA hvB hvj]
      exact Value.sup_possible_right _ (eval_ne_c s B v hsB hvB)
  | union s t ihs _ =>
    obtain ⟨hsA, _⟩ := (Value.union_eq_c _ _).mp hA
    obtain ⟨hsB, _⟩ := (Value.union_eq_b _ _).mp hB
    obtain ⟨j, hjA, hjB, hj⟩ := ihs hsA hsB
    refine ⟨j, hjA, hjB, ?_⟩
    intro v hvA hvB hvj
    change Value.union (s.eval v) (t.eval v) = .possible
    rw [hj v hvA hvB hvj]
    rfl

end Term
end KFOL.Bichain
