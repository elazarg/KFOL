module

public import KFOL.Core.AtomicBasis.Cardinality
public import KFOL.Core.AtomicBasis.Reset
public import KFOL.Core.AtomicBasis.Variety
public import KFOL.Core.AtomicBasis.NearUnanimity

/-! # Explicit finite basis and least near-unanimity arity after ambiguity collapse -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

omit [Fintype Role] in
/-- Semantic completeness over arbitrary carriers implies syntactic completeness
for the independently defined equational derivation relation. -/
theorem isBasis (three : Fin 3 ↪ Role) (rs : List Role) (hn : rs.Nodup)
    (covers : ∀ r, r ∈ rs) :
    letI := structureOf Role
    Equational.IsBasis (Carrier Role) (theory three rs) := by
  let _ := structureOf Role
  exact (Equational.isBasis_iff_models (theory three rs)).mpr
    ⟨atomic_models three rs covers, fun _ _ _ => inVariety_of_models three rs hn⟩

/-- The displayed finite set is a complete three-variable basis, with exactly
one coverage law and one Birkhoff law per unordered owner pair. -/
theorem explicit_basis (three : Fin 3 ↪ Role) :
    letI := structureOf Role
    (theory three Finset.univ.toList).Finite ∧
    Equational.IsBasis (Carrier Role) (theory three Finset.univ.toList) ∧
    (theory three Finset.univ.toList).ncard =
      (Fintype.card Role)^2 + 3 * Fintype.card Role + 4 ∧
    Equational.HasVariableBound (theory three Finset.univ.toList) 3 := by
  let _ := structureOf Role
  exact ⟨theory_finite three _, isBasis three _ (Finset.nodup_toList _) (by simp),
    theory_ncard three _, theory_variableBound three _⟩

theorem hasFiniteBasis (three : Fin 3 ↪ Role) :
    letI := structureOf Role
    Equational.HasFiniteBasis (Equational.CoreSymbol Role) (Carrier Role) := by
  let _ := structureOf Role
  exact ⟨theory three Finset.univ.toList, (explicit_basis three).1, (explicit_basis three).2.1⟩

theorem least_nearUnanimity (three : Fin 3 ↪ Role) :
    NearUnanimity (nearUnanimityTerm three) ∧
    ∀ (n : ℕ), n ≤ Fintype.card Role →
      ∀ t : Equational.Term (Equational.CoreSymbol Role) (Fin n), ¬NearUnanimity t :=
  ⟨nearUnanimityTerm_isNearUnanimity three, fun _ hn => not_nearUnanimity_of_arity_le hn⟩

theorem subvariety (three : Fin 3 ↪ Role) (M : Type v) [Nonempty M]
    [(Equational.language (Equational.CoreSymbol Role)).Structure M] :
    (letI := structureOf Role;
      Equational.InVariety (Equational.CoreSymbol Role) (Carrier Role) M) ↔
    (letI := Equational.coreStructure Role;
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M) ∧
      ∀ x y : M, reset three Finset.univ.toList x y = y :=
  inVariety_iff three _ (Finset.nodup_toList _) (by simp)

/-- Existence and the sharp arity bound, without exposing implementation syntax
in the public statement's semantic dependency surface. -/
theorem nearUnanimity_arity (three : Fin 3 ↪ Role) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) (Fin (Fintype.card Role + 1)),
      NearUnanimity t) ∧
    ∀ (n : ℕ), n ≤ Fintype.card Role →
      ∀ t : Equational.Term (Equational.CoreSymbol Role) (Fin n), ¬NearUnanimity t :=
  ⟨⟨nearUnanimityTerm three, nearUnanimityTerm_isNearUnanimity three⟩,
    fun _ hn => not_nearUnanimity_of_arity_le hn⟩

end KFOL.Core.AtomicBasis
