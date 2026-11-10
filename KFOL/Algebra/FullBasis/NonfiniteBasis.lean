module

public import KFOL.Algebra.FullBasis.Signatures
public import KFOL.Core.NonfiniteBasis
public import Mathlib.Data.Fintype.Perm

/-! # Neither named winners nor role permutations restore a finite basis -/

@[expose] public section
namespace KFOL.FullBasis
universe u
variable {Role : Type u} [DecidableEq Role] [Finite Role]

theorem finite_arity_countermodels (three : Fin 3 ↪ Role) (n : ℕ) :
    ∃ (B : Type u)
      (full : (Equational.language (Equational.FullSymbol Role)).Structure B)
      (publicChoice : (Equational.language (Equational.PublicSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      (∀ e : Equational.Identity (Equational.FullSymbol Role), e.arity ≤ n →
        (let _ := Equational.fullStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B full) ∧
      (∀ e : Equational.Identity (Equational.PublicSymbol Role), e.arity ≤ n →
        (let _ := Equational.publicStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B publicChoice) ∧
      (let _ := Equational.fullStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance full) ∧
      (let _ := Equational.publicStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance publicChoice) := by
  classical
  obtain ⟨M,str,hne,hfinite,_,hnot,hlocal⟩ := Core.Grid.finite_local_countermodel three (n + 1)
  let _ := str
  let _ := hne
  let _ := hfinite
  let _ := Equational.coreStructure Role
  have small (e : Equational.Identity (Equational.CoreSymbol Role)) (arity : e.arity ≤ n + 1)
      (valid : let _ := Equational.coreStructure Role; e.Holds (WinnerSet Role)) : e.Holds M := by
    apply e.holds_of_local_variety (n + 1) _ valid hlocal
    exact (show e.variableCount ≤ e.arity by
      simpa only [Equational.Identity.variableCount, Fintype.card_fin] using
        Finset.card_le_univ e.support).trans arity
  refine ⟨Envelope.Carrier Role M, Envelope.structureOf, Envelope.publicStructureOf,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact Envelope.full_small_identities three (Classical.arbitrary M) n small
  · exact Envelope.public_small_identities three (Classical.arbitrary M) n small
  · intro h
    exact hnot (Envelope.core_variety_of_full h)
  · intro h
    exact hnot (Envelope.core_variety_of_public h)

theorem finite_countermodels (three : Fin 3 ↪ Role) (n : ℕ) :
    ∃ (B : Type u)
      (full : (Equational.language (Equational.FullSymbol Role)).Structure B)
      (publicChoice : (Equational.language (Equational.PublicSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      (∀ e : Equational.Identity (Equational.FullSymbol Role), e.variableCount ≤ n →
        (let _ := Equational.fullStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B full) ∧
      (∀ e : Equational.Identity (Equational.PublicSymbol Role), e.variableCount ≤ n →
        (let _ := Equational.publicStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B publicChoice) ∧
      (let _ := Equational.fullStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance full) ∧
      (let _ := Equational.publicStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance publicChoice) := by
  classical
  obtain ⟨B,full,publicChoice,hne,hf,smallFull,smallPublic,notFull,notPublic⟩ :=
    finite_arity_countermodels three n
  let _ := full
  let _ := publicChoice
  let _ := Equational.fullStructure Role
  let _ := Equational.publicStructure Role
  let _ : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton (three 0)⟩
  refine ⟨B,full,publicChoice,hne,hf,?_,?_,notFull,notPublic⟩
  · intro e bound valid
    exact e.holds_of_small_arity n bound valid smallFull
  · intro e bound valid
    exact e.holds_of_small_arity n bound valid smallPublic

theorem no_basis_with_variable_bound_full (three : Fin 3 ↪ Role) (n : ℕ)
    (T : Equational.Theory (Equational.FullSymbol Role)) (bound : Equational.HasVariableBound T n) :
    let _ := Equational.fullStructure Role
    ¬Equational.IsBasis (WinnerSet Role) T := by
  let _ := Equational.fullStructure Role
  change ¬Equational.IsBasis (WinnerSet Role) T
  intro hbasis
  obtain ⟨B,str,_,hne,_,small,_,hnot,_⟩ := finite_countermodels three n
  let _ := str
  let _ := hne
  apply hnot
  apply hbasis.inVariety
  exact fun e he => small e (bound e he) (hbasis.models e he)

theorem not_hasFiniteBasis_full (three : Fin 3 ↪ Role) :
    let _ := Equational.fullStructure Role
    ¬Equational.HasFiniteBasis (Equational.FullSymbol Role) (WinnerSet Role) := by
  let _ := Equational.fullStructure Role
  change ¬Equational.HasFiniteBasis (Equational.FullSymbol Role) (WinnerSet Role)
  rintro ⟨T,hfinite,hbasis⟩
  obtain ⟨n,bound⟩ := Equational.finite_hasVariableBound T hfinite
  exact no_basis_with_variable_bound_full three n T bound hbasis

theorem no_basis_with_variable_bound_public (three : Fin 3 ↪ Role) (n : ℕ)
    (T : Equational.Theory (Equational.PublicSymbol Role)) (bound : Equational.HasVariableBound T n) :
    let _ := Equational.publicStructure Role
    ¬Equational.IsBasis (WinnerSet Role) T := by
  let _ := Equational.publicStructure Role
  change ¬Equational.IsBasis (WinnerSet Role) T
  intro hbasis
  obtain ⟨B,_,str,hne,_,_,small,_,hnot⟩ := finite_countermodels three n
  let _ := str
  let _ := hne
  apply hnot
  apply hbasis.inVariety
  exact fun e he => small e (bound e he) (hbasis.models e he)

theorem not_hasFiniteBasis_public (three : Fin 3 ↪ Role) :
    let _ := Equational.publicStructure Role
    ¬Equational.HasFiniteBasis (Equational.PublicSymbol Role) (WinnerSet Role) := by
  let _ := Equational.publicStructure Role
  change ¬Equational.HasFiniteBasis (Equational.PublicSymbol Role) (WinnerSet Role)
  rintro ⟨T,hfinite,hbasis⟩
  obtain ⟨n,bound⟩ := Equational.finite_hasVariableBound T hfinite
  exact no_basis_with_variable_bound_public three n T bound hbasis

theorem not_hasFiniteBasis_both (three : Fin 3 ↪ Role) :
    (let _ := Equational.publicStructure Role
     ¬Equational.HasFiniteBasis (Equational.PublicSymbol Role) (WinnerSet Role)) ∧
    (let _ := Equational.fullStructure Role
     ¬Equational.HasFiniteBasis (Equational.FullSymbol Role) (WinnerSet Role)) :=
  ⟨not_hasFiniteBasis_public three, not_hasFiniteBasis_full three⟩

end KFOL.FullBasis
