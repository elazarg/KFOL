module
public import KFOL.Complexity.RawSubsignatureMachines
public import KFOL.Complexity.CNFHardness
public import KFOL.Complexity.FiniteSignatureVerifier
@[expose] public section
namespace KFOL.Complexity.RawSubsignatureCompleteness
open Turing.MultiTapeTM
open RawSubsignatureMachines
variable {Role : Type} (selected : Finset (Raw.Operation Role))

/-- Every selected signature with two distinct operations contains one of
four native hard pairs; each actual CNF generator is machine-certified. -/
theorem coNPHard (three : Fin 3 ↪ Role) (hcard : 1 < selected.card) :
    Cslib.Complexity.coNPHard (equationEncoding selected) {equation | Raw.Valid selected equation} := by
  have htransport (reduction : Reductions.CNF → RawSubsignatureMachines.Tree selected × RawSubsignatureMachines.Tree selected)
      (runtime : Turing.MultiTapeTM.ComputableInPolyTime reduction RawPairMachines.cnfEncoding (equationEncoding selected))
      (correct : ∀ formula, Raw.Valid selected (reduction formula) ↔ ¬Reductions.Satisfiable formula) :
      Cslib.Complexity.coNPHard (equationEncoding selected) {equation | Raw.Valid selected equation} :=
    CNFHardness.coNPHard_of_CNF (Raw.Valid selected) reduction runtime correct
      ((.var 0, .var 0) : RawSubsignatureMachines.Tree selected × RawSubsignatureMachines.Tree selected) (fun _ => rfl)
  rcases Raw.exists_hard_pair selected hcard with ⟨hr, hu⟩ | ⟨a, b, hab, ha, hb⟩ | ⟨a, ha, hu⟩ | ⟨a, ha, hr⟩
  · exact htransport _ (resetUnion_polyTime selected hr hu) (Raw.Reduction.valid_resetUnion_iff selected three hr hu)
  · obtain ⟨c, hca, hcb⟩ := KFOL.exists_role_outside_pair three a b
    exact htransport _ (twoChoices_polyTime selected a b ha hb)
      (Raw.Reduction.valid_twoChoices_iff selected a b c hab hca.symm hcb ha hb)
  · obtain ⟨b, hba, _⟩ := KFOL.exists_role_outside_pair three a a
    obtain ⟨c, hca, hcb⟩ := KFOL.exists_role_outside_pair three a b
    exact htransport _ (choiceUnion_polyTime selected a ha hu)
      (Raw.Reduction.valid_choiceUnion_iff selected a b c hba.symm hca.symm hcb ha hu)
  · obtain ⟨b, hba, _⟩ := KFOL.exists_role_outside_pair three a a
    obtain ⟨c, hca, hcb⟩ := KFOL.exists_role_outside_pair three a b
    exact htransport _ (resetChoice_polyTime selected a ha hr)
      (Raw.Reduction.valid_resetChoice_iff selected a b c hba.symm hca.symm hcb.symm ha hr)

theorem mem_coNP [Fintype Role] (inhabitant : Role) :
    {equation | Raw.Valid selected equation} ∈ Cslib.Complexity.coNP (equationEncoding selected) := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language (Raw.Symbol selected)).Structure (WinnerSet Role) := Raw.structureOf selected
  exact FiniteSignatureVerifier.holds_mem_coNP (σ := Raw.Symbol selected) (Value := WinnerSet Role) Eq

theorem language_mem_coNP [Fintype Role] (inhabitant : Role) : Raw.Language selected ∈ Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language (Raw.Symbol selected)).Structure (WinnerSet Role) := Raw.structureOf selected
  exact FiniteSignatureVerifier.language_mem_coNP (σ := Raw.Symbol selected) (Value := WinnerSet Role) Eq

theorem coNPComplete [Fintype Role] (three : Fin 3 ↪ Role) (hcard : 1 < selected.card) :
    Cslib.Complexity.coNPComplete (equationEncoding selected) {equation | Raw.Valid selected equation} :=
  ⟨mem_coNP selected (three 0), coNPHard selected three hcard⟩

theorem language_coNPHard (three : Fin 3 ↪ Role) (hcard : 1 < selected.card) :
    Cslib.Complexity.coNPHard encBits (Raw.Language selected) :=
  CNFHardness.coNPHard_encode (equationEncoding selected) _ (coNPHard selected three hcard)

theorem language_coNPComplete [Fintype Role] (three : Fin 3 ↪ Role) (hcard : 1 < selected.card) :
    Cslib.Complexity.coNPComplete encBits (Raw.Language selected) :=
  ⟨language_mem_coNP selected (three 0), language_coNPHard selected three hcard⟩
end KFOL.Complexity.RawSubsignatureCompleteness
