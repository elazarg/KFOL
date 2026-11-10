module
public import KFOL.Complexity.OwnerHardnessTransport
@[expose] public section
namespace KFOL.Complexity.OwnerCountCompleteness
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
open KFOL.Complexity.OwnerHardnessTransport
variable {Role : Type} [Fintype Role] [DecidableEq Role]

def reduction (a b : Role) (formula : Reductions.CNF) : Owner.Term Role ℕ × Owner.Term Role ℕ :=
  (transport a b (Reductions.GuardedPair.equation formula).1,
    transport a b (Reductions.GuardedPair.equation formula).2)

omit [DecidableEq Role] in
theorem reduction_polyTime (a b : Role) : ComputableInPolyTime (reduction a b)
    Cslib.Complexity.encCNF OwnerLanguage.equationEncoding := by
  have h := (FiniteTermMachines.arguments_polyTime (σ := GuardedPair.Symbol)).comp
    GuardedPairMachines.reduction_polyTime
  have hl := (transport_polyTime a b).comp ((fst _ _).comp h)
  have hr := (transport_polyTime a b).comp ((snd _ _).comp h)
  exact FiniteTermMachines.equationRecode_polyTime.comp (hl.prod hr)

omit [Fintype Role] [DecidableEq Role] in
private theorem valid_reduction_iff (owners : Finset Role) (a b : Role)
    (ha : a ∈ owners) (hb : b ∈ owners) (relation : WinnerSet Role → WinnerSet Role → Prop)
    (formula : Reductions.CNF) : Owner.Valid owners relation (reduction a b formula) ↔
      ∀ valuation : ℕ → WinnerSet Role,
        relation ((Reductions.GuardedPair.equation formula).1.eval a b valuation)
          ((Reductions.GuardedPair.equation formula).2.eval a b valuation) := by
  simp only [Owner.Valid,reduction,eval_transport]
  exact and_iff_right (owners_transport a b owners ha hb _ ) |>.trans
    (and_iff_right (owners_transport a b owners ha hb _))

omit [DecidableEq Role] in
private theorem hard_transport (owners : Finset Role) (a b : Role) (ha : a ∈ owners) (hb : b ∈ owners)
    (relation : WinnerSet Role → WinnerSet Role → Prop) (reflexive : ∀ value, relation value value)
    (correct : ∀ formula : Reductions.CNF,
      (∀ valuation : ℕ → WinnerSet Role,
        relation ((Reductions.GuardedPair.equation formula).1.eval a b valuation)
          ((Reductions.GuardedPair.equation formula).2.eval a b valuation)) ↔ ¬Reductions.Satisfiable formula) :
    Cslib.Complexity.coNPHard encBits (Owner.Language owners relation) := by
  apply CNFHardness.coNPHard_encode OwnerLanguage.equationEncoding (Owner.Valid owners relation)
  apply CNFHardness.coNPHard_of_CNF (Owner.Valid owners relation) (reduction a b) (reduction_polyTime a b)
    (fun formula => (valid_reduction_iff owners a b ha hb relation formula).trans (correct formula))
    ((.var 0,.var 0) : Owner.Term Role ℕ × Owner.Term Role ℕ)
  exact ⟨trivial,trivial,fun valuation => reflexive (valuation 0)⟩

/-- Two distinct selected owners give complete equality hardness on original words. -/
theorem equality_language_coNPComplete (three : Fin 3 ↪ Role) (owners : Finset Role)
    (large : 1 < owners.card) : Cslib.Complexity.coNPComplete encBits (Owner.Language owners Eq) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp large
  obtain ⟨d,hda,hdb⟩ := exists_role_outside_pair three a b
  exact ⟨OwnerLanguage.language_mem_coNP owners a Eq,
    hard_transport owners a b ha hb Eq (fun _ => rfl)
      (Reductions.GuardedPair.equation_valid_iff_unsatisfiable a b d hab hda.symm hdb.symm)⟩

/-- A third observer has coNP-complete implication as soon as two distinct
selected owners differ from it. -/
theorem implication_language_coNPComplete (owners : Finset Role) (observer : Role)
    (large : 1 < (owners.erase observer).card) :
    Cslib.Complexity.coNPComplete encBits
      (Owner.Language owners (fun x y => observer ∈ x.val → observer ∈ y.val)) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp large
  have hma := Finset.mem_erase.mp ha
  have hmb := Finset.mem_erase.mp hb
  exact ⟨OwnerLanguage.language_mem_coNP owners observer _,
    hard_transport owners a b hma.2 hmb.2 _ (fun _ h => h)
      (Reductions.GuardedPair.third_role_observation_implication_valid_iff_unsatisfiable
        a b observer hab hma.1 hmb.1)⟩

/-- The same third-role lower bound holds for observational equivalence. -/
theorem equivalence_language_coNPComplete (owners : Finset Role) (observer : Role)
    (large : 1 < (owners.erase observer).card) :
    Cslib.Complexity.coNPComplete encBits
      (Owner.Language owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val)) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp large
  have hma := Finset.mem_erase.mp ha
  have hmb := Finset.mem_erase.mp hb
  exact ⟨OwnerLanguage.language_mem_coNP owners observer _,
    hard_transport owners a b hma.2 hmb.2 _ (fun _ => Iff.rfl)
      (Reductions.GuardedPair.third_role_observation_valid_iff_unsatisfiable
        a b observer hab hma.1 hmb.1)⟩
end KFOL.Complexity.OwnerCountCompleteness
