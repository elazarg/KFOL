module
public import KFOL.Complexity.ResetUnionHardness
public import KFOL.Complexity.GuardedPairHardness
public import KFOL.Complexity.FullHardness
@[expose] public section
namespace KFOL.Complexity.Canonicalization
open Turing.MultiTapeTM ComputableInPolyTime

private theorem collapse_of_hard_mem_P {Target : Type} (encoding : Target ↪ List Bool) (theory : Set Target)
    (hard : Cslib.Complexity.coNPHard encoding theory) (decidable : theory ∈ Cslib.Complexity.P encoding) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits := by
  apply Set.Subset.antisymm Cslib.Complexity.P_subset_NP
  intro language hnp
  have hco : languageᶜ ∈ Cslib.Complexity.coNP encBits := by
    change languageᶜᶜ ∈ Cslib.Complexity.NP encBits
    simpa only [compl_compl] using hnp
  have hred := hard encBits languageᶜ hco
  have hp := hred.mem_P decidable
  simpa only [compl_compl] using Cslib.Complexity.compl_mem_P hp

/-- A complete invariant computed in polynomial time decides equality by
comparing its two actual output words. CoNP hardness then implies P = NP. -/
theorem implies_P_eq_NP {Tree : Type} (termEncoding : Tree ↪ List Bool)
    (equationEncoding : (Tree × Tree) ↪ List Bool) (relation : Tree → Tree → Prop)
    (arguments : ComputableInPolyTime (id : Tree × Tree → _) equationEncoding (encPair termEncoding termEncoding))
    (hard : Cslib.Complexity.coNPHard equationEncoding {pair | relation pair.1 pair.2})
    (canonicalize : Tree → List Bool)
    (runtime : ComputableInPolyTime canonicalize termEncoding encBits)
    (complete : ∀ left right, canonicalize left = canonicalize right ↔ relation left right) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits := by
  have hl := runtime.comp ((fst termEncoding termEncoding).comp arguments)
  have hr := runtime.comp ((snd termEncoding termEncoding).comp arguments)
  have h := decide_eq' hl hr
  apply collapse_of_hard_mem_P equationEncoding _ hard
  refine ⟨fun pair => decide (canonicalize pair.1 = canonicalize pair.2), h, ?_⟩
  intro pair
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
  exact (complete pair.1 pair.2).symm

/-- Polynomial comparison of canonical outputs suffices; comparison need not
be literal word equality. Both output construction and comparison are charged. -/
theorem comparator_implies_P_eq_NP {Tree : Type}
    (termEncoding : Tree ↪ List Bool) (equationEncoding : (Tree × Tree) ↪ List Bool)
    (relation : Tree → Tree → Prop)
    (arguments : ComputableInPolyTime (id : Tree × Tree → _) equationEncoding (encPair termEncoding termEncoding))
    (hard : Cslib.Complexity.coNPHard equationEncoding {pair | relation pair.1 pair.2})
    (canonicalize : Tree → List Bool)
    (runtime : ComputableInPolyTime canonicalize termEncoding encBits)
    (compare : List Bool × List Bool → Bool)
    (comparison : ComputableInPolyTime compare (encPair encBits encBits) encBool)
    (complete : ∀ left right, compare (canonicalize left, canonicalize right) = true ↔ relation left right) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits := by
  have hl := runtime.comp ((fst termEncoding termEncoding).comp arguments)
  have hr := runtime.comp ((snd termEncoding termEncoding).comp arguments)
  have h := comparison.comp (hl.prod hr)
  apply collapse_of_hard_mem_P equationEncoding _ hard
  refine ⟨fun pair => compare (canonicalize pair.1, canonicalize pair.2), h, ?_⟩
  intro pair
  exact (complete pair.1 pair.2).symm

/-- No polynomial-time complete word invariant for the actual reset/union
identity theory exists unless the machine-level classes P and NP coincide. -/
theorem reset_union {Role : Type} (three : Fin 3 ↪ Role)
    (canonicalize : KFOL.ResetUnion.Term ℕ → List Bool)
    (runtime : ComputableInPolyTime canonicalize ResetUnionMachines.termEncoding encBits)
    (complete : ∀ left right, canonicalize left = canonicalize right ↔
      ∀ valuation : ℕ → WinnerSet Role, left.eval valuation = right.eval valuation) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits :=
  implies_P_eq_NP ResetUnionMachines.termEncoding ResetUnionMachines.equationEncoding
    (fun left right => ∀ valuation : ℕ → WinnerSet Role, left.eval valuation = right.eval valuation)
    ResetUnionMachines.arguments_polyTime (ResetUnionHardness.coNPHard three) canonicalize runtime complete

/-- The same obstruction applies to the native two-ternary-only H signature,
without a primitive reset operation. -/
theorem guarded_pair {Role : Type} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (canonicalize : GuardedPairMachines.Tree → List Bool)
    (runtime : ComputableInPolyTime canonicalize GuardedPairMachines.termEncoding encBits)
    (complete : ∀ left right, canonicalize left = canonicalize right ↔
      ∀ valuation : ℕ → WinnerSet Role, KFOL.GuardedPair.Term.eval a b left valuation = KFOL.GuardedPair.Term.eval a b right valuation) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits :=
  implies_P_eq_NP GuardedPairMachines.termEncoding GuardedPairMachines.equationEncoding
    (fun left right => ∀ valuation : ℕ → WinnerSet Role, KFOL.GuardedPair.Term.eval a b left valuation = KFOL.GuardedPair.Term.eval a b right valuation)
    FiniteTermMachines.arguments_polyTime (GuardedPairHardness.coNPHard a b d hab had hbd) canonicalize runtime complete
end KFOL.Complexity.Canonicalization

namespace KFOL.Complexity.Canonicalization
open Turing.MultiTapeTM ComputableInPolyTime

/-- For every role type containing three distinct roles, a polynomial-time
canonicalizer and polynomial-time comparator on the actual original core
would collapse the machine-level classes P and NP. No runtime behavior is
required outside the core subtype. -/
theorem original_core_comparator {K : ℕ} (a b d : Fin K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (canonicalize : FullHardness.CoreTerm K → List Bool)
    (runtime : ComputableInPolyTime canonicalize (FullHardness.originalCoreTermEncoding K) encBits)
    (compare : List Bool × List Bool → Bool)
    (comparison : ComputableInPolyTime compare (encPair encBits encBits) encBool)
    (complete : ∀ left right : FullHardness.CoreTerm K,
      compare (canonicalize left,canonicalize right) = true ↔
        ∀ v : ℕ → WinnerSet (Fin K),left.val.eval v = right.val.eval v) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits := by
  apply comparator_implies_P_eq_NP RawPairMachines.termEncoding RawPairMachines.equationEncoding
    (fun left right => ∀ v : ℕ → WinnerSet (Fin K),
      RawPair.Term.eval (WinnerSet.choice a) (WinnerSet.choice b) left v =
        RawPair.Term.eval (WinnerSet.choice a) (WinnerSet.choice b) right v)
    FiniteTermMachines.arguments_polyTime
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
    (fun t => canonicalize ⟨FullHardness.ofPair a b t,FullHardness.ofPair_isCore a b t⟩)
    (runtime.comp (FullHardness.ofPair_core_polyTime a b)) compare comparison
  intro left right
  simpa only [FullHardness.eval_ofPair] using complete
    ⟨FullHardness.ofPair a b left,FullHardness.ofPair_isCore a b left⟩
    ⟨FullHardness.ofPair a b right,FullHardness.ofPair_isCore a b right⟩

/-- Literal equality of canonical output words is the special case with the
standard native polynomial-time word comparator. -/
theorem original_core {K : ℕ} (a b d : Fin K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (canonicalize : FullHardness.CoreTerm K → List Bool)
    (runtime : ComputableInPolyTime canonicalize (FullHardness.originalCoreTermEncoding K) encBits)
    (complete : ∀ left right : FullHardness.CoreTerm K,
      canonicalize left = canonicalize right ↔
        ∀ v : ℕ → WinnerSet (Fin K),left.val.eval v = right.val.eval v) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits := by
  apply original_core_comparator a b d hab had hbd canonicalize runtime
    (fun p => decide (p.1 = p.2)) (decide_eq' (fst encBits encBits) (snd encBits encBits))
  intro left right
  simpa only [decide_eq_true_eq] using complete left right
end KFOL.Complexity.Canonicalization
