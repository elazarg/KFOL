module

public import KFOL.Core.AtomicBasis.Completeness
public import KFOL.Core.AtomicBasis.Soundness
public import KFOL.Core.ChoiceUnion.Laws

/-! # The atomic variety is the right-projection-reset subvariety of the core -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

variable {Role : Type u} [DecidableEq Role]

omit [DecidableEq Role] in
theorem winner_cover (i j : Role) (hij : i ≠ j) (x y : WinnerSet Role) :
    (WinnerSet.choice i x y).union (WinnerSet.choice j x y) = x.union y := by
  classical
  by_cases hxi : x = WinnerSet.singleton i <;>
    by_cases hxj : x = WinnerSet.singleton j <;>
    by_cases hyi : y = WinnerSet.singleton i <;>
    by_cases hyj : y = WinnerSet.singleton j
  all_goals simp_all [WinnerSet.choice]
  all_goals apply Subtype.ext
  all_goals ext r
  all_goals simp only [WinnerSet.val_union, Set.mem_union]
  all_goals tauto

omit [DecidableEq Role] in
theorem winner_birkhoff (i j : Role) (hij : i ≠ j) (x y : WinnerSet Role) :
    WinnerSet.choice i x (WinnerSet.choice j x y) =
      WinnerSet.choice j x (WinnerSet.choice i x y) := by
  classical
  by_cases hxi : x = WinnerSet.singleton i <;>
    by_cases hxj : x = WinnerSet.singleton j <;>
    by_cases hyi : y = WinnerSet.singleton i <;>
    by_cases hyj : y = WinnerSet.singleton j
  all_goals simp_all [WinnerSet.choice, WinnerSet.union_eq_singleton_iff]
  all_goals apply Subtype.ext
  all_goals ext r
  all_goals simp only [WinnerSet.val_union, Set.mem_union]
  all_goals tauto

omit [DecidableEq Role] in
/-- The lifting laws are consequences of the core theory, without reset projection. -/
theorem lifting_of_core {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role)
    (hm : letI := Equational.coreStructure Role;
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M) :
    LiftingLaws (join three) (operation (Role := Role) (M := M)) := by
  let _ := Equational.coreStructure Role
  refine ⟨Core.join_idem hm three, Core.join_comm hm three, Core.join_assoc hm three,
    Core.operation_idem hm, Core.operation_comm hm, Core.operation_assoc hm, ?_, ?_, ?_⟩
  · intro i x y z
    simpa using equation_of_inVariety hm
      (choiceTerm i (.var (0 : Fin 3)) (unionTerm three (.var 1) (.var 2)))
      (unionTerm three (choiceTerm i (.var 0) (.var 1)) (choiceTerm i (.var 0) (.var 2)))
      (fun v => by simpa only [realize_choice_winner, realize_union_winner, FirstOrder.Language.Term.realize_var] using
        Dissemilattice.winner_mul_add i (v 0) (v 1) (v 2)) ![x, y, z]
  · intro i j hij x y
    simpa using equation_of_inVariety hm
      (unionTerm three (choiceTerm i (.var (0 : Fin 2)) (.var 1))
        (choiceTerm j (.var 0) (.var 1))) (unionTerm three (.var 0) (.var 1))
      (fun v => by simpa only [realize_choice_winner, realize_union_winner, FirstOrder.Language.Term.realize_var] using
        winner_cover i j hij (v 0) (v 1)) ![x, y]
  · intro i j hij x y
    simpa using equation_of_inVariety hm
      (choiceTerm i (.var (0 : Fin 2)) (choiceTerm j (.var 0) (.var 1)))
      (choiceTerm j (.var 0) (choiceTerm i (.var 0) (.var 1)))
      (fun v => winner_birkhoff i j hij (v 0) (v 1)) ![x, y]

/-- Exact subvariety identification, in the original owned-choice signature. -/
theorem inVariety_iff {M : Type v} [Nonempty M]
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role) (rs : List Role) (hn : rs.Nodup) (covers : ∀ r, r ∈ rs) :
    (letI := structureOf Role;
      Equational.InVariety (Equational.CoreSymbol Role) (Carrier Role) M) ↔
    (letI := Equational.coreStructure Role;
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M) ∧
      ∀ x y : M, reset three rs x y = y := by
  let _ := structureOf Role
  let _ := Equational.coreStructure Role
  constructor
  · intro hm
    have hquot : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Carrier Role) :=
      ⟨inferInstance, fun e he => e.holds_of_surjective collapseHom (collapse_surjective three) he⟩
    exact ⟨hquot.trans hm, ((models_iff three rs).mp (hm.models (atomic_models three rs covers))).2⟩
  · rintro ⟨hm, hr⟩
    exact inVariety_of_models three rs hn ((models_iff three rs).mpr ⟨lifting_of_core three hm, hr⟩)

end KFOL.Core.AtomicBasis
