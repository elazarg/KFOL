module

public import KFOL.Core.Exhaustion
public import Mathlib.Order.Lattice
public import Mathlib.Data.Fin.VecNotation

/-! # Derived join and owned semilattice laws in every core model -/

@[expose] public section

namespace KFOL.Core

universe u v w

open FirstOrder

variable {Role : Type u} {M : Type v}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

attribute [local instance] Equational.coreStructure

@[simp] theorem funMap_choice (r : Role) (args : Fin 2 → M) :
    FirstOrder.Language.Structure.funMap (L := Equational.language (Equational.CoreSymbol Role))
      (.choice r) args = operation r (args 0) (args 1) := by
  unfold operation
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

theorem hom_operation {N : Type w}
    [(Equational.language (Equational.CoreSymbol Role)).Structure N]
    (f : M →[Equational.language (Equational.CoreSymbol Role)] N)
    (r : Role) (x y : M) : f (operation r x y) = operation r (f x) (f y) := by
  have h := f.map_fun (Equational.CoreSymbol.choice r) (fun i : Fin 2 => if i = 0 then x else y)
  rw [funMap_choice r _, funMap_choice r _] at h
  exact h

@[simp] theorem realize_choice (r : Role) {Var : Type w}
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → M) :
    (choiceTerm r s t).realize v = operation r (s.realize v) (t.realize v) := by
  change FirstOrder.Language.Structure.funMap _ (fun i => (if i = 0 then s else t).realize v) = _
  unfold operation
  congr 1
  funext i
  split <;> rfl

@[simp] theorem realize_union (three : Fin 3 ↪ Role) {Var : Type w}
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → M) :
    (unionTerm three s t).realize v = join three (s.realize v) (t.realize v) := by
  simp only [unionTerm, realize_choice, join]

@[simp] theorem operation_winner (r : Role) (x y : WinnerSet Role) :
    operation r x y = WinnerSet.choice r x y := rfl

theorem join_winner (three : Fin 3 ↪ Role) (x y : WinnerSet Role) :
    join three x y = x.union y := by
  exact WinnerSet.three_owner_union _ _ _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide))

/-- Transfer any finite displayed core equation to an arbitrary member of
the variety. Satisfaction remains the independently defined identity notion. -/
theorem equation_of_inVariety
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    {n : ℕ} (s t : Equational.Term (Equational.CoreSymbol Role) (Fin n))
    (hv : ∀ v : Fin n → WinnerSet Role, s.realize v = t.realize v) (v : Fin n → M) :
    s.realize v = t.realize v := hM.2 ⟨n, s, t⟩ hv v

theorem operation_idem
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (r : Role) (x : M) : operation r x x = x := by
  simpa using equation_of_inVariety hM
    (choiceTerm r (.var (0 : Fin 1)) (.var 0)) (.var 0)
    (fun v => WinnerSet.choice_self (v 0) r) (fun _ => x)

theorem operation_comm
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (r : Role) (x y : M) : operation r x y = operation r y x := by
  simpa using equation_of_inVariety hM
    (choiceTerm r (.var (0 : Fin 2)) (.var 1)) (choiceTerm r (.var 1) (.var 0))
    (fun v => WinnerSet.choice_comm (v 0) (v 1) r) ![x, y]

private theorem choice_assoc_winner (r : Role) (x y z : WinnerSet Role) :
    WinnerSet.choice r (WinnerSet.choice r x y) z =
      WinnerSet.choice r x (WinnerSet.choice r y z) := by
  classical
  by_cases hx : x = WinnerSet.singleton r <;> by_cases hy : y = WinnerSet.singleton r <;>
    by_cases hz : z = WinnerSet.singleton r
  all_goals simp_all [WinnerSet.choice, WinnerSet.union_eq_singleton_iff]
  apply Subtype.ext
  exact Set.union_assoc _ _ _

theorem operation_assoc
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (r : Role) (x y z : M) : operation r (operation r x y) z = operation r x (operation r y z) := by
  simpa using equation_of_inVariety hM
    (choiceTerm r (choiceTerm r (.var (0 : Fin 3)) (.var 1)) (.var 2))
    (choiceTerm r (.var 0) (choiceTerm r (.var 1) (.var 2)))
    (fun v => choice_assoc_winner r (v 0) (v 1) (v 2)) ![x, y, z]

theorem join_idem (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (x : M) : join three x x = x := by
  simpa using equation_of_inVariety hM (unionTerm three (.var (0 : Fin 1)) (.var 0)) (.var 0)
    (fun v => by rw [realize_union_winner]; exact WinnerSet.union_self (v 0)) (fun _ => x)

theorem join_comm (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (x y : M) : join three x y = join three y x := by
  simpa using equation_of_inVariety hM
    (unionTerm three (.var (0 : Fin 2)) (.var 1)) (unionTerm three (.var 1) (.var 0))
    (fun v => by rw [realize_union_winner, realize_union_winner]; exact WinnerSet.union_comm _ _) ![x, y]

theorem join_assoc (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (x y z : M) : join three (join three x y) z = join three x (join three y z) := by
  simpa using equation_of_inVariety hM
    (unionTerm three (unionTerm three (.var (0 : Fin 3)) (.var 1)) (.var 2))
    (unionTerm three (.var 0) (unionTerm three (.var 1) (.var 2)))
    (fun v => by
      simp only [realize_union_winner]
      apply Subtype.ext
      exact Set.union_assoc _ _ _) ![x, y, z]

/-- The order used by the core proof is the derived neutral join order,
not the order of any individual owner's semilattice operation. -/
@[instance_reducible] def modelSemilattice
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) : SemilatticeSup M :=
  letI : Max M := ⟨join three⟩
  SemilatticeSup.mk' (join_comm hM three) (join_assoc hM three) (join_idem hM three)

theorem operation_join_bound
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (r : Role) (x y : M) :
    join three (operation r x y) (join three x y) = join three x y := by
  simpa using equation_of_inVariety hM
    (unionTerm three (choiceTerm r (.var (0 : Fin 2)) (.var 1))
      (unionTerm three (.var 0) (.var 1)))
    (unionTerm three (.var 0) (.var 1)) (fun v => by
      simp only [realize_union_winner]
      apply Subtype.ext
      apply Set.union_eq_right.mpr
      classical
      change (WinnerSet.choice r (v 0) (v 1)).val ⊆ (v 0).val ∪ (v 1).val
      by_cases h : v 0 = WinnerSet.singleton r ∨ v 1 = WinnerSet.singleton r
      · simp only [WinnerSet.choice, ite_eq_left h]
        rcases h with h | h
        · exact h ▸ Set.subset_union_left
        · exact h ▸ Set.subset_union_right
      · simp only [WinnerSet.choice, ite_eq_right h, WinnerSet.val_union]
        exact subset_rfl) ![x, y]

/-- The lower ideal of e is a genuine core subalgebra. -/
def ideal (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (e : M) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure M where
  carrier := {x | join three x e = e}
  fun_mem := by
    intro n f args hargs
    cases f with
    | choice r =>
      let _ := modelSemilattice hM three
      change join three (FirstOrder.Language.Structure.funMap _ args) e = e
      rw [funMap_choice]
      change operation r (args 0) (args 1) ≤ e
      have hbound : operation r (args 0) (args 1) ≤ args 0 ⊔ args 1 :=
        operation_join_bound hM three r _ _
      exact hbound.trans (sup_le (hargs 0) (hargs 1))

/-- Semilattice absorption used in the typed-cover marker induction. -/
theorem operation_absorb_left
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (r : Role) (e c : M) : operation r e (operation r e c) = operation r e c := by
  rw [← operation_assoc hM, operation_idem hM]

theorem operation_absorb_factors
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (r : Role) (e c d : M) (h : operation r e (operation r c d) = e) :
    operation r e c = e ∧ operation r e d = e := by
  have left (c d : M) (h : operation r e (operation r c d) = e) : operation r e c = e := by
    calc
      operation r e c = operation r (operation r e (operation r c d)) c := by rw [h]
      _ = operation r e (operation r (operation r c d) c) := operation_assoc hM r _ _ _
      _ = operation r e (operation r c (operation r c d)) := by
        rw [operation_comm hM r (operation r c d) c]
      _ = operation r e (operation r c d) := by rw [operation_absorb_left hM]
      _ = e := h
  exact ⟨left c d h, left d c (by rwa [operation_comm hM r d c])⟩

end KFOL.Core
