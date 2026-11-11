module

public import KFOL.Core.OwnerElimination
public import KFOL.Core.RoleRestriction
public import Mathlib.Data.Fin.VecNotation

/-! # A six-valuation invariant of the core

The finite owner-elimination certificate is checked in the kernel. Restricting
roles then transports its membership consequence to every role set containing
three distinct owners.
-/

@[expose] public section
namespace KFOL.Core.SixValuation
open WinnerSet WinnerSet.StatusModel OwnerElimination

def values : Fin 6 → Fin 5 → StatusModel.Value (Fin 3) :=
  ![![⟨{2}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩, ⟨{0}, by decide⟩, ⟨{1}, by decide⟩],
    ![⟨{1}, by decide⟩, ⟨{1}, by decide⟩, ⟨{1, 2}, by decide⟩, ⟨{0}, by decide⟩, ⟨{2}, by decide⟩],
    ![⟨{1}, by decide⟩, ⟨{0}, by decide⟩, ⟨{2}, by decide⟩, ⟨{2}, by decide⟩, ⟨{2}, by decide⟩],
    ![⟨{2}, by decide⟩, ⟨{0}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩, ⟨{1}, by decide⟩],
    ![⟨{2}, by decide⟩, ⟨{1, 2}, by decide⟩, ⟨{1, 2}, by decide⟩, ⟨{1}, by decide⟩, ⟨{0}, by decide⟩],
    ![⟨{0}, by decide⟩, ⟨{2}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩, ⟨{0, 2}, by decide⟩]]

private def clauses : Fin 32 → Clause (Fin 6) (Fin 3) :=
  ![⟨some (0, 0), {(1, 0), (2, 1), (3, 0), (4, 0), (5, 1)}⟩,
    ⟨none, {(2, 1), (2, 2), (3, 0)}⟩,
    ⟨none, {(2, 1), (3, 0), (5, 1), (5, 2)}⟩,
    ⟨some (0, 0), {(3, 0), (3, 2), (5, 1)}⟩,
    ⟨some (0, 2), {(3, 0), (3, 2), (5, 1)}⟩,
    ⟨some (0, 0), {(1, 0), (1, 2), (2, 1), (3, 0), (5, 1)}⟩,
    ⟨some (0, 2), {(1, 0), (1, 2), (2, 1), (3, 0), (5, 1)}⟩,
    ⟨some (0, 2), {(1, 0), (2, 1), (3, 0), (4, 0), (4, 2), (5, 1)}⟩,
    ⟨some (0, 0), {(4, 0), (4, 1)}⟩,
    ⟨some (0, 1), {(4, 0), (4, 1)}⟩,
    ⟨some (0, 0), {(1, 0), (1, 1), (4, 0)}⟩,
    ⟨some (0, 1), {(1, 0), (1, 1), (4, 0)}⟩,
    ⟨some (0, 0), {(1, 0), (2, 0), (2, 1), (4, 0)}⟩,
    ⟨some (0, 1), {(1, 0), (2, 0), (2, 1), (4, 0)}⟩,
    ⟨some (0, 0), {(1, 0), (2, 1), (3, 0), (3, 1), (4, 0)}⟩,
    ⟨some (0, 1), {(1, 0), (2, 1), (3, 0), (3, 1), (4, 0)}⟩,
    ⟨some (0, 1), {(1, 0), (2, 1), (3, 0), (4, 0), (5, 0), (5, 1)}⟩,
    ⟨none, {(2, 0), (2, 1), (2, 2)}⟩,
    ⟨none, {(5, 0), (5, 1), (5, 2)}⟩,
    ⟨none, {(2, 0), (2, 1), (5, 1), (5, 2)}⟩,
    ⟨none, {(3, 0), (3, 1), (3, 2)}⟩,
    ⟨none, {(3, 0), (3, 2), (5, 1), (5, 2)}⟩,
    ⟨none, {(3, 0), (3, 2), (5, 0), (5, 1)}⟩,
    ⟨none, {(1, 0), (1, 1), (1, 2)}⟩,
    ⟨none, {(1, 0), (1, 2), (2, 0), (2, 1)}⟩,
    ⟨none, {(1, 0), (1, 2), (2, 1), (3, 0), (3, 1)}⟩,
    ⟨none, {(1, 0), (1, 2), (2, 1), (3, 0), (5, 0), (5, 1)}⟩,
    ⟨none, {(4, 0), (4, 1), (4, 2)}⟩,
    ⟨none, {(1, 0), (1, 1), (4, 0), (4, 2)}⟩,
    ⟨none, {(1, 0), (2, 0), (2, 1), (4, 0), (4, 2)}⟩,
    ⟨none, {(1, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 2)}⟩,
    ⟨none, {(1, 0), (2, 1), (3, 0), (4, 0), (4, 2), (5, 0), (5, 1)}⟩]

private def family : Finset (Clause (Fin 6) (Fin 3)) := Finset.univ.image clauses

private def orders (C : Clause (Fin 6) (Fin 3)) (r : Fin 3) : List (Atom (Fin 6) (Fin 3)) :=
  if C = clauses 0 then (![[(2, 1), (5, 1)], [(3, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 1), (3, 0), (5, 1)]]) r else
  if C = clauses 1 then (![[(2, 1), (2, 2)], [(2, 2), (3, 0)], [(2, 1), (3, 0)]]) r else
  if C = clauses 2 then (![[(2, 1), (5, 1), (5, 2)], [(5, 2), (3, 0)], [(5, 1), (2, 1), (3, 0)]]) r else
  if C = clauses 3 then (![[(3, 2), (5, 1)], [(3, 0), (3, 2)], [(3, 0), (5, 1)]]) r else
  if C = clauses 4 then (![[(3, 2), (5, 1)], [(3, 0), (3, 2)], [(3, 0), (5, 1)]]) r else
  if C = clauses 5 then (![[(2, 1), (5, 1), (1, 2)], [(3, 0), (1, 0), (1, 2)], [(1, 0), (2, 1), (3, 0), (5, 1)]]) r else
  if C = clauses 6 then (![[(1, 2), (2, 1), (5, 1)], [(3, 0), (1, 0), (1, 2)], [(1, 0), (2, 1), (3, 0), (5, 1)]]) r else
  if C = clauses 7 then (![[(2, 1), (5, 1), (4, 2)], [(3, 0), (1, 0), (4, 0), (4, 2)], [(4, 0), (1, 0), (2, 1), (3, 0), (5, 1)]]) r else
  if C = clauses 8 then (![[(4, 1)], [(4, 0)], [(4, 0), (4, 1)]]) r else
  if C = clauses 9 then (![[(4, 1)], [(4, 0)], [(4, 0), (4, 1)]]) r else
  if C = clauses 10 then (![[(1, 1)], [(1, 0), (4, 0)], [(4, 0), (1, 0), (1, 1)]]) r else
  if C = clauses 11 then (![[(1, 1)], [(1, 0), (4, 0)], [(4, 0), (1, 0), (1, 1)]]) r else
  if C = clauses 12 then (![[(2, 1)], [(2, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 0), (2, 1)]]) r else
  if C = clauses 13 then (![[(2, 1)], [(2, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 0), (2, 1)]]) r else
  if C = clauses 14 then (![[(2, 1), (3, 1)], [(3, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 1), (3, 0), (3, 1)]]) r else
  if C = clauses 15 then (![[(2, 1), (3, 1)], [(3, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 1), (3, 0), (3, 1)]]) r else
  if C = clauses 16 then (![[(2, 1), (5, 1)], [(5, 0), (3, 0), (1, 0), (4, 0)], [(4, 0), (1, 0), (2, 1), (3, 0), (5, 0), (5, 1)]]) r else
  if C = clauses 17 then (![[(2, 1), (2, 2)], [(2, 0), (2, 2)], [(2, 0), (2, 1)]]) r else
  if C = clauses 18 then (![[(5, 1), (5, 2)], [(5, 0), (5, 2)], [(5, 0), (5, 1)]]) r else
  if C = clauses 19 then (![[(2, 1), (5, 1), (5, 2)], [(2, 0), (5, 2)], [(5, 1), (2, 0), (2, 1)]]) r else
  if C = clauses 20 then (![[(3, 1), (3, 2)], [(3, 0), (3, 2)], [(3, 0), (3, 1)]]) r else
  if C = clauses 21 then (![[(3, 2), (5, 1), (5, 2)], [(5, 2), (3, 0), (3, 2)], [(3, 0), (5, 1)]]) r else
  if C = clauses 22 then (![[(3, 2), (5, 1)], [(5, 0), (3, 0), (3, 2)], [(3, 0), (5, 0), (5, 1)]]) r else
  if C = clauses 23 then (![[(1, 1), (1, 2)], [(1, 0), (1, 2)], [(1, 0), (1, 1)]]) r else
  if C = clauses 24 then (![[(1, 2), (2, 1)], [(2, 0), (1, 0), (1, 2)], [(1, 0), (2, 0), (2, 1)]]) r else
  if C = clauses 25 then (![[(1, 2), (2, 1), (3, 1)], [(3, 0), (1, 0), (1, 2)], [(1, 0), (2, 1), (3, 0), (3, 1)]]) r else
  if C = clauses 26 then (![[(1, 2), (2, 1), (5, 1)], [(5, 0), (3, 0), (1, 0), (1, 2)], [(1, 0), (2, 1), (3, 0), (5, 0), (5, 1)]]) r else
  if C = clauses 27 then (![[(4, 1), (4, 2)], [(4, 0), (4, 2)], [(4, 0), (4, 1)]]) r else
  if C = clauses 28 then (![[(1, 1), (4, 2)], [(1, 0), (4, 0), (4, 2)], [(4, 0), (1, 0), (1, 1)]]) r else
  if C = clauses 29 then (![[(2, 1), (4, 2)], [(2, 0), (1, 0), (4, 0), (4, 2)], [(4, 0), (1, 0), (2, 0), (2, 1)]]) r else
  if C = clauses 30 then (![[(2, 1), (3, 1), (4, 2)], [(3, 0), (1, 0), (4, 0), (4, 2)], [(4, 0), (1, 0), (2, 1), (3, 0), (3, 1)]]) r else
  if C = clauses 31 then (![[(2, 1), (4, 2), (5, 1)], [(5, 0), (3, 0), (1, 0), (4, 0), (4, 2)], [(4, 0), (1, 0), (2, 1), (3, 0), (5, 0), (5, 1)]]) r else
  []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem columns_checked :
    checkColumns family (fun j i => values i j) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem orders_checked : checkFamily family orders = true := by
  decide +kernel

theorem finite_persistence {Var : Type*} (tag : Var → Fin 5) (t : Term (Fin 3) Var)
    (ht : t.IsCore)
    (h : 0 ∈ (t.eval (fun j => Value.toWinner (values 0 (tag j)))).val) :
    0 ∈ (t.eval (fun j => Value.toWinner (values 1 (tag j)))).val ∨
    1 ∈ (t.eval (fun j => Value.toWinner (values 2 (tag j)))).val ∨
    0 ∈ (t.eval (fun j => Value.toWinner (values 3 (tag j)))).val ∨
    0 ∈ (t.eval (fun j => Value.toWinner (values 4 (tag j)))).val ∨
    1 ∈ (t.eval (fun j => Value.toWinner (values 5 (tag j)))).val := by
  have hcolumns := checkColumns_sound columns_checked
  have hall := core_preserves orders_checked
    (fun j i => Value.toWinner (values i (tag j))) (fun j => hcolumns (tag j)) t ht
  have hc : clauses 0 ∈ family := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hr := hall (clauses 0) hc
  simp only [Clause.Holds, Clause.Premise, Clause.Head, clauses,
    Matrix.cons_val_zero, Finset.mem_insert, Finset.mem_singleton] at hr
  simpa only [Prod.exists, exists_eq_or_imp, exists_eq_left, Prod.mk.injEq,
    exists_and_left, exists_or, and_assoc, and_left_comm, and_comm] using hr h

noncomputable def namedValues {Role : Type*} (three : Fin 3 ↪ Role)
    (i : Fin 6) (j : Fin 5) : WinnerSet Role :=
  expand (fun r => singleton (three r)) (Value.toWinner (values i j))

theorem persistence {Role Var : Type*} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore)
    (h : three 0 ∈ (t.eval (fun j => namedValues three 0 (tag j))).val) :
    three 0 ∈ (t.eval (fun j => namedValues three 1 (tag j))).val ∨
    three 1 ∈ (t.eval (fun j => namedValues three 2 (tag j))).val ∨
    three 0 ∈ (t.eval (fun j => namedValues three 3 (tag j))).val ∨
    three 0 ∈ (t.eval (fun j => namedValues three 4 (tag j))).val ∨
    three 1 ∈ (t.eval (fun j => namedValues three 5 (tag j))).val := by
  obtain ⟨s, hs, hse⟩ := exists_role_restriction three (Function.Embedding.refl (Fin 3)) t ht
  have he (i : Fin 6) : t.eval (fun j => namedValues three i (tag j)) =
      expand (fun r => singleton (three r))
        (s.eval (fun j => Value.toWinner (values i (tag j)))) :=
    hse (fun j => Value.toWinner (values i (tag j)))
  simp only [he, mem_expand_embedding] at h ⊢
  exact finite_persistence tag s hs h

end KFOL.Core.SixValuation
