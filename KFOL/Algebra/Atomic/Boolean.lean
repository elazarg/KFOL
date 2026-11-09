module

public import KFOL.Algebra.Atomic.Unary
public import Mathlib.Data.Fintype.Pi

/-! # Two-output functions from finite Boolean normal forms -/

@[expose] public section

namespace KFOL

open Classical

universe u v w

namespace WinnerSet

variable {Role : Type u}

/-- Owned choice is Boolean conjunction on two atomic labels, with truth `a`. -/
theorem choice_boolean_and (a b : Role) (p q : Prop) [Decidable p] [Decidable q] :
    choice b (singleton (if p then a else b)) (singleton (if q then a else b)) =
      singleton (if p ∧ q then a else b) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq,choice,eq_comm]

/-- Owned choice is Boolean disjunction on two atomic labels, with truth `a`. -/
theorem choice_boolean_or (a b : Role) (p q : Prop) [Decidable p] [Decidable q] :
    choice a (singleton (if p then a else b)) (singleton (if q then a else b)) =
      singleton (if p ∨ q then a else b) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq,choice,eq_comm]

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

/-- Finite conjunction of predicates already represented on two atoms. -/
theorem atomic_realization_conjunction {Index : Type w} (S : Finset Index)
    (a b : Role) (P : Index → (Var → Role) → Prop)
    (hP : ∀ i ∈ S, ∃ t : Term Role Var, t.AtomicRealizes
      (fun v => if P i v then a else b)) :
    ∃ t : Term Role Var, t.AtomicRealizes
      (fun v => if ∀ i ∈ S, P i v then a else b) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨.winner a,fun v => by simp [eval]⟩
  | @insert i S hi ih =>
    obtain ⟨s,hs⟩ := hP i (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
    refine ⟨.choice b s t,fun v => ?_⟩
    change WinnerSet.choice b (s.eval _) (t.eval _) = _
    rw [hs v,ht v,WinnerSet.choice_boolean_and]
    simp only [Finset.mem_insert,forall_eq_or_imp]

/-- Finite disjunction of predicates already represented on two atoms. -/
theorem atomic_realization_disjunction {Index : Type w} (S : Finset Index)
    (a b : Role) (P : Index → (Var → Role) → Prop)
    (hP : ∀ i ∈ S, ∃ t : Term Role Var, t.AtomicRealizes
      (fun v => if P i v then a else b)) :
    ∃ t : Term Role Var, t.AtomicRealizes
      (fun v => if ∃ i ∈ S, P i v then a else b) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨.winner b,fun v => by simp [eval]⟩
  | @insert i S hi ih =>
    obtain ⟨s,hs⟩ := hP i (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
    refine ⟨.choice a s t,fun v => ?_⟩
    change WinnerSet.choice a (s.eval _) (t.eval _) = _
    rw [hs v,ht v,WinnerSet.choice_boolean_or]
    simp only [Finset.mem_insert,exists_eq_or_imp]

/-- An exact valuation test is a conjunction of unary label tests. -/
theorem atomic_realization_point [Finite Role] [Finite Var]
    (a b : Role) (w : Var → Role) :
    ∃ t : Term Role Var, t.AtomicRealizes (fun v => if v = w then a else b) := by
  classical
  let := Fintype.ofFinite Var
  obtain ⟨t,ht⟩ := atomic_realization_conjunction (Finset.univ : Finset Var)
    a b (fun i v => v i = w i) (fun i _ => atomic_realization_unary i
      (fun x => if x = w i then a else b))
  refine ⟨t,fun v => ?_⟩
  have hc : (∀ i ∈ (Finset.univ : Finset Var), v i = w i) ↔ v = w :=
    ⟨fun h => funext (fun i => h i (Finset.mem_univ _)),fun h i _ => congrFun h i⟩
  by_cases hv : v = w
  · subst v
    simpa using ht w
  · have hn : ¬(∀ i ∈ (Finset.univ : Finset Var), v i = w i) := fun h => hv (hc.mp h)
    simpa only [hn,hv,ite_false] using ht v

/-- Every function into one fixed pair has an atomic realization by finite DNF. -/
theorem atomic_realization_atMostTwo [Finite Role] [Finite Var]
    (f : (Var → Role) → Role) (hf : Atomic.AtMostTwo f) :
    ∃ t : Term Role Var, t.AtomicRealizes f := by
  classical
  let := Fintype.ofFinite Var
  let := Fintype.ofFinite Role
  obtain ⟨a,b,hab⟩ := hf
  let S := Finset.univ.filter (fun v : Var → Role => f v = a)
  obtain ⟨t,ht⟩ := atomic_realization_disjunction S a b (fun w v => v = w)
    (fun w _ => atomic_realization_point a b w)
  refine ⟨t,fun v => ?_⟩
  have htest : (∃ w ∈ S, v = w) ↔ f v = a := by simp [S]
  rw [ht v]
  dsimp only
  simp only [htest]
  rcases hab v with ha | hb
  · simp [ha]
  · by_cases ha : f v = a <;> simp [ha,hb,eq_comm]

end Term

end KFOL
