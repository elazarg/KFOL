module

public import KFOL.Core.AtomicObserver
public import KFOL.Core.IntervalCompletion
public import KFOL.Core.RelationalInterpolation
public import KFOL.Definitions.CrownFrame
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # The full matching of an interval crown has no core realization

Reverse matching intervals propagate around the finite cycle and reverse a
positive opposite interval. The resulting obstruction concerns the complete
winner-valued operation and any ambient role set with three named owners.
-/

@[expose] public section
namespace KFOL.Core.IntervalCrown.Frame
open WinnerSet
universe u v
variable {Var : Type u} {Role : Type v} [Fintype Var] [DecidableEq Var] {m : ℕ}

private theorem rotate_ne_self (hm : 3 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  have : NeZero m := ⟨by omega⟩
  intro h
  have hh : i + (1 : Fin m) = i + 0 := by simpa only [finRotate_apply,add_zero] using h
  have he : (1 : Fin m) = 0 := add_left_cancel hh
  have hv := congrArg Fin.val he
  simp only [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (by omega : 1 < m)] at hv
  omega

private theorem rotate_twice_ne_self (hm : 3 ≤ m) (i : Fin m) :
    finRotate m (finRotate m i) ≠ i := by
  have : NeZero m := ⟨by omega⟩
  intro h
  have hh : i + ((1 : Fin m) + 1) = i + 0 := by
    simpa only [finRotate_apply,add_assoc,add_zero] using h
  have he : (1 : Fin m) + 1 = 0 := add_left_cancel hh
  have hv := congrArg Fin.val he
  simp only [Fin.val_add,Fin.val_one',Fin.val_zero,
    Nat.mod_eq_of_lt (by omega : 1 < m),Nat.mod_eq_of_lt (by omega : 2 < m)] at hv
  omega

/-- Three or more crown edges have distinct lower endpoints. -/
theorem lower_injective (G : Frame Var m) (hm : 3 ≤ m) : Function.Injective G.lower := by
  intro i j hij
  by_contra hne
  have hji : j = finRotate m i := by
    rcases (G.incidence i j).mp (hij ▸ (G.cover i).le) with h | h
    · exact (hne h.symm).elim
    · exact h
  have hij' : i = finRotate m j := by
    rcases (G.incidence j i).mp (hij.symm ▸ (G.cover j).le) with h | h
    · exact (hne h).elim
    · exact h
  exact rotate_twice_ne_self hm i (by simpa only [hji] using hij'.symm)

/-- Three or more crown edges also have distinct upper endpoints. -/
theorem upper_injective (G : Frame Var m) (hm : 3 ≤ m) : Function.Injective G.upper := by
  intro i j hij
  by_contra hne
  have hnextj : i = finRotate m j := by
    rcases (G.incidence j i).mp (hij ▸ (G.cover i).le) with h | h
    · exact (hne h).elim
    · exact h
  have hinc : G.lower (finRotate m i) ⊆ G.upper j := by
    rw [← hij]
    exact (G.incidence i _).mpr (Or.inr rfl)
  rcases (G.incidence j _).mp hinc with h | h
  · exact rotate_twice_ne_self hm j (by rw [← hnextj]; exact h)
  · exact hne ((finRotate m).injective h)

/-- The other lower endpoint lies strictly below the same upper endpoint. -/
theorem opposite_strict (G : Frame Var m) (hm : 3 ≤ m) (i : Fin m) :
    G.lower (finRotate m i) ⊂ G.upper i := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨(G.incidence i _).mpr (Or.inr rfl),?_⟩
  intro he
  have hh : G.lower i ⊆ G.upper (finRotate m i) :=
    ((G.cover i).le.trans he.ge).trans (G.cover (finRotate m i)).le
  rcases (G.incidence (finRotate m i) i).mp hh with h | h
  · exact rotate_ne_self hm i h.symm
  · exact rotate_twice_ne_self hm i h.symm

/-- An opposite interval is never one of the selected matching intervals. -/
theorem opposite_not_mem_edges (G : Frame Var m) (hm : 3 ≤ m) (i : Fin m) :
    (G.lower (finRotate m i),G.upper i) ∉ G.edges Set.univ := by
  rintro ⟨j,_,he⟩
  obtain ⟨hl,hu⟩ := Prod.mk.inj he
  have hji : i = j := G.upper_injective hm hu
  subst j
  exact rotate_ne_self hm i (G.lower_injective hm hl)

private theorem atomic_lower (three : Fin 3 ↪ Role) (L U : Finset Var) :
    Intervals.lowerInputs (three 2) (AtomicObserver.values three L U) = L := by
  classical
  ext j
  by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
    simp [Intervals.lowerInputs,AtomicObserver.values,hL,hU,WinnerSet.singleton_inj,
      three.injective.eq_iff]

private theorem atomic_upper (three : Fin 3 ↪ Role) (L U : Finset Var) (hLU : L ⊆ U) :
    Intervals.upperInputs (three 1) (AtomicObserver.values three L U) = U := by
  classical
  ext j
  have hj : j ∈ L → j ∈ U := fun h => hLU h
  by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
    simp_all [Intervals.upperInputs,AtomicObserver.values,WinnerSet.singleton_inj,
      three.injective.eq_iff]

omit [Fintype Var] in
private theorem atomic_union [Nonempty Var] (three : Fin 3 ↪ Role)
    (L U : Finset Var) (hLU : L ⊆ U) :
    three 0 ∈ (Intervals.inputUnion (AtomicObserver.values three L U)).val ↔ L ⊂ U := by
  classical
  have hat (j : Var) : three 0 ∈ (AtomicObserver.values three L U j).val ↔
      j ∉ L ∧ j ∈ U := by
    by_cases hL : j ∈ L <;> by_cases hU : j ∈ U <;>
      simp [AtomicObserver.values,hL,hU,WinnerSet.val_singleton,three.injective.eq_iff]
  change (three 0 ∈ ⋃ j, (AtomicObserver.values three L U j).val) ↔ L ⊂ U
  simp only [Set.mem_iUnion,hat]
  constructor
  · rintro ⟨j,hjL,hjU⟩
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hLU,fun he => hjL (he ▸ hjU)⟩
  · intro h
    obtain ⟨j,hjU,hjL⟩ := Finset.exists_of_ssubset h
    exact ⟨j,hjL,hjU⟩

/-- The atomic observer sees every strict interval except the selected ones. -/
theorem atomic_operation_iff [Nonempty Var] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (L U : Finset Var) (hLU : L ⊆ U) :
    three 0 ∈ (Intervals.operation (three 1) (three 2) selected
      (AtomicObserver.values three L U)).val ↔ L ⊂ U ∧ (L,U) ∉ selected := by
  classical
  unfold Intervals.operation
  rw [atomic_lower,atomic_upper three L U hLU]
  split_ifs with hF
  · simp [hF,WinnerSet.val_union,WinnerSet.val_singleton,three.injective.eq_iff]
  · simp only [atomic_union three L U hLU,hF,not_false_eq_true,and_true]

private theorem finite_reverse_shift {Index : Type*} [Finite Index]
    (next : Equiv.Perm Index) (P : Index → Prop)
    (h : ∀ j, P (next j) → P j) : ∀ j, P j → P (next j) := by
  let f : {j // P j} → {j // P j} := fun j =>
    ⟨next.symm j.val,h _ (by simpa only [next.apply_symm_apply] using j.property)⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact next.symm.injective (congrArg Subtype.val he)
  intro j hj
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective hf ⟨j,hj⟩
  have he : next.symm x.val = j := congrArg Subtype.val hx
  have hxj : x.val = next j := by simpa only [next.apply_symm_apply] using congrArg next he
  exact hxj ▸ x.property

private theorem trace_contradiction (G : Frame Var m)
    (h : Finset Var → Finset Var → Prop) (ha : AtomicObserver.Admissible h)
    (hz : ∀ i, ¬h (G.lower i) (G.upper i)) (i : Fin m)
    (hp : h (G.lower (finRotate m i)) (G.upper i)) : False := by
  have back (j : Fin m) : AtomicObserver.Reach h (G.lower (finRotate m j)) (G.lower j) := by
    have hj : AtomicObserver.Edge h (G.lower (finRotate m j)) (G.upper j) :=
      Or.inl ((G.incidence j _).mpr (Or.inr rfl))
    have hz' : AtomicObserver.Edge h (G.upper j) (G.lower j) :=
      Or.inr ⟨(G.cover j).le,hz j⟩
    exact (Relation.ReflTransGen.single hj).tail hz'
  have forward : AtomicObserver.Reach h (G.lower i) (G.lower (finRotate m i)) := by
    apply finite_reverse_shift (finRotate m)
      (fun j => AtomicObserver.Reach h (G.lower i) (G.lower j))
      (fun j hj => hj.trans (back j)) i
    exact Relation.ReflTransGen.refl
  apply ha.2 _ _ ((G.incidence i _).mpr (Or.inr rfl)) hp
  have hz' : AtomicObserver.Edge h (G.upper i) (G.lower i) :=
    Or.inr ⟨(G.cover i).le,hz i⟩
  exact (Relation.ReflTransGen.single hz').trans forward

/-- The full matching cycle obstructs a core realizer in every ambient role set. -/
theorem full_operation_not_core {Role : Type v} [Nonempty Var]
    (three : Fin 3 ↪ Role) (G : Frame Var m) (hm : 3 ≤ m) :
    ¬∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = Intervals.operation (three 1) (three 2) (G.edges Set.univ) values := by
  classical
  rintro ⟨t,ht,he⟩
  let h (L U : Finset Var) : Prop :=
    three 0 ∈ (Intervals.operation (three 1) (three 2) (G.edges Set.univ)
      (AtomicObserver.values three L U)).val
  have ha : AtomicObserver.Admissible h :=
    (AtomicObserver.admissible_iff_embedding three h).mpr ⟨t,ht,
      fun L U _ => by dsimp [h]; rw [he]⟩
  have hz (i : Fin m) : ¬h (G.lower i) (G.upper i) := by
    dsimp only [h]
    rw [atomic_operation_iff three _ _ _ (G.cover i).le]
    intro hh
    exact hh.2 ⟨i,Set.mem_univ _,rfl⟩
  let i : Fin m := ⟨0,by omega⟩
  have hp : h (G.lower (finRotate m i)) (G.upper i) := by
    exact (atomic_operation_iff three _ _ _ (G.opposite_strict hm i).le).mpr
      ⟨G.opposite_strict hm i,G.opposite_not_mem_edges hm i⟩
  exact trace_contradiction G h ha hz i hp

/-- All matching atomic rows and one opposite row already exclude a common
interpolant, so the matching count plus one is a sharp locality obstruction. -/
theorem full_operation_not_locallyInterpolable {Role : Type v} [Nonempty Var]
    (three : Fin 3 ↪ Role) (G : Frame Var m) (hm : 3 ≤ m) :
    ¬LocallyInterpolable (m+1)
      (Intervals.operation (three 1) (three 2) (G.edges Set.univ)) := by
  classical
  let i : Fin m := ⟨0,by omega⟩
  let rows : Fin (m+1) → Var → WinnerSet Role :=
    Fin.lastCases (AtomicObserver.values three (G.lower (finRotate m i)) (G.upper i))
      (fun j => AtomicObserver.values three (G.lower j) (G.upper j))
  intro hlocal
  obtain ⟨t,ht,he⟩ := hlocal rows
  let h (L U : Finset Var) : Prop := three 0 ∈ (t.eval (AtomicObserver.values three L U)).val
  have ha : AtomicObserver.Admissible h :=
    (AtomicObserver.admissible_iff_embedding three h).mpr ⟨t,ht,fun _ _ _ => Iff.rfl⟩
  have hz (j : Fin m) : ¬h (G.lower j) (G.upper j) := by
    have hj : t.eval (AtomicObserver.values three (G.lower j) (G.upper j)) =
        Intervals.operation (three 1) (three 2) (G.edges Set.univ)
          (AtomicObserver.values three (G.lower j) (G.upper j)) := by
      simpa only [rows,Fin.lastCases_castSucc] using he j.castSucc
    dsimp only [h]
    rw [hj,atomic_operation_iff three _ _ _ (G.cover j).le]
    intro hh
    exact hh.2 ⟨j,Set.mem_univ _,rfl⟩
  have hp : h (G.lower (finRotate m i)) (G.upper i) := by
    have hi : t.eval (AtomicObserver.values three (G.lower (finRotate m i)) (G.upper i)) =
        Intervals.operation (three 1) (three 2) (G.edges Set.univ)
          (AtomicObserver.values three (G.lower (finRotate m i)) (G.upper i)) := by
      simpa only [rows,Fin.lastCases_last] using he (Fin.last m)
    dsimp only [h]
    rw [hi]
    exact (atomic_operation_iff three _ _ _ (G.opposite_strict hm i).le).mpr
      ⟨G.opposite_strict hm i,G.opposite_not_mem_edges hm i⟩
  exact trace_contradiction G h ha hz i hp

/-- Constant input tuples avoid every matching interval, so the operation is idempotent. -/
theorem full_operation_idempotent {Role : Type v} [Nonempty Var]
    (three : Fin 3 ↪ Role) (G : Frame Var m) (A : WinnerSet Role) :
    Intervals.operation (three 1) (three 2) (G.edges Set.univ) (fun _ => A) = A := by
  classical
  have hn : (Intervals.lowerInputs (three 2) (fun _ : Var => A),
      Intervals.upperInputs (three 1) (fun _ : Var => A)) ∉ G.edges Set.univ := by
    rintro ⟨i,_,he⟩
    obtain ⟨hl,hu⟩ := Prod.mk.inj he
    obtain ⟨j,hj⟩ := G.lower_nonempty i
    have hj' : A = WinnerSet.singleton (three 2) := by
      have hm : j ∈ Intervals.lowerInputs (three 2) (fun _ : Var => A) := hl ▸ hj
      simpa only [Intervals.lowerInputs,Finset.mem_filter,Finset.mem_univ,true_and] using hm
    have hall : Intervals.upperInputs (three 1) (fun _ : Var => A) = Finset.univ := by
      simp [Intervals.upperInputs,hj',WinnerSet.singleton_inj,three.injective.eq_iff]
    exact G.upper_ne_univ i (hu.symm.trans hall)
  rw [Intervals.operation,ite_eq_right hn]
  apply Subtype.ext
  change (⋃ _ : Var, A.val) = A.val
  exact Set.iUnion_const _

end KFOL.Core.IntervalCrown.Frame
