module

public import KFOL.Core.ThreeSlotQuantified
public import KFOL.Reductions.PrenexReduction
public import Complexity.Logics.Propositional.CNF.ThreeCNF

/-! # Three-clause splitting after a quantified prefix

The clause chains and their fixed-assignment extension come from complexitylib.
Auxiliary occurrences are assigned consecutive stages after every original
quantifier, using the first occurrence of each auxiliary variable. -/

@[expose] public section
namespace KFOL.Bichain.Quantified.ThreeCNF

open Cslib.Logic.PL

abbrev Tag := ℕ ⊕ (ℕ × ℕ)

def split (F : Formula) : CNF Tag := CNF.to3CNF F.cls

/-- One extra stage is reserved for references outside the original prefix.
Well-formed input clauses never use such a reference. -/
def extra (F : Formula) : ℕ := 1 + (split F).vars.length

def name (F : Formula) : Tag → ℕ
  | .inl j => if 1 ≤ j ∧ j ≤ F.n then j else F.n+1
  | .inr p => F.n+2+(split F).vars.idxOf (.inr p)

def translate (F : Formula) : Formula where
  n := F.n + extra F
  ex j := if j ≤ F.n then F.ex j else true
  cls := CNF.relabel (name F) (split F)

private theorem matrix_eval (F : Formula) (α : ℕ → Bool) :
    Matrix F α ↔ CNF.eval α F.cls = true := by
  simp only [Matrix,CNF.eval_eq_true_iff,Clause.eval_eq_true_iff]

theorem width (F : Formula) : ∀ C ∈ (translate F).cls, C.length ≤ 3 := by
  intro D hd
  obtain ⟨C,hc,rfl⟩ := List.mem_map.mp hd
  simpa [Clause.relabel] using CNF.length_le_three_of_mem_to3CNF hc

private theorem name_bounds (F : Formula) {s : Tag} (mem : s ∈ (split F).vars) :
    1 ≤ name F s ∧ name F s ≤ F.n + extra F := by
  cases s with
  | inl j =>
    simp only [name,extra]
    split_ifs <;> omega
  | inr p =>
    have := List.idxOf_lt_length_of_mem mem
    simp only [name,extra]
    omega

theorem wf_translate (F : Formula) : (translate F).WF := by
  intro D hd l hl
  obtain ⟨C,hc,rfl⟩ := List.mem_map.mp hd
  obtain ⟨⟨s,b⟩, member, rfl⟩ := List.mem_map.mp hl
  exact name_bounds F (CNF.mem_vars.mpr ⟨C,hc,b,member⟩)

private theorem base_agreement (F : Formula) (wf : F.WF) (v : ℕ) (mem : v ∈ CNF.vars F.cls) :
    1 ≤ v ∧ v ≤ F.n := by
  obtain ⟨C,hc,b,hb⟩ := CNF.mem_vars.mp mem
  exact wf C hc (v,b) hb

/-- For each fixed assignment of the prefix, all newly appended stages are
existential and make the width-three matrix true exactly as prescribed. -/
theorem after_prefix (F : Formula) (wf : F.WF) (α : ℕ → Bool) :
    sat (translate F) (extra F) F.n α ↔ Matrix F α := by
  rw [ThreeSlot.sat_exists_tail]
  · constructor
    · rintro ⟨β,agree,hm⟩
      have eval := (matrix_eval _ _).mp hm
      change CNF.eval β (CNF.relabel (name F) (split F)) = true at eval
      rw [CNF.eval_relabel] at eval
      have orig := CNF.eval_comp_inl_of_eval_to3CNF eval
      apply (matrix_eval _ _).mpr
      convert orig using 1
      apply CNF.eval_congr
      intro j mem
      have good := base_agreement F wf j mem
      exact (by simpa [Function.comp_apply,name,good] using (agree j (Or.inl good.2)).symm)
    · intro hm
      let inputs (j : ℕ) := if 1 ≤ j ∧ j ≤ F.n then α j else false
      have inputsTrue : CNF.eval inputs F.cls = true := by
        rw [← (matrix_eval _ α).mp hm]
        apply CNF.eval_congr
        intro j mem
        simp [inputs,base_agreement _ wf _ mem]
      let values := CNF.to3CNFAssignment F.cls inputs
      let names := (split F).vars
      let β (j : ℕ) := if j ≤ F.n ∨ F.n+extra F < j then α j
        else if j = F.n+1 then false else values (names.getD (j-(F.n+2)) (.inl 0))
      refine ⟨β,fun j h => by simp [β,h],(matrix_eval _ _).mpr ?_⟩
      change CNF.eval β (CNF.relabel (name F) (split F)) = true
      rw [CNF.eval_relabel]
      have same : CNF.eval (β ∘ name F) (split F) = CNF.eval values (split F) := by
        apply CNF.eval_congr
        intro s mem
        cases s with
        | inl j =>
          by_cases good : 1 ≤ j ∧ j ≤ F.n
          · simp [β, name, good, values, inputs]
          · have h : ¬ (F.n+1 ≤ F.n ∨ F.n+extra F < F.n+1) := by unfold extra; omega
            change β (if 1 ≤ j ∧ j ≤ F.n then j else F.n+1) = inputs j
            simp only [ite_eq_right good, β, ite_eq_right h, ite_true, inputs]
        | inr p =>
          have bound : names.idxOf (.inr p) < names.length := List.idxOf_lt_length_of_mem mem
          have small : ¬ (F.n+2+names.idxOf (.inr p) ≤ F.n ∨ F.n+extra F < F.n+2+names.idxOf (.inr p)) := by
            change ¬ (F.n+2+names.idxOf (.inr p) ≤ F.n ∨
              F.n+(1+names.length) < F.n+2+names.idxOf (.inr p))
            omega
          have diff : F.n+2+names.idxOf (.inr p) ≠ F.n+1 := by omega
          change β (F.n+2+names.idxOf (.inr p)) = _
          simp only [β, ite_eq_right small, ite_eq_right diff, Nat.add_sub_cancel_left]
          rw [List.getD_eq_getElem _ _ bound, List.getElem_idxOf]
      exact same.trans (CNF.eval_to3CNF_to3CNFAssignment inputsTrue)
  · intro j lo _
    simp [translate,show ¬ j ≤ F.n by omega]

private theorem prefix_iff (F : Formula) (wf : F.WF) (k i : ℕ) (total : i+k = F.n) (α : ℕ → Bool) :
    sat (translate F) (k+extra F) i α ↔ sat F k i α := by
  induction k generalizing i α with
  | zero =>
    have e : i = F.n := by omega
    subst i
    simpa only [Nat.zero_add,sat] using after_prefix F wf α
  | succ k ih =>
    rw [show k+1+extra F = (k+extra F)+1 by omega, sat, sat]
    have h : (translate F).ex (i+1) = F.ex (i+1) := by
      simp [translate, show i+1 ≤ F.n by omega]
    rw [h]
    cases e : F.ex (i+1) with
    | false => exact forall_congr' (fun s => ih (i+1) (by omega) (Function.update α (i+1) s))
    | true => exact exists_congr (fun s => ih (i+1) (by omega) (Function.update α (i+1) s))

theorem sat_translate_iff (F : Formula) (wf : F.WF) (α : ℕ → Bool) :
    sat (translate F) (translate F).n 0 α ↔ sat F F.n 0 α :=
  prefix_iff F wf F.n 0 (by omega) α

/-- Splitting and indexing increase both the number of stages and clauses
by at most a linear function of the input prefix, clauses, and literals. -/
theorem size_bound (F : Formula) :
    (translate F).cls.length ≤ F.cls.length + (CNF.vars F.cls).length ∧
      (translate F).n ≤ F.n + 1 + 3 * (F.cls.length + (CNF.vars F.cls).length) := by
  have count (cs : CNF ℕ) :
      (cs.map (fun c => max 1 (c.length - 2))).sum ≤ cs.length + (cs.map List.length).sum := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have rows : (split F).length ≤ F.cls.length + (CNF.vars F.cls).length := by
    rw [split, CNF.length_to3CNF, CNF.length_vars]
    exact count _
  have literals : (split F).vars.length ≤ 3 * (split F).length :=
    CNF.length_vars_le_mul_length (fun _ h => CNF.length_le_three_of_mem_to3CNF h)
  refine ⟨?_,?_⟩
  · simpa only [translate,CNF.relabel,List.length_map] using rows
  · change F.n + (1 + (split F).vars.length) ≤ _
    omega

/-- Turn the existing complexitylib TQBFCNF presentation into a three-slot
instance. Open inputs retain the false instance of the existing stage conversion. -/
def fromTQBFCNF (x : List (ℕ × ℕ) × CNF ℕ) : Formula :=
  ThreeSlot.translate (translate (Recognition.Lists.formulaOf x))

theorem fromTQBFCNF_correct (x : List (ℕ × ℕ) × CNF ℕ) :
    sat (fromTQBFCNF x) (fromTQBFCNF x).n 0 (fun _ => false) ↔ x ∈ Cslib.Complexity.TQBFCNF :=
  (ThreeSlot.sat_translate_iff _ (wf_translate _) _).trans
    ((sat_translate_iff _ (Recognition.Lists.formulaOf_wf x) _).trans (Recognition.Lists.mem_TQBFCNF_iff x).symm)

theorem fromTQBFCNF_wf (x : List (ℕ × ℕ) × CNF ℕ) : (fromTQBFCNF x).WF :=
  ThreeSlot.wf_translate _ (wf_translate _)

/-- The three-slot colors used by the rectangle associated with a TQBFCNF instance. -/
def inputSlot (x : List (ℕ × ℕ) × CNF ℕ) : ℕ → Fin 3 :=
  ThreeSlot.slot (translate (Recognition.Lists.formulaOf x))

theorem fromTQBFCNF_separated (x : List (ℕ × ℕ) × CNF ℕ) (c : ℕ) :
    ∀ p ∈ (fromTQBFCNF x).cls.getD c [], ∀ q ∈ (fromTQBFCNF x).cls.getD c [],
      inputSlot x p.1 = inputSlot x q.1 → p = q :=
  ThreeSlot.getD_slot_unique _ (wf_translate _) (width _) c

end KFOL.Bichain.Quantified.ThreeCNF
