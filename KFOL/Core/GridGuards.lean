module

public import KFOL.Core.GridProfiles
public import KFOL.Core.PairLabel
public import KFOL.Core.PairModel
public import KFOL.Core.MarkerGap

/-! # The graph-generated label cover's actual closure invariant -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf pairStructure

/-- The graph's typed upper-marker invariant, stated on arbitrary members
of any subalgebra of the actual generated grid. -/
def Guard {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i : Fin r) (j : Fin s) (z : C × Native.atomicRestriction (pairRoles three)) : Prop :=
  (z.2.val = Native.atom (three 0) → A hr three i z.1.val = true) ∧
  (z.2.val = Native.atom (three 1) → B hs three j z.1.val = true) ∧
  (A hr three i z.1.val = true → z.2.val ≠ Native.atom (three 0) →
    (z.1.val.val (.inr (.inr (i,j)))).val = Native.upper) ∧
  (B hs three j z.1.val = true → z.2.val ≠ Native.atom (three 1) →
    (z.1.val.val (.inr (.inr (i,j)))).val = Native.upper)

/-- Every generator receives its actual prescribed label. Its two missing
label cases are exactly the crossing-block marker condition. -/
theorem guard_graph {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i : Fin r) (j : Fin s) (x : C) :
    Guard hr hs three C i j (x,pairLabel three (A hr three i x.val) (B hs three j x.val)) := by
  refine ⟨fun h => (pairLabel_atom_zero three _ _).mp h |>.1,
    fun h => (pairLabel_atom_one three _ _).mp h |>.1, ?_, ?_⟩
  · intro ha hn
    have hb : B hs three j x.val = true := by
      cases he : B hs three j x.val
      · exact False.elim (hn ((pairLabel_atom_zero three _ _).mpr ⟨ha,he⟩))
      · rfl
    exact annotation_upper_of_AB hr hs three x.val i j ha hb
  · intro hb hn
    have ha : A hr three i x.val = true := by
      cases he : A hr three i x.val
      · exact False.elim (hn ((pairLabel_atom_one three _ _).mpr ⟨hb,he⟩))
      · rfl
    exact annotation_upper_of_AB hr hs three x.val i j ha hb

theorem annotation_no_atom_of_matching_A {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i k : Fin r) (hik : i ≠ k) (j : Fin s)
    (matching : ∀ x : C, A hr three i x.val = A hr three k x.val)
    (x : C) (hx : A hr three i x.val = true) (owner : Role) :
    (x.val.val (.inr (.inr (i,j)))).val ≠ Native.atom owner := by
  by_cases ho : owner = three 2
  · subst owner
    apply annotation_no_gamma_of_A hr three x.val k i (Ne.symm hik) j
    rw [← matching x]
    exact hx
  · exact annotation_no_other_atom three x.val i j owner ho

theorem annotation_no_atom_of_matching_B {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (j l : Fin s) (hjl : j ≠ l) (i : Fin r)
    (matching : ∀ x : C, B hs three j x.val = B hs three l x.val)
    (x : C) (hx : B hs three j x.val = true) (owner : Role) :
    (x.val.val (.inr (.inr (i,j)))).val ≠ Native.atom owner := by
  by_cases ho : owner = three 2
  · subst owner
    apply annotation_no_gamma_of_B hs three x.val l j (Ne.symm hjl) i
    rw [← matching x]
    exact hx
  · exact annotation_no_other_atom three x.val i j owner ho

/-- Closure is proved from the operations, not stipulated as a certificate.
The matching foreign blocks protect all positive siblings. -/
theorem guard_operation {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i k : Fin r) (hik : i ≠ k) (j l : Fin s) (hjl : j ≠ l)
    (matchA : ∀ x : C, A hr three i x.val = A hr three k x.val)
    (matchB : ∀ x : C, B hs three j x.val = B hs three l x.val)
    (owner : Role) (x y : C × Native.atomicRestriction (pairRoles three))
    (hx : Guard hr hs three C i j x) (hy : Guard hr hs three C i j y) :
    Guard hr hs three C i j (Core.operation owner x y) := by
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  refine ⟨?_,?_,?_,?_⟩
  · intro hlabel
    change Native.choice owner x.2.val y.2.val = Native.atom (three 0) at hlabel
    change A hr three i (Core.operation owner x.1.val y.1.val) = true
    rw [A_operation]
    exact Native.bit_positive_of_atom_step (three 0) owner x.2.val y.2.val _ _ hx.1 hy.1 hlabel
  · intro hlabel
    change Native.choice owner x.2.val y.2.val = Native.atom (three 1) at hlabel
    change B hs three j (Core.operation owner x.1.val y.1.val) = true
    rw [B_operation]
    exact Native.bit_positive_of_atom_step (three 1) owner x.2.val y.2.val _ _ hx.2.1 hy.2.1 hlabel
  · intro hbit hlabel
    change A hr three i (Core.operation owner x.1.val y.1.val) = true at hbit
    rw [A_operation] at hbit
    change Native.choice owner x.2.val y.2.val ≠ Native.atom (three 0) at hlabel
    change Native.choice owner (x.1.val.val (.inr (.inr (i,j)))).val
      (y.1.val.val (.inr (.inr (i,j)))).val = Native.upper
    exact Native.upper_of_gap_step (three 0) owner _ _ _ _ _ _ hx.2.2.1 hy.2.2.1
      (annotation_no_other_atom three x.1.val i j _ h02)
      (annotation_no_other_atom three y.1.val i j _ h02)
      (annotation_no_atom_of_matching_A hr three C i k hik j matchA x.1)
      (annotation_no_atom_of_matching_A hr three C i k hik j matchA y.1) hbit hlabel
  · intro hbit hlabel
    change B hs three j (Core.operation owner x.1.val y.1.val) = true at hbit
    rw [B_operation] at hbit
    change Native.choice owner x.2.val y.2.val ≠ Native.atom (three 1) at hlabel
    change Native.choice owner (x.1.val.val (.inr (.inr (i,j)))).val
      (y.1.val.val (.inr (.inr (i,j)))).val = Native.upper
    exact Native.upper_of_gap_step (three 1) owner _ _ _ _ _ _ hx.2.2.2 hy.2.2.2
      (annotation_no_other_atom three x.1.val i j _ h12)
      (annotation_no_other_atom three y.1.val i j _ h12)
      (annotation_no_atom_of_matching_B hs three C j l hjl i matchB x.1)
      (annotation_no_atom_of_matching_B hs three C j l hjl i matchB y.1) hbit hlabel

end KFOL.Core.Grid
