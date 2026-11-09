module

public import KFOL.Core.GridGuards
public import KFOL.Core.GridIdealLabel
public import KFOL.Core.TypedCover

/-! # The actual local typed cover from two matching row and column blocks -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf pairStructure

/-- All graph pairs are available as generators; the prescribed label itself
is not incorrectly assumed to preserve arbitrary operations. -/
def labelGraph {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i : Fin r) (j : Fin s) : Set (C × Native.atomicRestriction (pairRoles three)) :=
  Set.range (fun x : C => (x,pairLabel three (A hr three i x.val) (B hs three j x.val)))

def localCover {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i : Fin r) (j : Fin s) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (C × Native.atomicRestriction (pairRoles three)) :=
  Language.Substructure.closure _ (labelGraph hr hs three C i j)

theorem localCover_guard {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i k : Fin r) (hik : i ≠ k) (j l : Fin s) (hjl : j ≠ l)
    (matchA : ∀ x : C, A hr three i x.val = A hr three k x.val)
    (matchB : ∀ x : C, B hs three j x.val = B hs three l x.val)
    (z : localCover hr hs three C i j) : Guard hr hs three C i j z.val := by
  refine Language.Substructure.closure_induction (p := Guard hr hs three C i j) z.property ?_ ?_
  · intro z hz
    obtain ⟨x,rfl⟩ := hz
    exact guard_graph hr hs three C i j x
  · intro n f args ih
    cases f with
    | choice owner =>
      rw [funMap_choice]
      exact guard_operation hr hs three C i k hik j l hjl matchA matchB owner _ _ (ih 0) (ih 1)

/-- The graph cover agrees with the ideal homomorphism whenever its first
projection lies below e. This proves the precise semantic compatibility. -/
theorem localCover_compatible {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (i k : Fin r) (hik : i ≠ k) (j l : Fin s) (hjl : j ≠ l)
    (matchA : ∀ x : C, A hr three i x.val = A hr three k x.val)
    (matchB : ∀ x : C, B hs three j x.val = B hs three l x.val)
    (z : localCover hr hs three C i j)
    (hz : Core.join three z.val.1.val (lower three) = lower three) :
    z.val.2 = pairLabel three (A hr three i z.val.1.val) (B hs three j z.val.1.val) := by
  have hg := localCover_guard hr hs three C i k hik j l hjl matchA matchB z
  rcases (lower_ideal_exact hr hs three z.val.1.val).mp hz with hT | hS | he
  · have ha : z.val.2.val = Native.atom (three 0) := by
      by_contra hn
      have hp := hg.2.2.1 (by rw [hT]; exact A_T hr hs three i) hn
      rw [hT, T_apply hr hs] at hp
      cases hp
    apply Subtype.ext
    change z.val.2.val = pairLabelValue three _ _
    rw [hT, A_T hr hs, B_T hr hs]
    simpa only [pairLabelValue, Bool.not_false, Bool.true_and, ite_true] using ha
  · have hb : z.val.2.val = Native.atom (three 1) := by
      by_contra hn
      have hp := hg.2.2.2 (by rw [hS]; exact B_S hr hs three j) hn
      rw [hS, S_apply hr hs] at hp
      cases hp
    apply Subtype.ext
    change z.val.2.val = pairLabelValue three _ _
    rw [hS, A_S hr hs, B_S hr hs]
    simpa [pairLabelValue] using hb
  · have hn0 : z.val.2.val ≠ Native.atom (three 0) := by
      intro hh
      have ha := hg.1 hh
      rw [he,A_lower] at ha
      cases ha
    have hn1 : z.val.2.val ≠ Native.atom (three 1) := by
      intro hh
      have hb := hg.2.1 hh
      rw [he,B_lower] at hb
      cases hb
    apply Subtype.ext
    change z.val.2.val = pairLabelValue three _ _
    rw [he,A_lower,B_lower]
    change z.val.2.val = Native.lower
    cases hv : z.val.2.val with
    | lower => rfl
    | upper => exact False.elim (z.val.2.property.2 hv)
    | atom owner =>
      have hm := z.val.2.property.1 owner hv
      rcases hm with ho | ho
      · exact False.elim (hn0 (hv.trans (congrArg Native.atom ho)))
      · exact False.elim (hn1 (hv.trans (congrArg Native.atom ho)))

/-- The local upper clone belongs to the core variety whenever two distinct
row blocks and two distinct column blocks agree on the whole subalgebra.
Both covers here are actual generated subalgebras with onto projections. -/
theorem upper_clone_of_matching_blocks {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    (he : lower three ∈ C)
    (i k : Fin r) (hik : i ≠ k) (j l : Fin s) (hjl : j ≠ l)
    (matchA : ∀ x : C, A hr three i x.val = A hr three k x.val)
    (matchB : ∀ x : C, B hs three j x.val = B hs three l x.val) :
    letI := upperStructure (Role := Role) (⟨lower three,he⟩ : C)
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Option C) := by
  let _ : Nonempty C := ⟨⟨lower three,he⟩⟩
  let hC := (span_inVariety three).substructure C
  let e : C := ⟨lower three,he⟩
  let D := Native.atomicRestriction (pairRoles three)
  let P := localCover hr hs three C i j
  let eta := (idealLabel hr hs three i j).comp (idealInclusion three C he)
  let q : P →[Equational.language (Equational.CoreSymbol Role)] C :=
    (fstHom (M := C) (N := D)).comp P.subtype.toHom
  let label : P →[Equational.language (Equational.CoreSymbol Role)] D :=
    (sndHom (M := C) (N := D)).comp P.subtype.toHom
  have onto : Function.Surjective q := by
    intro x
    refine ⟨⟨(x,pairLabel three (A hr three i x.val) (B hs three j x.val)),
      Language.Substructure.subset_closure ⟨x,rfl⟩⟩,rfl⟩
  have hpne : Nonempty P := ⟨(onto e).choose⟩
  let _ := hpne
  have hP : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) P :=
    (pair_inVariety hC (Native.atomicRestriction_inVariety three (pairRoles three))).substructure P
  refine typed_upper_clone_cover three hC e ?_ (pairRoles three) (pairRoles_proper three)
    eta ?_ hP q onto label ?_
  · intro owner c hc
    apply Subtype.ext
    apply lower_reflecting three owner c.val
    exact congrArg (fun x : C => x.val) hc
  · intro c owner
    have ht := idealLabel_typed hr hs three i j (idealInclusion three C he c) owner
    refine ht.trans ?_
    constructor
    · intro hn hh
      exact hn (congrArg (fun x : C => x.val) hh)
    · intro hn hh
      exact hn (Subtype.ext hh)
  · intro z hz
    change z.val.2 = pairLabel three (A hr three i z.val.1.val) (B hs three j z.val.1.val)
    apply localCover_compatible hr hs three C i k hik j l hjl matchA matchB z
    exact congrArg (fun x : C => x.val) hz

end KFOL.Core.Grid
