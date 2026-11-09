module

public import KFOL.Core.ChoiceUnion.NormalForm

/-! # Covering monomial supports suffices in every seven-law model -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

namespace Laws

variable {M : Type u} {plus times : M → M → M} (h : Laws plus times)

include h

/-- Transitivity in the join order, written without assuming a common
lattice order for the two semilattice operations. -/
theorem absorb_trans {x y z : M} (hxy : plus x y = y) (hyz : plus y z = z) : plus x z = z := by
  calc
    plus x z = plus x (plus y z) := congrArg (plus x) hyz.symm
    _ = plus (plus x y) z := (h.add_assoc x y z).symm
    _ = z := by rw [hxy,hyz]

/-- Distributivity makes multiplication monotone in the join order. -/
theorem mul_join_mono {x x' y y' : M} (hx : plus x x' = x') (hy : plus y y' = y') :
    plus (times x y) (times x' y') = times x' y' := by
  apply h.absorb_trans (y := times x' y)
  · rw [← h.add_mul,hx]
  · rw [← h.mul_add,hy]

theorem absorb_mul {x y z : M} (hx : plus x z = z) (hy : plus y z = z) : plus (times x y) z = z := by
  have hh := h.mul_join_mono hx hy
  simpa only [h.mul_idem] using hh

end Laws

noncomputable def supportFamilyUnion {Var : Type v} (C : Finset (Support Var)) (hC : C.Nonempty) : Support Var := by
  classical
  exact ⟨C.biUnion (fun B => B.val),hC.biUnion (fun B _ => B.property)⟩

variable {M : Type u} {plus times : M → M → M} (h : Laws plus times)

theorem evalSupport_familyUnion {Var : Type v} (C : Finset (Support Var)) (hC : C.Nonempty) (v : Var → M) :
    letI := h.meetSemilattice
    evalSupport h (supportFamilyUnion C hC) v = C.inf' hC (fun B => evalSupport h B v) := by
  classical
  let _ := h.meetSemilattice
  exact Finset.inf'_biUnion v hC (fun B => B.property)

/-- For each variable of A, a contained monomial of F contains that variable.
Their meet-product is exactly A, so join-monotonicity proves absorption. -/
theorem absorb_support_of_cover {Var : Type v} (A : Support Var) (F : NormalForm Var)
    (cover : ∀ j ∈ A.val, ∃ B ∈ F.val, B.val ⊆ A.val ∧ j ∈ B.val) (v : Var → M) :
    plus (evalSupport h A v) (evalNormal h F v) = evalNormal h F v := by
  classical
  let C := F.val.filter (fun B => B.val ⊆ A.val)
  have hC : C.Nonempty := by
    obtain ⟨j,hj⟩ := A.property
    obtain ⟨B,hBF,hBA,_⟩ := cover j hj
    exact ⟨B,Finset.mem_filter.mpr ⟨hBF,hBA⟩⟩
  have hUnion : supportFamilyUnion C hC = A := by
    apply Subtype.ext
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨B,hBC,hjB⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp hBC).2 hjB
    · intro j hj
      obtain ⟨B,hBF,hBA,hjB⟩ := cover j hj
      exact Finset.mem_biUnion.mpr ⟨B,Finset.mem_filter.mpr ⟨hBF,hBA⟩,hjB⟩
  have hpoint (B : Support Var) (hBC : B ∈ C) :
      plus (evalSupport h B v) (evalNormal h F v) = evalNormal h F v := by
    let _ := h.joinSemilattice
    have hBF := (Finset.mem_filter.mp hBC).1
    exact sup_eq_right.mpr (Finset.le_sup' (fun A => evalSupport h A v) hBF)
  let _ := h.meetSemilattice
  have hi : plus (C.inf' hC (fun B => evalSupport h B v)) (evalNormal h F v) = evalNormal h F v :=
    Finset.inf'_induction hC (fun B => evalSupport h B v)
      (p := fun x => plus x (evalNormal h F v) = evalNormal h F v)
      (fun x hx y hy => h.absorb_mul hx hy) hpoint
  rw [← evalSupport_familyUnion h C hC v,hUnion] at hi
  exact hi

/-- The syntactic support-cover condition transfers an entire polynomial
comparison to every model of the seven laws. -/
theorem absorb_normal_of_cover {Var : Type v} (F G : NormalForm Var)
    (cover : ∀ A ∈ F.val, ∀ j ∈ A.val, ∃ B ∈ G.val, B.val ⊆ A.val ∧ j ∈ B.val) (v : Var → M) :
    plus (evalNormal h F v) (evalNormal h G v) = evalNormal h G v := by
  let _ := h.joinSemilattice
  exact Finset.sup'_induction F.property (fun A => evalSupport h A v)
    (p := fun x => plus x (evalNormal h G v) = evalNormal h G v)
    (fun x hx y hy => by change plus (plus x y) (evalNormal h G v) = _; rw [h.add_assoc,hy,hx])
    (fun A hA => absorb_support_of_cover h A G (cover A hA) v)

end KFOL.Dissemilattice
