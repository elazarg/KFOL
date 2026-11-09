module

public import KFOL.Core.ChoiceUnion.Laws
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Lattice.Union

/-! # Nonempty sums of nonempty meet monomials -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

abbrev Support (Var : Type v) := {S : Finset Var // S.Nonempty}
abbrev NormalForm (Var : Type v) := {F : Finset (Support Var) // F.Nonempty}

noncomputable def supportUnion {Var : Type v} (A B : Support Var) : Support Var := by
  classical
  exact ⟨A.val ∪ B.val,A.property.mono Finset.subset_union_left⟩

noncomputable def merge {Var : Type v} (F G : NormalForm Var) : NormalForm Var := by
  classical
  exact ⟨F.val ∪ G.val,F.property.mono Finset.subset_union_left⟩

noncomputable def product {Var : Type v} (F G : NormalForm Var) : NormalForm Var := by
  classical
  refine ⟨F.val.biUnion (fun A => G.val.image (supportUnion A)),?_⟩
  obtain ⟨A,hA⟩ := F.property
  obtain ⟨B,hB⟩ := G.property
  exact ⟨supportUnion A B,Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_image.mpr ⟨B,hB,rfl⟩⟩⟩

/-- Distribution introduces products of supports, never an empty monomial
or empty sum; repeated variables are removed by the two idempotence laws. -/
noncomputable def normalForm {Var : Type v} : Term Var → NormalForm Var := by
  classical
  exact fun t => match t with
    | .var x => ⟨{⟨{x},Finset.singleton_nonempty x⟩},Finset.singleton_nonempty _⟩
    | .func Symbol.join args => merge (normalForm (args 0)) (normalForm (args 1))
    | .func Symbol.mul args => product (normalForm (args 0)) (normalForm (args 1))

variable {M : Type u} {plus times : M → M → M} (h : Laws plus times)

/-- A meet fold in the meet operation's own semilattice order. -/
noncomputable def evalSupport {Var : Type v} (A : Support Var) (v : Var → M) : M :=
  letI := h.meetSemilattice
  A.val.inf' A.property v

/-- A join fold in the separate join operation's semilattice order. -/
noncomputable def evalNormal {Var : Type v} (F : NormalForm Var) (v : Var → M) : M :=
  letI := h.joinSemilattice
  F.val.sup' F.property (fun A => evalSupport h A v)

theorem evalSupport_union {Var : Type v} (A B : Support Var) (v : Var → M) :
    evalSupport h (supportUnion A B) v = times (evalSupport h A v) (evalSupport h B v) := by
  classical
  let _ := h.meetSemilattice
  exact Finset.inf'_union A.property B.property v

theorem evalNormal_merge {Var : Type v} (F G : NormalForm Var) (v : Var → M) :
    evalNormal h (merge F G) v = plus (evalNormal h F v) (evalNormal h G v) := by
  classical
  let _ := h.joinSemilattice
  exact Finset.sup'_union F.property G.property (fun A => evalSupport h A v)

/-- Repeated finite distribution, justified only by the displayed seven laws. -/
theorem evalNormal_product {Var : Type v} (F G : NormalForm Var) (v : Var → M) :
    evalNormal h (product F G) v = times (evalNormal h F v) (evalNormal h G v) := by
  classical
  let _ := h.joinSemilattice
  symm
  calc
    times (evalNormal h F v) (evalNormal h G v) =
        F.val.sup' F.property (fun A => times (evalSupport h A v) (evalNormal h G v)) := by
      exact Finset.apply_sup'_eq_sup'_comp F.property (fun x => times x (evalNormal h G v))
        (fun x y => h.add_mul x y (evalNormal h G v))
    _ = F.val.sup' F.property (fun A => G.val.sup' G.property
        (fun B => times (evalSupport h A v) (evalSupport h B v))) := by
      apply Finset.sup'_congr F.property rfl
      intro A _
      exact Finset.apply_sup'_eq_sup'_comp G.property (times (evalSupport h A v))
        (h.mul_add (evalSupport h A v))
    _ = evalNormal h (product F G) v := by
      unfold evalNormal product
      rw [Finset.sup'_biUnion (fun C => evalSupport h C v) F.property
        (fun A => G.property.image (supportUnion A))]
      apply Finset.sup'_congr F.property rfl
      intro A _
      rw [← Finset.sup'_comp_eq_image G.property (fun C => evalSupport h C v)]
      apply Finset.sup'_congr G.property rfl
      intro B _
      exact (evalSupport_union h A B v).symm

/-- The normal form denotes the original arbitrary term in every model of
the seven laws, at every variable type and with unrestricted reuse. -/
theorem normalForm_sound [(Equational.language Symbol).Structure M]
    (hM : Laws (M := M) add mul) {Var : Type v} (t : Term Var) (v : Var → M) :
    evalNormal hM (normalForm t) v = t.realize v := by
  induction t with
  | var x =>
    unfold normalForm evalNormal evalSupport
    simp only [Finset.sup'_singleton,Finset.inf'_singleton,FirstOrder.Language.Term.realize_var]
  | @func n sym args ih =>
    cases sym with
    | join =>
      change evalNormal hM (merge (normalForm (args 0)) (normalForm (args 1))) v =
        FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) Symbol.join (fun i => (args i).realize v)
      rw [evalNormal_merge,funMap_join,ih 0,ih 1]
    | mul =>
      change evalNormal hM (product (normalForm (args 0)) (normalForm (args 1))) v =
        FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) Symbol.mul (fun i => (args i).realize v)
      rw [evalNormal_product,funMap_mul,ih 0,ih 1]

end KFOL.Dissemilattice
