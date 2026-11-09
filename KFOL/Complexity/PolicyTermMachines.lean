module

public import KFOL.Complexity.FiniteTermMachines
public import KFOL.Definitions.Policies

/-! Fixed finite policy alphabets use the generic original finite-signature codec. -/

@[expose] public section

namespace KFOL.Complexity.PolicyTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

variable {Label : Type} [Fintype Label]

def operationEquiv : Operation (Policies.Symbol Label) ≃ Option Label where
  toFun p := match p with
    | ⟨_, .reset⟩ => none
    | ⟨_, .selective label⟩ => some label
  invFun p := match p with
    | none => ⟨2, .reset⟩
    | some label => ⟨3, .selective label⟩
  left_inv p := by cases p with | mk n symbol => cases symbol <;> rfl
  right_inv p := by cases p <;> rfl

noncomputable instance operationFintype : Fintype (Operation (Policies.Symbol Label)) :=
  Fintype.ofEquiv (Option Label) (operationEquiv (Label := Label)).symm

noncomputable abbrev termEncoding : Policies.Term Label ℕ ↪ List Bool :=
  FiniteTermMachines.termEncoding

@[fun_prop] theorem var_polyTime : ComputableInPolyTime
    (fun j : ℕ => (.var j : Policies.Term Label ℕ)) encNat termEncoding :=
  FiniteTermMachines.var_polyTime

@[fun_prop] theorem step_polyTime : ComputableInPolyTime
    (fun p : Policies.Term Label ℕ × Policies.Term Label ℕ => Policies.Term.step p.1 p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have hl := cons' (fst (termEncoding (Label := Label)) (termEncoding (Label := Label)))
    (cons' (snd (termEncoding (Label := Label)) (termEncoding (Label := Label))) (const []))
  have h := (FiniteTermMachines.construct_fixed_polyTime
    (⟨2, .reset⟩ : Operation (Policies.Symbol Label))).comp hl
  convert h using 1
  funext p
  unfold Policies.Term.step FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

@[fun_prop] theorem selective_polyTime (label : Label) : ComputableInPolyTime
    (fun p : Policies.Term Label ℕ × (Policies.Term Label ℕ × Policies.Term Label ℕ) =>
      Policies.Term.selective label p.1 p.2.1 p.2.2)
    (encPair termEncoding (encPair termEncoding termEncoding)) termEncoding := by
  let input := encPair (termEncoding (Label := Label))
    (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  have hx := fst (termEncoding (Label := Label))
    (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  have hy : ComputableInPolyTime
      (fun p : Policies.Term Label ℕ × (Policies.Term Label ℕ × Policies.Term Label ℕ) => p.2.1)
      input termEncoding := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : Policies.Term Label ℕ × (Policies.Term Label ℕ × Policies.Term Label ℕ) => p.2.2)
      input termEncoding := by fun_prop
  have hl := cons' hx (cons' hy (cons' hz (const [])))
  have h := (FiniteTermMachines.construct_fixed_polyTime
    (⟨3, .selective label⟩ : Operation (Policies.Symbol Label))).comp hl
  convert h using 1
  funext p
  unfold Policies.Term.selective FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp

noncomputable def resetHeader : ℕ :=
  1 + (Words.delimit (encodeOperation (Policies.Symbol Label) ⟨2, .reset⟩)).length

noncomputable def selectiveHeader (label : Label) : ℕ :=
  1 + (Words.delimit (encodeOperation (Policies.Symbol Label) ⟨3, .selective label⟩)).length

theorem length_step (s t : Policies.Term Label ℕ) :
    (termEncoding (Policies.Term.step s t)).length =
      (termEncoding s).length + (termEncoding t).length + resetHeader (Label := Label) := by
  simp [termEncoding, FiniteTermMachines.termEncoding, Policies.Term.step, encode_func,
    resetHeader, List.ofFn_succ, add_comm, add_left_comm, add_assoc]

theorem length_selective (label : Label) (x y z : Policies.Term Label ℕ) :
    (termEncoding (Policies.Term.selective label x y z)).length =
      (termEncoding x).length + (termEncoding y).length + (termEncoding z).length + selectiveHeader label := by
  simp [termEncoding, FiniteTermMachines.termEncoding, Policies.Term.selective, encode_func,
    selectiveHeader, List.ofFn_succ, add_comm, add_left_comm, add_assoc]

end KFOL.Complexity.PolicyTermMachines
