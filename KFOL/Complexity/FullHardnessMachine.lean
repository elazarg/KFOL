module
public import KFOL.Complexity.FullHardnessSyntax
public import KFOL.Complexity.RawPairMachines
public import KFOL.Complexity.FullTermMachines
public import KFOL.Complexity.FiniteFoldRuntime
/-! A native translation of original two-owner trees into the original full
syntax. The finite source alphabet is independent of the role count. -/
@[expose] public section
namespace KFOL.Complexity.FullHardness
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

noncomputable def pairNode (a b : ℕ) (operation : Operation RawPair.Symbol)
    (children : List FullTermCode.Raw) : FullTermCode.Raw :=
  match operation with
  | ⟨_,.binary sign⟩ => FullTermMachines.construct ⟨2,.choice (if sign then a else b)⟩ children

private theorem pairNode_polyTime (a b : ℕ) : ComputableInPolyTime
    (fun p : Unit × (Operation RawPair.Symbol × List FullTermCode.Raw) => pairNode a b p.2.1 p.2.2)
    (encPair encUnit (encPair FiniteTermMachines.operationEncoding
      (encList FullTermMachines.termEncoding))) FullTermMachines.termEncoding := by
  let input := encPair encUnit (encPair (FiniteTermMachines.operationEncoding (σ := RawPair.Symbol))
    (encList FullTermMachines.termEncoding))
  have hop : ComputableInPolyTime
      (fun p : Unit × (Operation RawPair.Symbol × List FullTermCode.Raw) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime
      (fun p : Unit × (Operation RawPair.Symbol × List FullTermCode.Raw) => p.2.2)
      input (encList FullTermMachines.termEncoding) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => pairNode a b operation p.2.2)
  intro operation
  rcases operation with ⟨n,operation⟩
  cases operation with
  | binary sign =>
    exact FullTermMachines.construct_polyTime.comp
      ((const (⟨2,.choice (if sign then a else b)⟩ : FullTermCode.Operation)).prod hchildren)

theorem fold_rawPair (a b : ℕ) (t : RawPairMachines.Tree) :
    FiniteFoldMachine.fold (fun (_ : Unit) j => (.var j : FullTermCode.Raw))
      (fun (_ : Unit) op children => pairNode a b op children) () t = rawPair a b t := by
  induction t with
  | var j => rfl
  | func symbol args ih =>
    cases symbol with
    | binary sign =>
      change FullTermMachines.construct ⟨2,.choice (if sign then a else b)⟩
        (List.ofFn (fun i => FiniteFoldMachine.fold
          (fun (_ : Unit) j => (.var j : FullTermCode.Raw))
          (fun (_ : Unit) op children => pairNode a b op children) () (args i))) = _
      rw [FullTermMachines.construct_ofFn]
      change (.func (.choice (if sign then a else b)) _ : FullTermCode.Raw) =
        .func (.choice (if sign then a else b)) _
      congr 1
      funext i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> simp only [ite_true, ite_false, Fin.isValue,
        show (1 : Fin 2) ≠ 0 from by decide, ih]

/-- Maximum of the two literal original owner-header lengths. -/
def ownerHeader (a b : ℕ) : ℕ :=
  max (1 + (Words.delimit (FullTermCode.encodeOperation ⟨2,.choice a⟩)).length)
    (1 + (Words.delimit (FullTermCode.encodeOperation ⟨2,.choice b⟩)).length)

theorem rawPair_length_le (a b : ℕ) (t : RawPairMachines.Tree) :
    (FullTermCode.encode (rawPair a b t)).length ≤
      (ownerHeader a b + 1) * (FiniteTermCode.encode RawPair.Symbol t).length := by
  induction t with
  | var j =>
    change (false :: Words.delimit (Words.BinaryNatCode.encode j)).length ≤ _
    have h : 1 ≤ ownerHeader a b + 1 := by omega
    simpa only [FiniteTermCode.encode_var] using Nat.le_mul_of_pos_left
      (false :: Words.delimit (Words.BinaryNatCode.encode j)).length h
  | func symbol args ih =>
    cases symbol with
    | binary sign =>
      have hhead : 1 + (Words.delimit (FullTermCode.encodeOperation
          ⟨2,.choice (if sign then a else b)⟩)).length ≤ ownerHeader a b + 1 := by
        cases sign <;> simp only [Bool.false_eq_true, ite_false, ite_true, ownerHeader] <;> omega
      have h := Nat.add_le_add (ih 0) (ih 1)
      simp only [rawPair, FullTermCode.encode, FiniteTermCode.encode_func,
        List.ofFn_succ, List.ofFn_zero,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_append] at *
      simp only [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl,
        ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false] at *
      nlinarith

@[fun_prop] theorem rawPair_polyTime (a b : ℕ) : ComputableInPolyTime (rawPair a b)
    RawPairMachines.termEncoding FullTermMachines.termEncoding := by
  have h := FiniteFoldMachine.fold_polyTime
    (contextEncoding := encUnit) (valueEncoding := FullTermMachines.termEncoding)
    (fun (_ : Unit) j => (.var j : FullTermCode.Raw))
    (fun (_ : Unit) op children => pairNode a b op children)
    (FullTermMachines.var_polyTime.comp (snd _ _)) (pairNode_polyTime a b)
    (ownerHeader a b + 1) 1 (fun contextUnit t => by
      cases contextUnit
      rw [fold_rawPair]
      have hb := rawPair_length_le a b t
      change (FullTermCode.encode (rawPair a b t)).length ≤ _
      simp only [Nat.pow_one]
      nlinarith) (.var 0)
  have hunit := h.comp ((const ()).prod (id' (encIn := RawPairMachines.termEncoding)))
  simpa only [Function.comp_def, fold_rawPair] using hunit
end KFOL.Complexity.FullHardness
