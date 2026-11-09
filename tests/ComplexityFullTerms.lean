module
public import KFOL.Complexity.FullTermDecoding
public import KFOL.Algorithms.FullTermCode.View
@[expose] public section
namespace KFOLTest.ComplexityFullTerms
open KFOL KFOL.FullTermCode KFOL.Complexity Turing.MultiTapeTM
example (operation : Operation) : operation.1 ≤ 2 := arity_le_two operation
example : decodeOperation [true,true] = none := rfl
example : decodeOperation [false] = none := rfl
example (array : List ℕ) : decodeOperation (encodeOperation ⟨1,.rename array⟩) = some ⟨1,.rename array⟩ :=
  decodeOperation_encodeOperation _
example (tree : Raw) : decode (encode tree) = some tree := decode_encode tree
example : ComputableInPolyTime (fun tree => decode (encode tree)) FullTermMachines.termEncoding (encOption FullTermMachines.termEncoding) := by
  have h := FullTermMachines.decode_polyTime
  exact h.comp FullTermMachines.encode_polyTime
example : ComputableInPolyTime decode encBits (encOption FullTermMachines.termEncoding) := FullTermMachines.decode_polyTime
example {Context Value : Type} (contextE : Context ↪ List Bool) (valueE : Value ↪ List Bool)
    (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2) (encPair contextE encNat) valueE)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextE (encPair FullTermMachines.operationEncoding (encList valueE))) valueE)
    (c degree : ℕ) (hsize : ∀ context tree, (valueE (FullTermFold.fold leaf node context tree)).length ≤
      c * ((contextE context).length + (encode tree).length + 1)^degree) (fallback : Value) :
    ComputableInPolyTime (fun p : Context × Raw => FullTermFold.fold leaf node p.1 p.2)
      (encPair contextE FullTermMachines.termEncoding) valueE :=
  FullTermFold.fold_polyTime leaf node hleaf hnode c degree hsize fallback
end KFOLTest.ComplexityFullTerms
