module

public import KFOL.Complexity.DescriptorValidation

/-! Cross-representation checks for the native machine and paper word codecs. -/

@[expose] public section

namespace KFOLTest.ComplexityCodecs

open KFOL KFOL.Algorithms Turing.MultiTapeTM

set_option maxRecDepth 4096

-- Native machine product framing and the preserved paper word framing differ.
example : encPair encBits encBits ([], []) = [false] := by decide
example : Words.pair [] [] = [false, true] := by decide
example : encPair encBits encBits ([true], [false]) = [true, true, false, false] := by decide
example : Words.pair [true] [false] = [true, true, false, true, false] := by decide

-- Sparse natural names remain binary in the native intermediate representation.
example : (encNat 100000).length = 17 := by decide
example : (encOption (encList encNat)
    (LabelDictionary.decode (LabelDictionary.encode [100000, 7]))).length = 43 := by decide
example : encOption encNat (Words.BinaryNatCode.decode? []) = [true] := by decide
example : encOption encNat (Words.BinaryNatCode.decode? [false]) = [] := by decide

private def descriptor : GuardDescriptor := ⟨[7, 42], by decide, [(1, ∅), (0, {1})]⟩

-- The typed decoder returns precisely its existing paper serialization.
example : encOption KFOL.Complexity.DescriptorValidation.descriptorEncoding
    (GuardDescriptor.decode (GuardDescriptor.encode descriptor)) =
      true :: GuardDescriptor.encode descriptor := by decide
example : (encOption KFOL.Complexity.DescriptorValidation.descriptorEncoding
    (GuardDescriptor.decode (GuardDescriptor.encode descriptor))).length = 71 := by decide
example : encOption KFOL.Complexity.DescriptorValidation.descriptorEncoding
    (GuardDescriptor.decode [true]) = [] := by decide

end KFOLTest.ComplexityCodecs
