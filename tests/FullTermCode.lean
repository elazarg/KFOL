module

import KFOL.Algorithms.FullTermCode.View

namespace KFOL.Tests.FullTermCode
open KFOL.FullTermCode

/-- Every original node and full explicit permutation array survives a raw
word roundtrip; this works uniformly in the actual binary role count. -/
example {K : ℕ} (term : Term (Fin K) ℕ) :
    decode (encode (view term)) = some (view term) := decode_encode _

example (K name : ℕ) : encodeInput ⟨K,.var name⟩ =
    Words.pair (Words.BinaryNatCode.encode K) (false :: Words.delimit (Words.BinaryNatCode.encode name)) := rfl

example : decodeOperation [true,true] = none := rfl
example : decodeOperation [false,false] = none := rfl

/-- Noncommuting switches are retained as distinct original source nodes. -/
example : view (Term.rename (Equiv.swap (0:Fin 3) 1)
    (.rename (Equiv.swap 1 2) (.var 7))) =
    .func (.rename [1,0,2]) (fun _ =>
      .func (.rename [0,2,1]) (fun _ => .var 7)) := by
  rfl

#print axioms encode_append_of_parse
#print axioms encodeInput_injective

end KFOL.Tests.FullTermCode
