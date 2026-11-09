module

public import KFOL.Definitions.Algorithms
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing

/-! # Binary encodings at the external word-codec boundary

The mathematical algebra and support indexing do not import this module.
Binary natural codes and self-delimiting framing are reused from ComplexityLib.
-/

@[expose] public section

namespace KFOL.Algorithms

namespace GuardRecord

/-- A compressed output position and its prerequisite positions. -/
abbrev Record (n : ℕ) := Fin n × Finset (Fin n)

/-- The binary output index is framed once, followed by the fixed-width
membership word. Neither field uses a unary numeric-value encoding. -/
def encode {n : ℕ} (r : Record n) : List Bool :=
  _root_.Complexity.pair (_root_.Complexity.BinaryNatCode.encode r.1.val) (Bitset.encode r.2)

/-- Reject bad framing, noncanonical binary indices, out-of-range outputs
and payloads of the wrong width. -/
def decode (n : ℕ) (word : List Bool) : Option (Record n) := do
  let (index, payload) ← _root_.Complexity.unpair? word
  let j ← _root_.Complexity.BinaryNatCode.decode? index
  if h : j < n then
    let A ← Bitset.decode n payload
    return (⟨j, h⟩, A)
  else none

/-- Independently frame each record. Framing does not recursively double
the already encoded tail of the table. -/
def encodeList {n : ℕ} (records : List (Record n)) : List Bool :=
  ((records.map encode).map _root_.Complexity.delimit).flatten

/-- Parse complete framed records, consuming the entire input. -/
def decodeList (n : ℕ) (word : List Bool) : Option (List (Record n)) := do
  let blocks ← _root_.Complexity.undelimitBlocks word
  blocks.mapM (decode n)

end GuardRecord

namespace LabelDictionary

/-- Sparse natural variable names keep their canonical binary representation. -/
def encode (labels : List ℕ) : List Bool :=
  ((labels.map _root_.Complexity.BinaryNatCode.encode).map _root_.Complexity.delimit).flatten

/-- Decode a complete label sequence; dictionary uniqueness is supplied by
the actual-support construction, independently of this list codec. -/
def decode (word : List Bool) : Option (List ℕ) := do
  let blocks ← _root_.Complexity.undelimitBlocks word
  blocks.mapM _root_.Complexity.BinaryNatCode.decode?

end LabelDictionary
end KFOL.Algorithms
