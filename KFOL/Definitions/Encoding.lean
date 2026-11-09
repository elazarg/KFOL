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

namespace TermCode

/-- Prefix binary syntax: `false` introduces a framed canonical binary
variable name; `true` introduces two successive child trees. Only labels
are framed, so nesting never duplicates an already encoded subtree. -/
def encode : Reset.Term ℕ → List Bool
  | .var j => false :: _root_.Complexity.delimit (_root_.Complexity.BinaryNatCode.encode j)
  | .func .reset args => true :: (encode (args 0) ++ encode (args 1))

/-- Parse one tree and return its unconsumed suffix. Fuel bounds recursive
depth and is supplied from the input bit length, never a decoded label value. -/
def parse : ℕ → List Bool → Option (Reset.Term ℕ × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: word => do
      let (name, rest) ← _root_.Complexity.unpair? word
      let j ← _root_.Complexity.BinaryNatCode.decode? name
      return (.var j, rest)
  | fuel + 1, true :: word => do
      let (left, rest) ← parse fuel word
      let (right, rest) ← parse fuel rest
      return (Reset.Term.step left right, rest)

/-- A term input contains exactly one complete tree, with no trailing bits. -/
def decode (word : List Bool) : Option (Reset.Term ℕ) := do
  let (t, rest) ← parse word.length word
  if rest.isEmpty then some t else none

/-- Executable binary frontend: decode the original tree, collect its actual
support and raw guards, and pair the dictionary with the compressed record stream. -/
def extract (word : List Bool) : Option (List Bool) := do
  let t ← decode word
  let D := SupportIndex.labels t
  let records ← t.guardEntries.mapM (SupportIndex.compressEntry D)
  return _root_.Complexity.pair (LabelDictionary.encode D) (GuardRecord.encodeList records)

end TermCode
end KFOL.Algorithms
