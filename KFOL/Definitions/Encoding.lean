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

/-- Complete dictionary/record data. Distinct names give a faithful map from
finite positions to labels; records may repeat and dictionary positions may
be unused. Canonicality and realizability are checked separately. -/
structure GuardDescriptor where
  labels : List ℕ
  distinct : labels.Nodup
  records : List (GuardRecord.Record labels.length)

namespace GuardDescriptor

/-- The same single-word format produced by original-term extraction. -/
def encode (d : GuardDescriptor) : List Bool :=
  _root_.Complexity.pair (LabelDictionary.encode d.labels) (GuardRecord.encodeList d.records)

/-- Validate framing, canonical binary labels, dictionary uniqueness and
every record's output range and prerequisite width, consuming all input. -/
def decode (word : List Bool) : Option GuardDescriptor := do
  let (dict, stream) ← _root_.Complexity.unpair? word
  let labels ← LabelDictionary.decode dict
  if h : labels.Nodup then
    let records ← GuardRecord.decodeList labels.length stream
    return ⟨labels, h, records⟩
  else none

/-- All explicitly listed prerequisites at an output, interpreted as a set.
Duplicate records do not change the table; dominated guards are retained. -/
def guards (d : GuardDescriptor) (j : Fin d.labels.length) : Finset (Finset (Fin d.labels.length)) :=
  (d.records.toFinset.filter (fun p => p.1 = j)).image Prod.snd

/-- Choose the first listed output with an empty prerequisite, if present.
The semantic checker ensures that a valid table has exactly one such output. -/
def root? (d : GuardDescriptor) : Option (Fin d.labels.length) :=
  (d.records.find? (fun p => decide (p.2 = ∅))).map Prod.fst

/-- Candidate table at a supplied root, independent of the recognizer. -/
def table (d : GuardDescriptor) (r : Fin d.labels.length) : Reset.GuardTable (Fin d.labels.length) :=
  ⟨r, d.guards⟩

/-- Check the actual listed tables, without silently removing dominated
guards. An empty descriptor parses successfully but fails this semantic check. -/
def check (d : GuardDescriptor) : Bool :=
  match d.root? with
  | none => false
  | some r => (d.table r).check

/-- Total external recognizer: malformed descriptors and unrealizable
canonical candidates are both rejected. -/
def recognize (word : List Bool) : Bool :=
  match decode word with
  | none => false
  | some d => d.check

end GuardDescriptor

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
