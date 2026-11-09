/-
Framing definitions adapted from ComplexityLib v1, revision 257ad90.
Copyright (c) 2025-2026 Samuel Schlesinger and Bolton Bailey.
Those adapted parts are under Apache 2.0; see LICENSES/Apache-2.0.txt.
-/
module

public import KFOL.Definitions.Algorithms
public import Mathlib.Data.Nat.Size

/-! # Binary encodings at the external word-codec boundary

The mathematical algebra and support indexing do not import this module.
Binary names and framing have an independent mathlib-only definition below,
so backend upgrades do not change the serialized language.
-/

@[expose] public section

namespace KFOL.Words

namespace BinaryNatCode

/-- Interpret little-endian bits without using a decoded value as a clock. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bits => Nat.bit b (value bits)

/-- The minimal little-endian representation, with the empty word for zero. -/
def encode (n : ℕ) : List Bool := n.bits

/-- Accept exactly the minimal binary representation of the interpreted value. -/
def decode? (bits : List Bool) : Option ℕ :=
  let n := value bits
  if n.bits = bits then some n else none

end BinaryNatCode

/-- Double payload bits and terminate with the separator `false,true`. -/
def delimit (word : List Bool) : List Bool :=
  (word.flatMap fun b => [b, b]) ++ [false, true]

/-- Parse a complete first frame, returning the remaining suffix. -/
def unpair? : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: true :: rest => some ([], rest)
  | false :: false :: rest => (unpair? rest).map (fun p => (false :: p.1, p.2))
  | true :: true :: rest => (unpair? rest).map (fun p => (true :: p.1, p.2))
  | _ => none

/-- Frame the first word; retain the second word verbatim. This paper codec
has a two-bit separator and is distinct from native machine input pairing. -/
def pair (left right : List Bool) : List Bool := delimit left ++ right

/-- Parse a sequence of complete frames, with one unit of fuel per frame. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, word => do
    let (block, rest) ← unpair? word
    let blocks ← undelimitBlocksAux fuel rest
    return block :: blocks

/-- Every frame is nonempty, so bit length supplies sufficient frame fuel. -/
def undelimitBlocks (word : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux word.length word

end KFOL.Words

namespace KFOL.Algorithms

namespace GuardRecord

/-- A compressed output position and its prerequisite positions. -/
abbrev Record (n : ℕ) := Fin n × Finset (Fin n)

/-- The binary output index is framed once, followed by the fixed-width
membership word. Neither field uses a unary numeric-value encoding. -/
def encode {n : ℕ} (r : Record n) : List Bool :=
  _root_.KFOL.Words.pair (_root_.KFOL.Words.BinaryNatCode.encode r.1.val) (Bitset.encode r.2)

/-- Reject bad framing, noncanonical binary indices, out-of-range outputs
and payloads of the wrong width. -/
def decode (n : ℕ) (word : List Bool) : Option (Record n) := do
  let (index, payload) ← _root_.KFOL.Words.unpair? word
  let j ← _root_.KFOL.Words.BinaryNatCode.decode? index
  if h : j < n then
    let A ← Bitset.decode n payload
    return (⟨j, h⟩, A)
  else none

/-- Independently frame each record. Framing does not recursively double
the already encoded tail of the table. -/
def encodeList {n : ℕ} (records : List (Record n)) : List Bool :=
  ((records.map encode).map _root_.KFOL.Words.delimit).flatten

/-- Parse complete framed records, consuming the entire input. -/
def decodeList (n : ℕ) (word : List Bool) : Option (List (Record n)) := do
  let blocks ← _root_.KFOL.Words.undelimitBlocks word
  blocks.mapM (decode n)

end GuardRecord

namespace LabelDictionary

/-- Sparse natural variable names keep their canonical binary representation. -/
def encode (labels : List ℕ) : List Bool :=
  ((labels.map _root_.KFOL.Words.BinaryNatCode.encode).map _root_.KFOL.Words.delimit).flatten

/-- Decode a complete label sequence; dictionary uniqueness is supplied by
the actual-support construction, independently of this list codec. -/
def decode (word : List Bool) : Option (List ℕ) := do
  let blocks ← _root_.KFOL.Words.undelimitBlocks word
  blocks.mapM _root_.KFOL.Words.BinaryNatCode.decode?

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
  _root_.KFOL.Words.pair (LabelDictionary.encode d.labels) (GuardRecord.encodeList d.records)

/-- Validate framing, canonical binary labels, dictionary uniqueness and
every record's output range and prerequisite width, consuming all input. -/
def decode (word : List Bool) : Option GuardDescriptor := do
  let (dict, stream) ← _root_.KFOL.Words.unpair? word
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

/-- Delete dominated prerequisites at each output by scanning only listed
records. Minimal duplicate records retain their original order and multiplicity. -/
def minimalRecords (d : GuardDescriptor) : List (GuardRecord.Record d.labels.length) :=
  d.records.filter (fun p => decide
    (∀ q ∈ d.records, q.1 = p.1 → q.2 ⊆ p.2 → p.2 ⊆ q.2))

/-- A structural wrapper retaining the original dictionary and its index type. -/
abbrev normalize (d : GuardDescriptor) : GuardDescriptor :=
  ⟨d.labels, d.distinct, d.minimalRecords⟩

/-- Normalize a complete external descriptor; malformed inputs are rejected. -/
def normalizeWord (word : List Bool) : Option (List Bool) := do
  let d ← decode word
  return encode d.normalize

end GuardDescriptor

namespace TermCode

/-- Prefix binary syntax: `false` introduces a framed canonical binary
variable name; `true` introduces two successive child trees. Only labels
are framed, so nesting never duplicates an already encoded subtree. -/
def encode : Reset.Term ℕ → List Bool
  | .var j => false :: _root_.KFOL.Words.delimit (_root_.KFOL.Words.BinaryNatCode.encode j)
  | .func .reset args => true :: (encode (args 0) ++ encode (args 1))

/-- Parse one tree and return its unconsumed suffix. Fuel bounds recursive
depth and is supplied from the input bit length, never a decoded label value. -/
def parse : ℕ → List Bool → Option (Reset.Term ℕ × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: word => do
      let (name, rest) ← _root_.KFOL.Words.unpair? word
      let j ← _root_.KFOL.Words.BinaryNatCode.decode? name
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
  return _root_.KFOL.Words.pair (LabelDictionary.encode D) (GuardRecord.encodeList records)

end TermCode

namespace ResetEquation

/-- Both terms use the same finite dictionary, including all variables of
either side. Numeric names do not determine its dimension. -/
def labels (s t : Reset.Term ℕ) : List ℕ :=
  (SupportIndex.labels s ++ SupportIndex.labels t).dedup

/-- Compare normalized listed guards on a shared dictionary. This uses
finite positions, not equality of independently serialized descriptors. -/
def check (s t : Reset.Term ℕ) : Bool := Id.run do
  let D := labels s t
  let some left := s.guardEntries.mapM (SupportIndex.compressEntry D) | return false
  let some right := t.guardEntries.mapM (SupportIndex.compressEntry D) | return false
  let a : GuardDescriptor := ⟨D, List.nodup_dedup _, left⟩
  let b : GuardDescriptor := ⟨D, List.nodup_dedup _, right⟩
  return (List.ofFn (fun i : Fin D.length =>
    let leftGuards : Finset (Finset (Fin D.length)) := a.normalize.guards i
    let rightGuards : Finset (Finset (Fin D.length)) := b.normalize.guards i
    decide (leftGuards = rightGuards))).all id

/-- A binary equation is a pair of original tree codes. Malformed pairs or
trees are rejected before the shared-support equality check. -/
def checkWord (word : List Bool) : Bool :=
  match _root_.KFOL.Words.unpair? word with
  | none => false
  | some (left, right) =>
    match TermCode.decode left, TermCode.decode right with
    | some s, some t => check s t
    | _, _ => false

end ResetEquation
end KFOL.Algorithms
