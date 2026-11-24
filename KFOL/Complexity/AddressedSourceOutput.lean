module

public import KFOL.Complexity.AddressTableOutput
public import KFOL.Complexity.AddressedEnvelope
public import KFOL.Complexity.FullSparseSemantics
public import KFOL.Core.SourceNormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! # Projecting an explicit winner table to its isolated-source table

For arity d, the source encoding contains d blocks, one for each head.
A block contains k^d bits in increasing base-k order. The digit of the
head gives the observer. At the other coordinates its digit stands for
the neutral menu and each other digit stands for its singleton.

On a well-formed input the number of signatures in each block is bounded
by the supplied winner table length. This also gives a polynomial clock on
malformed inputs. All identifiers in the winner menus are binary.
-/

@[expose] public section
namespace KFOL.Complexity.AddressedSourceOutput

open AddressTableOutput AddressedEnvelope Turing.MultiTapeTM ComputableInPolyTime

abbrev RawTable := ℕ × List Names
abbrev tableEncoding := encPair encUnary (encList namesEncoding)
abbrev sourceEncoding := encPair encUnary encBits

def probeFlag (observer color role : ℕ) (atHead : Bool) : Bool :=
  if atHead || decide (color ≠ observer) then decide (role = color) else decide (role ≠ observer)

def sameInput (k d i head s : ℕ) : Bool :=
  (List.range d).all fun j => (List.range k).all fun r =>
    decide ((mask k i j).testBit r = probeFlag (digit k s head) (digit k s j) r (decide (j = head)))

/-- Find the unique tuple representing the probe and read its winner bit.
The scan is bounded by the explicit length supplied on the input. -/
def lookup (k : ℕ) (raw : RawTable) (head s : ℕ) : Bool :=
  (List.range raw.2.length).any fun i =>
    sameInput k raw.1 i head s &&
      AddressedEnvelope.member (digit k s head) (raw.2.getD i [])

def blockSize (k : ℕ) (raw : RawTable) : ℕ := min (k ^ raw.1) raw.2.length

def project (k : ℕ) (raw : RawTable) : ℕ × List Bool :=
  (raw.1, (List.range (raw.1 * blockSize k raw)).map fun t =>
    lookup k raw (t / blockSize k raw) (t % blockSize k raw))

variable {X : Type} {input : X ↪ List Bool}

theorem digit_poly (k : ℕ) {s j : X → ℕ} (hs : ComputableInPolyTime s input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => digit k (s x) (j x)) input encNat := by
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_div'
    (ComputableTidilyInPolyTime.unary_to_binary.comp hs.tidy)
    (ComputableTidilyInPolyTime.binary_pow' (.const _) hj.tidy)) (.const _))

private theorem probe_flag_poly {r t j : X → ℕ} {atHead : X → Bool}
    (hr : ComputableInPolyTime r input encNat) (ht : ComputableInPolyTime t input encNat)
    (hj : ComputableInPolyTime j input encNat) (hh : ComputableInPolyTime atHead input encBool) :
    ComputableInPolyTime (fun x => probeFlag (r x) (t x) (j x) (atHead x)) input encBool := by
  have test := bool_or.comp (hh.prod (bool_not.comp (decide_eq' ht hr)))
  simpa only [probeFlag, Function.comp_apply, decide_not] using
    test.ite (decide_eq' hj ht) (bool_not.comp (decide_eq' hj hr))

theorem same_input_poly (k : ℕ) {d i h s : X → ℕ} (hd : ComputableInPolyTime d input encUnary)
    (hi : ComputableInPolyTime i input encUnary) (hh : ComputableInPolyTime h input encUnary)
    (hs : ComputableInPolyTime s input encUnary) :
    ComputableInPolyTime (fun x => sameInput k (d x) (i x) (h x) (s x)) input encBool := by
  let ij := encPair input encUnary
  let pre := fst input encUnary
  let pre' := fst ij encUnary
  let j := snd input encUnary
  let r := snd ij encUnary
  have bit := ComputableTidilyInPolyTime.binary_testBit
    ((mask_poly k (hi.comp pre) j).comp pre').tidy r.tidy
  have flag := probe_flag_poly (((digit_poly k hs hh).comp pre).comp pre')
    ((digit_poly k (hs.comp pre) j).comp pre') (unary_to_binary.comp r)
    ((decide_eq' j (hh.comp pre)).comp pre')
  have inner := allWithInput (test := fun (p : X × ℕ) r => decide ((mask k (i p.1) p.2).testBit r =
    probeFlag (digit k (s p.1) (h p.1)) (digit k (s p.1) p.2) r (decide (p.2 = h p.1))))
    (const (List.range k)) (decide_eq' (ComputableInPolyTime.of_tidy bit) flag)
  exact allWithInput (test := fun x j => (List.range k).all fun r =>
    decide ((mask k (i x) j).testBit r =
      probeFlag (digit k (s x) (h x)) (digit k (s x) j) r (decide (j = h x))))
    (ComputableInPolyTime.range.comp hd) inner

theorem lookup_poly (k : ℕ) {raw : X → RawTable} {h s : X → ℕ}
    (hp : ComputableInPolyTime raw input tableEncoding)
    (hh : ComputableInPolyTime h input encUnary) (hs : ComputableInPolyTime s input encUnary) :
    ComputableInPolyTime (fun x => lookup k (raw x) (h x) (s x)) input encBool := by
  have len := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length namesEncoding)).comp hp.snd'
  apply anyWithInput (ComputableInPolyTime.range.comp len)
  let pre := fst input encUnary
  let i := snd input encUnary
  have pass := same_input_poly k (hp.fst'.comp pre) i (hh.comp pre) (hs.comp pre)
  have val := (listGetD (encA := namesEncoding) (encL := encList namesEncoding) []).comp
    ((hp.snd'.comp pre).prod i)
  exact bool_and' pass (member_polyTime.comp (((digit_poly k hs hh).comp pre).prod val))

theorem block_poly (k : ℕ) {raw : X → RawTable} (hp : ComputableInPolyTime raw input tableEncoding) :
    ComputableInPolyTime (fun x => blockSize k (raw x)) input encUnary := by
  have len := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length namesEncoding)).comp hp.snd'
  apply (binary_min_unary' len (binary_pow' (const k) hp.fst')).of_enc_eq
  intro x
  simp only [blockSize,Function.comp_apply]
  rw [Nat.min_comm]

/-- A concrete polynomial-time reduction on the two explicit formats.
The source output stores its Boolean block without per-bit framing. -/
theorem project_poly (k : ℕ) : ComputableInPolyTime (project k) tableEncoding sourceEncoding := by
  let pre := fst tableEncoding encUnary
  let pos := snd tableEncoding encUnary
  have block := block_poly k (id' (encIn := tableEncoding))
  have coords := pos.prod (block.comp pre)
  have bits := mapWithInput (f := fun (raw : RawTable) i =>
    lookup k raw (i / blockSize k raw) (i % blockSize k raw))
    (ComputableInPolyTime.range.comp (unary_mul' (fst _ _) block))
    (lookup_poly k pre (unary_div.comp coords) (unary_mod.comp coords))
  exact (fst encUnary (encList namesEncoding)).prod ((bits_encList_polyTime encBool).2.comp bits)

end KFOL.Complexity.AddressedSourceOutput
