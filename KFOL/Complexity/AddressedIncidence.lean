module

public import KFOL.Complexity.AddressedEnvelope
public import KFOL.Complexity.RecognitionHardness
public import KFOL.Core.AddressSize
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! # Listing the numbered addressed rectangle in polynomial time

The input consists of the original alternating prefix length, the stage
count before separating literal slots, and the final matrix and stage count.
Numbers in the output, including indices of rails, are written in binary.
-/

@[expose] public section
namespace KFOL.Complexity.AddressedIncidence

open Turing.MultiTapeTM Recognition.Lists Core.AddressSize AddressedEnvelope

abbrev Matrix := List (List (ℕ × ℕ))

/-- Stages after the first cutoff are existential auxiliaries. -/
def exAt (old i : ℕ) : Bool := if i ≤ old then exB old i else true

def leftT (z : Tup) : Bool := z.1 == 0 || z.1 == 3

def markCode (old n : ℕ) (z : Tup) : Tup :=
  if z.1 == 0 then
    (if z.2.1 ≤ n then (0, z.2.1, if exAt old z.2.1 then z.2.2 else 1)
     else (4, z.2.1 - n - 1, 0))
  else if z.1 == 1 then (1, z.2.1, 0)
  else if z.1 == 2 then (3, z.2.1, z.2.2)
  else (4, z.2.1, 0)

def rightT (old n : ℕ) (z e : Tup) : Bool :=
  (z.1 == 1 && e.1 == 0 && e.2.1 == z.2.1 + 1 && decide (e.2.1 ≤ n) &&
    (e.2.2 == 1 || exAt old e.2.1)) ||
  (z.1 == 1 && e.1 == 1 && e.2.1 == z.2.1 + 1) ||
  (z.1 == 1 && e.1 == 3 && decide (n ≤ z.2.1)) ||
  (z.1 == 1 && e.1 == 4 && z.2.1 == n + e.2.1) ||
  (z.1 == 2 && e.1 == 2 && e.2.1 == z.2.1 && e.2.2 == z.2.2)

def serialT (e : Tup) : ℕ :=
  8 * e.2.1 +
  (if e.1 == 0 then e.2.2 else if e.1 == 1 then 2 else if e.1 == 2 then 3+e.2.2
   else if e.1 == 3 then 5+e.2.2 else 7)

/-- Logical identifiers reserve zero and one for the two private labels. -/
def nameT (e : Tup) : ℕ := 2 + serialT e

def slotT (h i : ℕ) : ℕ := if i ≤ h then 0 else if i ≤ 2*h then 1 else 2

def trackT (h : ℕ) (e : Tup) : ℕ :=
  if e.1 == 0 then 2 * (e.2.1 % 2) + e.2.2 else if e.1 == 1 then 4 + e.2.1 % 2
  else if e.1 == 2 then 6 else if e.1 == 3 then 7 + slotT h e.2.1 else 10 + e.2.1 % 2

def postings (old n : ℕ) (cls : Matrix) (side : Bool) (z : Tup) : Names :=
  toBin side.toNat :: (((labsT n cls.length).filter fun e =>
    if side then inIB n cls z e else rightT old n z e).map fun e => toBin (nameT e))

/-- The endpoint and every marked row of this orientation. -/
def rowData (old n : ℕ) (cls : Matrix) (side : Bool) : RowData :=
  (postings old n cls side (if side then (0,0,0) else (1,0,0)),
    ((rowsT n cls.length).filter fun z => leftT z == side).map fun z =>
      (toBin (nameT (markCode old n z)), postings old n cls side z))

/-- Flatten a rail into the menu tuple. Coordinate zero is the selector. -/
def pos (d g i b : ℕ) : ℕ := 1 + 2 * (g*d+i) + b

def code (d g serial : ℕ) : Names :=
  (List.range d).map fun i => toBin (pos d g i (serial.testBit i).toNat)

/-- Every logical label and the tuple coordinates in its address. Both
private tracks use the all-zero digits. -/
def addresses (h n m : ℕ) : List Entry :=
  let d := width (8 * (n+m+1))
  [(toBin 0,code d 12 0), (toBin 1,code d 13 0)] ++
    ((labsT n m).map fun e => (toBin (nameT e),code d (trackT h e) (serialT e)))

variable {X : Type} {input : X ↪ List Bool}

@[fun_prop] theorem exAt_poly {o i : X → ℕ} (ho : ComputableInPolyTime o input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => exAt (o x) (i x)) input encBool := by unfold exAt; fun_prop

@[fun_prop] theorem leftT_poly {z : X → Tup} (hz : ComputableInPolyTime z input eTup) :
    ComputableInPolyTime (fun x => leftT (z x)) input encBool := by unfold leftT; fun_prop

@[fun_prop] theorem markCode_poly {o n : X → ℕ} {z : X → Tup}
    (ho : ComputableInPolyTime o input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hz : ComputableInPolyTime z input eTup) :
    ComputableInPolyTime (fun x => markCode (o x) (n x) (z x)) input eTup := by unfold markCode; fun_prop

@[fun_prop] theorem rightT_poly {o n : X → ℕ} {z e : X → Tup}
    (ho : ComputableInPolyTime o input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hz : ComputableInPolyTime z input eTup) (he : ComputableInPolyTime e input eTup) :
    ComputableInPolyTime (fun x => rightT (o x) (n x) (z x) (e x)) input encBool := by unfold rightT; fun_prop

@[fun_prop] theorem serialT_poly {e : X → Tup} (he : ComputableInPolyTime e input eTup) :
    ComputableInPolyTime (fun x => serialT (e x)) input encUnary := by unfold serialT; fun_prop

@[fun_prop] theorem nameT_poly {e : X → Tup} (he : ComputableInPolyTime e input eTup) :
    ComputableInPolyTime (fun x => nameT (e x)) input encUnary := by unfold nameT; fun_prop

@[fun_prop] theorem slotT_poly {h i : X → ℕ} (hh : ComputableInPolyTime h input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => slotT (h x) (i x)) input encUnary := by unfold slotT; fun_prop

@[fun_prop] theorem trackT_poly {h : X → ℕ} {e : X → Tup}
    (hh : ComputableInPolyTime h input encUnary) (he : ComputableInPolyTime e input eTup) :
    ComputableInPolyTime (fun x => trackT (h x) (e x)) input encUnary := by
  have index : ComputableInPolyTime (fun x => (e x).2.1) input encUnary := by fun_prop
  have imod : ComputableInPolyTime (fun x => (e x).2.1 % 2) input encUnary :=
    ComputableInPolyTime.unary_mod.comp (index.prod (.const 2))
  unfold trackT
  fun_prop

@[fun_prop] theorem postings_poly {o n : X → ℕ} {cls : X → Matrix} {s : X → Bool} {z : X → Tup}
    (ho : ComputableInPolyTime o input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime cls input (encList eLoss)) (hs : ComputableInPolyTime s input encBool)
    (hz : ComputableInPolyTime z input eTup) :
    ComputableInPolyTime (fun x => postings (o x) (n x) (cls x) (s x) (z x)) input namesEncoding := by
  unfold postings
  fun_prop

@[fun_prop] theorem rowData_poly {o n : X → ℕ} {cls : X → Matrix} {s : X → Bool}
    (ho : ComputableInPolyTime o input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime cls input (encList eLoss)) (hs : ComputableInPolyTime s input encBool) :
    ComputableInPolyTime (fun x => rowData (o x) (n x) (cls x) (s x)) input rowEncoding := by
  unfold rowData
  fun_prop

@[fun_prop] theorem pos_poly {d g i b : X → ℕ}
    (hd : ComputableInPolyTime d input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hi : ComputableInPolyTime i input encUnary) (hb : ComputableInPolyTime b input encUnary) :
    ComputableInPolyTime (fun x => pos (d x) (g x) (i x) (b x)) input encUnary := by unfold pos; fun_prop

@[fun_prop] theorem code_poly {d g j : X → ℕ}
    (hd : ComputableInPolyTime d input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => code (d x) (g x) (j x)) input namesEncoding := by
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hd)
  have digit : ComputableInPolyTime (fun p : X × ℕ => (j p.1).testBit p.2)
      (encPair input encUnary) encBool := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.binary_testBit ((ComputableInPolyTime.unary_to_binary.comp hj).comp
      (ComputableInPolyTime.fst input encUnary)).tidy (ComputableInPolyTime.snd input encUnary).tidy)
  fun_prop

@[fun_prop] theorem addresses_poly {h n m : X → ℕ}
    (hh : ComputableInPolyTime h input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun x => addresses (h x) (n x) (m x)) input (encList entryEncoding) := by
  have bits : ComputableInPolyTime (fun x => width (8 * (n x + m x + 1))) input encUnary := by
    have pre : ComputableInPolyTime (fun x => 8 * (n x + m x + 1) + 1) input encUnary := by fun_prop
    have log := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two).comp pre
    simp only [width, Nat.log2_eq_log_two]
    fun_prop
  unfold addresses
  apply ComputableInPolyTime.cons' ((ComputableInPolyTime.const 0).prod (code_poly bits (.const 12) (.const 0)))
  apply ComputableInPolyTime.cons' ((ComputableInPolyTime.const 1).prod (code_poly bits (.const 13) (.const 0)))
  apply ComputableInPolyTime.mapWithInput (labsT_poly hn hm)
  have e := ComputableInPolyTime.snd input eTup
  have orig := ComputableInPolyTime.fst input eTup
  exact (toBin_poly (nameT_poly e)).prod
    (code_poly (bits.comp orig) (trackT_poly (hh.comp orig) e) (serialT_poly e))

end KFOL.Complexity.AddressedIncidence
