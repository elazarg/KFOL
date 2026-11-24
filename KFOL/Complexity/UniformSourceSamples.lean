module

public import KFOL.Complexity.AddressedSourceCorrectness
public import KFOL.Complexity.TablePeelingUniformMasks

/-! # Uniform source probes as an exact listed interpolation sample

The two unary parameters are the number of roles and the arity. For every
given source bit the certificate supplies all winners of the operation at
that probe. Only the observer's winner bit is prescribed by the input.
The resulting rows have polynomial total width also when K varies.
-/

@[expose] public section
namespace KFOL.Complexity.UniformSourceSamples

open Turing.MultiTapeTM ComputableInPolyTime AddressedSourceOutput AddressTableOutput
open AddressedEnvelope

abbrev Input := ℕ × (ℕ × List Bool)
abbrev Proof := Input × List Bool
abbrev sourceEncoding := encPair encUnary (encPair encUnary encBits)
abbrev proofEncoding := encPair sourceEncoding encBits

def block (x : Input) := min (x.1^x.2.1) x.2.2.length
def head (x : Input) (t : ℕ) := t / block x
def signature (x : Input) (t : ℕ) := t % block x
def observer (x : Input) (t : ℕ) := digit x.1 (signature x t) (head x t)

def inputMenu (x : Input) (t j : ℕ) : Names :=
  (List.range x.1).filter fun r =>
    probeFlag (observer x t) (digit x.1 (signature x t) j) r (decide (j = head x t))

def outputMenu (p : Proof) (t : ℕ) : Names :=
  (List.range p.1.1).filter fun r => p.2.getD (t*p.1.1+r) false

def samples (p : Proof) : TablePeeling.Input :=
  (p.1.2.1, (List.range p.1.2.2.length).map fun t =>
    ((List.range p.1.2.1).map (inputMenu p.1 t), outputMenu p t))

def consistent (p : Proof) : Bool :=
  decide (p.1.2.2.length = p.1.2.1*p.1.1^p.1.2.1) &&
    (List.range p.1.2.2.length).all (fun t => decide
      (p.1.2.2.getD t false = p.2.getD (t*p.1.1+observer p.1 t) false))

def width (x : Input) : ℕ := x.1*x.2.2.length

variable {X : Type} {e : X ↪ List Bool}

theorem width_poly : ComputableInPolyTime width sourceEncoding encUnary :=
  unary_mul' (fst _ _) (length_bits.comp ((snd _ _).comp (snd _ _)))

private theorem block_poly {x : X → Input} (hx : ComputableInPolyTime x e sourceEncoding) :
    ComputableInPolyTime (fun a => block (x a)) e encUnary := by
  have pow := binary_pow' (unary_to_binary.comp hx.fst') hx.snd'.fst'
  have len := length_bits.comp hx.snd'.snd'
  apply (binary_min_unary' len pow).of_enc_eq
  intro _
  simp only [block,Function.comp_apply]
  rw [Nat.min_comm]

private theorem digit_poly {k t j : X → ℕ} (hk : ComputableInPolyTime k e encUnary)
    (ht : ComputableInPolyTime t e encUnary) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun a => digit (k a) (t a) (j a)) e encNat := by
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_div'
    (ComputableTidilyInPolyTime.unary_to_binary.comp ht.tidy)
    (ComputableTidilyInPolyTime.binary_pow' (unary_to_binary.comp hk).tidy hj.tidy)) (unary_to_binary.comp hk).tidy)

private theorem head_poly {x : X → Input} {t : X → ℕ} (hx : ComputableInPolyTime x e sourceEncoding)
    (ht : ComputableInPolyTime t e encUnary) :
    ComputableInPolyTime (fun a => head (x a) (t a)) e encUnary := unary_div.comp (ht.prod (block_poly hx))

private theorem sig_poly {x : X → Input} {t : X → ℕ} (hx : ComputableInPolyTime x e sourceEncoding)
    (ht : ComputableInPolyTime t e encUnary) :
    ComputableInPolyTime (fun a => signature (x a) (t a)) e encUnary := unary_mod.comp (ht.prod (block_poly hx))

private theorem obs_poly {x : X → Input} {t : X → ℕ} (hx : ComputableInPolyTime x e sourceEncoding)
    (ht : ComputableInPolyTime t e encUnary) :
    ComputableInPolyTime (fun a => observer (x a) (t a)) e encNat :=
  digit_poly hx.fst' (sig_poly hx ht) (head_poly hx ht)

private theorem probeFlag_poly {r j v : X → ℕ} {h : X → Bool}
    (hr : ComputableInPolyTime r e encNat) (hj : ComputableInPolyTime j e encNat)
    (hv : ComputableInPolyTime v e encNat) (hh : ComputableInPolyTime h e encBool) :
    ComputableInPolyTime (fun a => probeFlag (r a) (j a) (v a) (h a)) e encBool := by
  have test := bool_or.comp (hh.prod (bool_not.comp (decide_eq' hj hr)))
  simpa only [probeFlag, Function.comp_apply, decide_not] using
    test.ite (decide_eq' hv hj) (bool_not.comp (decide_eq' hv hr))

private theorem inputMenu_poly {x : X → Input} {t j : X → ℕ} (hx : ComputableInPolyTime x e sourceEncoding)
    (ht : ComputableInPolyTime t e encUnary) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun a => inputMenu (x a) (t a) (j a)) e namesEncoding := by
  let pre := fst e encNat
  have s := sig_poly hx ht
  have o := obs_poly hx ht
  have h := head_poly hx ht
  apply filterWithInput (TablePeelingUniform.rangeBinary_poly hx.fst')
  exact probeFlag_poly (o.comp pre) ((digit_poly hx.fst' s hj).comp pre) (snd e encNat) ((decide_eq' hj h).comp pre)

private theorem binary_names {names : X → Names} (h : ComputableInPolyTime names e (encList encUnary)) :
    ComputableInPolyTime names e namesEncoding := by
  have named : ComputableInPolyTime (fun s : List ℕ => s) (encList encUnary) namesEncoding := by
    rw [show (fun s : List ℕ => s) = List.map (fun i : ℕ => i) by funext s; exact (List.map_id' s).symm]
    exact ComputableInPolyTime.map unary_to_binary
  exact named.comp h

private theorem outputMenu_poly {p : X → Proof} {t : X → ℕ} (hp : ComputableInPolyTime p e proofEncoding)
    (ht : ComputableInPolyTime t e encUnary) :
    ComputableInPolyTime (fun a => outputMenu (p a) (t a)) e namesEncoding := by
  apply binary_names
  apply filterWithInput (ComputableInPolyTime.range.comp hp.fst'.fst')
  let pre := fst e encUnary
  exact bitsGetDWithInput (hp.snd'.comp pre)
    (unary_add' ((unary_mul' ht hp.fst'.fst').comp pre) (snd e encUnary)) false

theorem samples_poly : ComputableInPolyTime samples proofEncoding TablePeeling.inputEncoding := by
  let x := fst sourceEncoding encBits
  let indexed := encPair proofEncoding encUnary
  let pre := fst proofEncoding encUnary
  let pre' := fst indexed encUnary
  let t := snd proofEncoding encUnary
  have menus := mapWithInput (f := fun (p : Proof × ℕ) j => inputMenu p.1.1 p.2 j)
    (ComputableInPolyTime.range.comp (x.snd'.fst'.comp pre))
    (inputMenu_poly ((x.comp pre).comp pre') (t.comp pre') (snd indexed encUnary))
  exact x.snd'.fst'.prod (mapWithInput (f := fun (p : Proof) t =>
    ((List.range p.1.2.1).map (inputMenu p.1 t), outputMenu p t))
    (ComputableInPolyTime.range.comp (length_bits.comp x.snd'.snd'))
    (menus.prod (outputMenu_poly pre t)))

theorem consistent_poly : ComputableInPolyTime consistent proofEncoding encBool := by
  let x := fst sourceEncoding encBits
  let w := snd sourceEncoding encBits
  let pre := fst proofEncoding encUnary
  let t := snd proofEncoding encUnary
  have len := length_bits.comp x.snd'.snd'
  have pow := binary_pow' (unary_to_binary.comp x.fst') x.snd'.fst'
  have shape := decide_eq' (unary_to_binary.comp len) (binary_mul' (unary_to_binary.comp x.snd'.fst') pow)
  have atObs := binary_add.comp ((unary_to_binary.comp (unary_mul' t (x.fst'.comp pre))).prod (obs_poly (x.comp pre) t))
  have read := ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
    ((w.comp pre).tidy) atObs.tidy
  have equal := decide_eq' (bitsGetDWithInput (x.snd'.snd'.comp pre) t false) (ComputableInPolyTime.of_tidy read)
  exact bool_and' shape (allWithInput (test := fun (p : Proof) t => decide
      (p.1.2.2.getD t false = p.2.getD (t*p.1.1+observer p.1 t) false))
    (ComputableInPolyTime.range.comp len) equal)

theorem consistent_iff (p : Proof) : consistent p = true ↔
    p.1.2.2.length = p.1.2.1*p.1.1^p.1.2.1 ∧ ∀ t < p.1.2.2.length,
      p.1.2.2.getD t false = p.2.getD (t*p.1.1+observer p.1 t) false := by
  simp only [consistent,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range]

end KFOL.Complexity.UniformSourceSamples
