module

public import KFOL.Reductions.PrenexReduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Pair
public import Complexity.Logics.Propositional.CNF.PolyTime
public import Complexity.Foundations.Data.List.Counting

/-! # The reduction to recognition runs in polynomial time

Every list program of the reduction is computed by a deterministic multitape
Turing machine in polynomial time. Inside the reduction numbers are counted
in unary. The last step rewrites every number of the output in binary.
-/

@[expose] public section

namespace KFOL.Recognition.Lists

open Turing.MultiTapeTM Cslib.Logic.PL Problems

/-! ### Encodings inside the reduction -/

/-- Triples. -/
abbrev eTup : Tup ↪ List Bool := encPair encUnary (encPair encUnary encUnary)

/-- Postings. -/
abbrev ePost : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary

/-- Losses, and lists of clauses over stages. -/
abbrev eLoss : List (ℕ × ℕ) ↪ List Bool := encList ePost

/-- Fixed inputs of rows. -/
abbrev eFix : List (ℕ × ℕ × ℕ) ↪ List Bool :=
  encList (encPair encUnary (encPair encUnary encUnary))

/-- Inputs with their losses. -/
abbrev eSrc : List (ℕ × List (List (ℕ × ℕ))) ↪ List Bool :=
  encList (encPair encUnary (encList eLoss))

/-- Guards. -/
abbrev eEnt : List ((ℕ × ℕ) × List (ℕ × ℕ)) ↪ List Bool :=
  encList (encPair (encPair encUnary encUnary) eLoss)

/-- Instances with numbers in unary. -/
abbrev eGuardU : GuardList ↪ List Bool := encPair (encList encUnary) eEnt

variable {γ : Type} {encIn : γ ↪ List Bool}

/-! ### Coded rows of a formula -/

@[fun_prop]
theorem nm_poly (side : ℕ) {t : γ → Tup} (ht : ComputableInPolyTime t encIn eTup) :
    ComputableInPolyTime (fun x => nm side (t x)) encIn encUnary := by
  unfold nm
  fun_prop

@[fun_prop]
theorem candV_poly {N : γ → ℕ} (hN : ComputableInPolyTime N encIn encUnary) :
    ComputableInPolyTime (fun x => candV (N x)) encIn (encList eTup) := by
  unfold candV
  fun_prop

@[fun_prop]
theorem candL_poly {N : γ → ℕ} (hN : ComputableInPolyTime N encIn encUnary) :
    ComputableInPolyTime (fun x => candL (N x)) encIn (encList eTup) := by
  unfold candL
  fun_prop

@[fun_prop]
theorem isRowB_poly {n m : γ → ℕ} {t : γ → Tup}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (ht : ComputableInPolyTime t encIn eTup) :
    ComputableInPolyTime (fun x => isRowB (n x) (m x) (t x)) encIn encBool := by
  unfold isRowB
  fun_prop

@[fun_prop]
theorem isLabB_poly {n m : γ → ℕ} {t : γ → Tup}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (ht : ComputableInPolyTime t encIn eTup) :
    ComputableInPolyTime (fun x => isLabB (n x) (m x) (t x)) encIn encBool := by
  unfold isLabB
  fun_prop

@[fun_prop]
theorem rowsT_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => rowsT (n x) (m x)) encIn (encList eTup) := by
  unfold rowsT
  fun_prop

@[fun_prop]
theorem labsT_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => labsT (n x) (m x)) encIn (encList eTup) := by
  unfold labsT
  fun_prop

@[fun_prop]
theorem exB_poly {n i : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => exB (n x) (i x)) encIn encBool := by
  unfold exB
  fun_prop

@[fun_prop]
theorem markT_poly {n : γ → ℕ} {t : γ → Tup}
    (hn : ComputableInPolyTime n encIn encUnary) (ht : ComputableInPolyTime t encIn eTup) :
    ComputableInPolyTime (fun x => markT (n x) (t x)) encIn eTup := by
  unfold markT
  fun_prop

@[fun_prop]
theorem tupEq_poly {s t : γ → Tup}
    (hs : ComputableInPolyTime s encIn eTup) (ht : ComputableInPolyTime t encIn eTup) :
    ComputableInPolyTime (fun x => tupEq (s x) (t x)) encIn encBool := by
  unfold tupEq
  fun_prop

@[fun_prop]
theorem inIB_poly {n : γ → ℕ} {cls : γ → List (List (ℕ × ℕ))} {z e : γ → Tup}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hcls : ComputableInPolyTime cls encIn (encList eLoss))
    (hz : ComputableInPolyTime z encIn eTup) (he : ComputableInPolyTime e encIn eTup) :
    ComputableInPolyTime (fun x => inIB (n x) (cls x) (z x) (e x)) encIn encBool := by
  unfold inIB
  fun_prop

@[fun_prop]
theorem inJB_poly {n : γ → ℕ} {z e : γ → Tup}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hz : ComputableInPolyTime z encIn eTup) (he : ComputableInPolyTime e encIn eTup) :
    ComputableInPolyTime (fun x => inJB (n x) (z x) (e x)) encIn encBool := by
  unfold inJB
  fun_prop

@[fun_prop]
theorem selN_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => selN (n x) (m x)) encIn (encList encUnary) := by
  unfold selN
  fun_prop

@[fun_prop]
theorem coN_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => coN (n x) (m x)) encIn (encList encUnary) := by
  unfold coN pad
  fun_prop

@[fun_prop]
theorem xN_poly {n m : γ → ℕ} {cls : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (hcls : ComputableInPolyTime cls encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => xN (n x) (m x) (cls x)) encIn (encList encUnary) := by
  unfold xN
  fun_prop

@[fun_prop]
theorem yN_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => yN (n x) (m x)) encIn (encList encUnary) := by
  unfold yN pad
  fun_prop

@[fun_prop]
theorem mkN_poly {n m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary) :
    ComputableInPolyTime (fun x => mkN (n x) (m x)) encIn eLoss := by
  unfold mkN
  fun_prop

@[fun_prop]
theorem fxN_poly (c1 c2 : ℕ) {n m : γ → ℕ} {cls : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (hcls : ComputableInPolyTime cls encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => fxN c1 c2 (n x) (m x) (cls x)) encIn eFix := by
  unfold fxN pad
  fun_prop

/-! ### Losses and guards -/

@[fun_prop]
theorem twoOf_poly {ms : γ → List ℕ} (hms : ComputableInPolyTime ms encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => twoOf (ms x)) encIn (encList encUnary) := by
  unfold twoOf
  fun_prop

@[fun_prop]
theorem lossCapN_poly (c0 : ℕ) {coN : γ → List ℕ}
    (hco : ComputableInPolyTime coN encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => lossCapN c0 (coN x)) encIn eLoss := by
  unfold lossCapN
  fun_prop

@[fun_prop]
theorem lossXN_poly (c2 : ℕ) {selN xN : γ → List ℕ}
    (hsel : ComputableInPolyTime selN encIn (encList encUnary))
    (hx : ComputableInPolyTime xN encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => lossXN c2 (selN x) (xN x)) encIn eLoss := by
  unfold lossXN
  fun_prop

@[fun_prop]
theorem lossYN_poly (c1 : ℕ) {selN yN : γ → List ℕ}
    (hsel : ComputableInPolyTime selN encIn (encList encUnary))
    (hy : ComputableInPolyTime yN encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => lossYN c1 (selN x) (yN x)) encIn eLoss := by
  unfold lossYN
  fun_prop

@[fun_prop]
theorem lossRowN_poly (c1 c2 : ℕ) {selN : γ → List ℕ} {fxN : γ → List (ℕ × ℕ × ℕ)}
    {z : γ → ℕ} (hsel : ComputableInPolyTime selN encIn (encList encUnary))
    (hfx : ComputableInPolyTime fxN encIn eFix) (hz : ComputableInPolyTime z encIn encUnary) :
    ComputableInPolyTime (fun x => lossRowN c1 c2 (selN x) (fxN x) (z x)) encIn eLoss := by
  unfold lossRowN
  fun_prop

@[fun_prop]
theorem sourcesN_poly (c0 c1 c2 : ℕ) {selN coN xN yN : γ → List ℕ} {mkN : γ → List (ℕ × ℕ)}
    {fxN : γ → List (ℕ × ℕ × ℕ)}
    (hsel : ComputableInPolyTime selN encIn (encList encUnary))
    (hco : ComputableInPolyTime coN encIn (encList encUnary))
    (hx : ComputableInPolyTime xN encIn (encList encUnary))
    (hy : ComputableInPolyTime yN encIn (encList encUnary))
    (hmk : ComputableInPolyTime mkN encIn eLoss) (hfx : ComputableInPolyTime fxN encIn eFix) :
    ComputableInPolyTime
      (fun x => sourcesN c0 c1 c2 (selN x) (coN x) (xN x) (yN x) (mkN x) (fxN x)) encIn eSrc := by
  unfold sourcesN
  fun_prop

@[fun_prop]
theorem sourcesOf_poly (c0 c1 c2 : ℕ) {n : γ → ℕ} {cls : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hcls : ComputableInPolyTime cls encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => sourcesOf c0 c1 c2 (n x) (cls x)) encIn eSrc := by
  unfold sourcesOf
  fun_prop

@[fun_prop]
theorem selections_poly {zs : γ → List (List (ℕ × ℕ))}
    (hzs : ComputableInPolyTime zs encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => selections (zs x)) encIn (encList eLoss) := by
  unfold selections pick0 pick1 pick2 pick3
  fun_prop

@[fun_prop]
theorem primesOf_poly {zs : γ → List (List (ℕ × ℕ))}
    (hzs : ComputableInPolyTime zs encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => primesOf (zs x)) encIn (encList eLoss) := by
  unfold primesOf subsetB
  fun_prop

@[fun_prop]
theorem entriesOf_poly (K : ℕ) {src : γ → List (ℕ × List (List (ℕ × ℕ)))}
    (hsrc : ComputableInPolyTime src encIn eSrc) :
    ComputableInPolyTime (fun x => entriesOf K (src x)) encIn eEnt := by
  unfold entriesOf
  fun_prop

@[fun_prop]
theorem instanceOf_poly (K c0 c1 c2 : ℕ) {n : γ → ℕ} {cls : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hcls : ComputableInPolyTime cls encIn (encList eLoss)) :
    ComputableInPolyTime (fun x => instanceOf K c0 c1 c2 (n x) (cls x)) encIn eGuardU := by
  unfold instanceOf
  fun_prop

/-! ### Reading the instance -/

@[fun_prop]
theorem roundVars_poly {ps : γ → List (ℕ × ℕ)}
    (hps : ComputableInPolyTime ps encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun x => QBF.roundVars (ps x)) encIn (encList encNat) := by
  unfold QBF.roundVars
  fun_prop

@[fun_prop]
theorem lastIdx_poly {xs : γ → List ℕ} {v : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => lastIdx (xs x) (v x)) encIn encUnary := by
  unfold lastIdx
  fun_prop

@[fun_prop]
theorem closedB_poly {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn (encList (encList (encPair encNat encBool)))) :
    ComputableInPolyTime (fun x => closedB (xs x) (ψ x)) encIn encBool := by
  unfold closedB
  fun_prop

@[fun_prop]
theorem clsOf_poly {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn (encList (encList (encPair encNat encBool)))) :
    ComputableInPolyTime (fun x => clsOf (xs x) (ψ x)) encIn (encList eLoss) := by
  unfold clsOf
  fun_prop

theorem reduce0_poly (K c0 c1 c2 : ℕ) :
    ComputableInPolyTime (reduce0 K c0 c1 c2)
      (encPair (encList (encPair encNat encNat)) (encList (encList (encPair encNat encBool))))
      eGuardU := by
  unfold reduce0
  fun_prop

/-! ### Binary output -/

/-- A number, to be written in binary. -/
def toBin (n : ℕ) : ℕ := n

@[fun_prop]
theorem toBin_poly {j : γ → ℕ} (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => toBin (j x)) encIn encNat :=
  ComputableInPolyTime.unary_to_binary.comp hj

/-- The same instance with every number to be written in binary. -/
def rebin (g : GuardList) : GuardList :=
  (g.1.map toBin,
    g.2.map fun e => ((toBin e.1.1, toBin e.1.2), e.2.map fun q => (toBin q.1, toBin q.2)))

theorem rebin_eq (g : GuardList) : rebin g = g := by
  have h : toBin = id := rfl
  simp [rebin, h]

theorem rebin_poly : ComputableInPolyTime rebin eGuardU guardListEncoding := by
  unfold rebin
  fun_prop

/-- **The reduction is polynomial-time**, from instances with variables in
binary to instances with names and owners in binary. -/
theorem reduce_poly (K c0 c1 c2 : ℕ) :
    ComputableInPolyTime (fun x => rebin (reduce0 K c0 c1 c2 x))
      Cslib.Complexity.encPrenexCNF guardListEncoding :=
  rebin_poly.comp (reduce0_poly K c0 c1 c2)

end KFOL.Recognition.Lists

namespace KFOL.Recognition.Lists

open Turing.MultiTapeTM Cslib.Logic.PL Problems

/-- The reduction from true closed prenex formulas to normal forms of core
term operations with `K` owners. -/
def reduce {K : ℕ} (three : Fin 3 ↪ Fin K) (x : List (ℕ × ℕ) × CNF ℕ) : GuardList :=
  rebin (reduce0 K (three 0).val (three 1).val (three 2).val x)

/-- **Prenex truth reduces to recognition.** A deterministic multitape Turing
machine maps, in polynomial time, every list of rounds and matrix to a list
of guards that is the normal form of a core term operation exactly when the
formula is closed and true. -/
theorem TQBFCNF_reducible {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PolyTimeReducible Cslib.Complexity.encPrenexCNF guardListEncoding
      Cslib.Complexity.TQBFCNF (coreNormalForms three) :=
  ⟨reduce three, reduce_poly K _ _ _, fun x => by
    rw [reduce, rebin_eq]
    exact (reduce0_mem_iff three x).symm⟩

/-- **Recognition from the normal form is hard for polynomial space.** -/
theorem coreNormalForms_pspaceHard {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PSPACEHard guardListEncoding (coreNormalForms three) :=
  Cslib.Complexity.TQBFCNF_pspaceHard.trans (TQBFCNF_reducible three)

end KFOL.Recognition.Lists
