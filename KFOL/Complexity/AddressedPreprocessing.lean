module

public import KFOL.Core.QuantifiedThreeCNF
public import KFOL.Complexity.RecognitionHardness
public import Complexity.Logics.Propositional.CNF.ThreeCNF.PolyTime

/-! # Computing the three-slot quantified formula from an encoded input

Stage numbers are unary. The original variable names are read in binary, and
references to a name use its last binding in the prefix.
-/

@[expose] public section
namespace KFOL.Complexity.AddressedPreprocessing

open Turing.MultiTapeTM Cslib.Logic.PL Bichain.Quantified Recognition.Lists

abbrev Input := List (ℕ × ℕ) × CNF ℕ
abbrev matrixEncoding {α : Type} (e : α ↪ List Bool) := encList (encList (encPair e encBool))
abbrev tagEncoding := encSum encUnary (encPair encUnary encUnary)

private theorem base_stages : ComputableInPolyTime (fun u : Input => (formulaOf u).n)
    Cslib.Complexity.encPrenexCNF encUnary := by
  unfold formulaOf Cslib.Complexity.encPrenexCNF
  simp only [apply_ite]
  fun_prop

private theorem base_matrix : ComputableInPolyTime (fun u : Input => (formulaOf u).cls)
    Cslib.Complexity.encPrenexCNF (matrixEncoding encUnary) := by
  unfold formulaOf Cslib.Complexity.encPrenexCNF
  simp only [apply_ite]
  fun_prop

private theorem split_matrix : ComputableInPolyTime (fun u : Input => ThreeCNF.split (formulaOf u))
    Cslib.Complexity.encPrenexCNF (matrixEncoding tagEncoding) := by
  unfold ThreeCNF.split
  have := base_matrix
  fun_prop

open ComputableInPolyTime

private theorem names_poly : ComputableInPolyTime
    (fun u : Input => (ThreeCNF.split (formulaOf u)).vars)
    Cslib.Complexity.encPrenexCNF (encList tagEncoding) := by
  have := split_matrix
  fun_prop

private theorem name_poly : ComputableInPolyTime
    (fun p : Input × ThreeCNF.Tag => ThreeCNF.name (formulaOf p.1) p.2)
    (encPair Cslib.Complexity.encPrenexCNF tagEncoding) encUnary := by
  let e := Cslib.Complexity.encPrenexCNF
  have hc : ComputableInPolyTime (fun s : ThreeCNF.Tag => tagEncoding s) tagEncoding encBits :=
    .of_eq (fun _ => rfl)
  have hcode := hc.comp (snd e tagEncoding)
  have hstage := base_stages.comp (fst e tagEncoding)
  have hnames := names_poly.comp (fst e tagEncoding)
  have hindex : ComputableInPolyTime
      (fun p : Input × ThreeCNF.Tag => (ThreeCNF.split (formulaOf p.1)).vars.idxOf p.2)
      (encPair e tagEncoding) encUnary := by
    apply (idxOfWithInput hnames (snd e tagEncoding)).of_enc_eq
    intro p
    congr 1
    unfold List.idxOf
    congr 1
    funext a
    apply Bool.eq_iff_iff.mpr
    simp
  have hlen := length_bits.comp hcode
  have hhead := (headD (encA := encBool) (encL := encBits) false).comp hcode
  let read (p : Input × ThreeCNF.Tag) :=
    let j := (tagEncoding p.2).length - 1
    let n := (formulaOf p.1).n
    if (tagEncoding p.2).headD false then n+2+(ThreeCNF.split (formulaOf p.1)).vars.idxOf p.2
    else if 1 ≤ j then (if j ≤ n then j else n+1) else n+1
  have fast : ComputableInPolyTime read (encPair e tagEncoding) encUnary := by
    have digit := unary_sub' hlen (const 1)
    have spare := unary_add' hstage (const 1)
    have aux := unary_add' (unary_add' hstage (const 2)) hindex
    have alt := (unary_le' (const 1) digit).ite ((unary_le' digit hstage).ite digit spare) spare
    simpa only [read, Function.comp_apply, decide_eq_true_eq] using hhead.ite aux alt
  apply fast.of_enc_eq
  rintro ⟨u, j | p⟩
  · simp [read, ThreeCNF.name, tagEncoding]
    split_ifs <;> simp_all
  · simp [read, ThreeCNF.name, tagEncoding]

private theorem stage3_poly : ComputableInPolyTime
    (fun u : Input => (ThreeCNF.translate (formulaOf u)).n)
    Cslib.Complexity.encPrenexCNF encUnary := by
  have := base_stages
  have := names_poly
  change ComputableInPolyTime (fun u : Input =>
    (formulaOf u).n + (1 + (ThreeCNF.split (formulaOf u)).vars.length)) _ _
  fun_prop

private theorem matrix3_poly : ComputableInPolyTime
    (fun u : Input => (ThreeCNF.translate (formulaOf u)).cls)
    Cslib.Complexity.encPrenexCNF (matrixEncoding encUnary) := by
  have := name_poly
  have := split_matrix
  change ComputableInPolyTime
    (fun u : Input => CNF.relabel (ThreeCNF.name (formulaOf u)) (ThreeCNF.split (formulaOf u))) _ _
  unfold CNF.relabel Clause.relabel
  apply mapWithInput split_matrix
  apply mapWithInput (snd _ _)
  have ctx := fst (encPair Cslib.Complexity.encPrenexCNF (encList (encPair tagEncoding encBool)))
    (encPair tagEncoding encBool)
  have lit := snd (encPair Cslib.Complexity.encPrenexCNF (encList (encPair tagEncoding encBool)))
    (encPair tagEncoding encBool)
  exact (name_poly.comp (ctx.fst'.prod lit.fst')).prod lit.snd'

private theorem distribute_poly : ComputableInPolyTime
    (fun p : ℕ × Clause ℕ => ThreeSlot.distribute p.1 p.2)
    (encPair encUnary (encList (encPair encUnary encBool))) (encList (encPair encUnary encBool)) := by
  let f (p : ℕ × Clause ℕ) := p.2.take 1 ++
    ((p.2.drop 1).take 1).map (ThreeSlot.shift p.1) ++ (p.2.drop 2).map (ThreeSlot.shift (2*p.1))
  have poly : ComputableInPolyTime f (encPair encUnary (encList (encPair encUnary encBool)))
      (encList (encPair encUnary encBool)) := by
    unfold f ThreeSlot.shift
    fun_prop
  apply poly.of_enc_eq
  rintro ⟨n, _ | ⟨a, _ | ⟨b, rest⟩⟩⟩ <;> simp [f, ThreeSlot.distribute]

private theorem equalities_poly : ComputableInPolyTime
    (fun p : ℕ × ℕ => ThreeSlot.equalities p.1 p.2) (encPair encUnary encUnary)
      (matrixEncoding encUnary) := by
  unfold ThreeSlot.equalities
  have hi := fst encUnary encUnary
  have hj := snd encUnary encUnary
  have literal (j : ℕ × ℕ → ℕ) (h : ComputableInPolyTime j (encPair encUnary encUnary) encUnary)
      (b : Bool) := h.prod (const (encOut := encBool) b)
  have clause (positive : Bool) := (literal _ hi positive).cons'
    ((literal _ hj (!positive)).cons' (const []))
  exact (clause false).cons' ((clause true).cons' (const []))

private theorem links_poly : ComputableInPolyTime ThreeSlot.links encUnary (matrixEncoding encUnary) := by
  let one (p : ℕ × ℕ) := p.2+1
  have hone : ComputableInPolyTime one (encPair encUnary encUnary) encUnary :=
    unary_add' (snd _ _) (const 1)
  have hfirst := equalities_poly.comp (hone.prod (unary_add' (fst _ _) hone))
  have hsecond := equalities_poly.comp (hone.prod (unary_add' (unary_mul' (const 2) (fst _ _)) hone))
  unfold ThreeSlot.links
  exact flatMapWithInput (f := fun n k => ThreeSlot.equalities (k+1) (n+(k+1)) ++
    ThreeSlot.equalities (k+1) (2*n+(k+1))) range (listAppend' hfirst hsecond)

/-- The original quantifier stages, the split-formula stages, and the final three-slot stages. -/
theorem counts_poly : ComputableInPolyTime (fun u : Input =>
    ((formulaOf u).n, (ThreeCNF.translate (formulaOf u)).n, (ThreeCNF.fromTQBFCNF u).n))
    Cslib.Complexity.encPrenexCNF (encPair encUnary (encPair encUnary encUnary)) :=
  base_stages.prod (stage3_poly.prod (unary_mul' (const 3) stage3_poly))

theorem clauses_poly : ComputableInPolyTime (fun u : Input => (ThreeCNF.fromTQBFCNF u).cls)
    Cslib.Complexity.encPrenexCNF (matrixEncoding encUnary) := by
  change ComputableInPolyTime (fun u => ((ThreeCNF.translate (formulaOf u)).cls.map
    (ThreeSlot.distribute (ThreeCNF.translate (formulaOf u)).n)) ++
      ThreeSlot.links (ThreeCNF.translate (formulaOf u)).n) _ _
  have shifted := mapWithInput (f := fun u c => ThreeSlot.distribute (ThreeCNF.translate (formulaOf u)).n c) matrix3_poly (distribute_poly.comp
    ((stage3_poly.comp (fst _ _)).prod (snd _ _)))
  exact listAppend' shifted (links_poly.comp stage3_poly)

/-- Both literal fields in unary, the input of the incidence compiler. -/
theorem numeric_clauses_poly : ComputableInPolyTime (fun u : Input => numCls (ThreeCNF.fromTQBFCNF u))
    Cslib.Complexity.encPrenexCNF (encList eLoss) := by
  unfold numCls
  have h := clauses_poly
  fun_prop

end KFOL.Complexity.AddressedPreprocessing
