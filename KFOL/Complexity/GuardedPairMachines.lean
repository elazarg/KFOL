module
public import KFOL.Complexity.FiniteTermDecoding
public import KFOL.Complexity.ResetUnionReduction
public import KFOL.Reductions.GuardedPair
@[expose] public section
namespace KFOL.Complexity.GuardedPairMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
open KFOL.Reductions

def operationEquiv : Operation KFOL.GuardedPair.Symbol ≃ Bool where
  toFun operation := match operation with | ⟨_, .guarded sign⟩ => sign
  invFun sign := ⟨3, .guarded sign⟩
  left_inv operation := by cases operation with | mk n symbol => cases symbol; rfl
  right_inv _ := rfl

noncomputable instance operationFintype : Fintype (Operation KFOL.GuardedPair.Symbol) :=
  Fintype.ofEquiv Bool operationEquiv.symm

abbrev Tree := KFOL.GuardedPair.Term ℕ
noncomputable abbrev termEncoding := FiniteTermMachines.termEncoding (σ := KFOL.GuardedPair.Symbol)
noncomputable abbrev equationEncoding := FiniteTermMachines.equationEncoding (σ := KFOL.GuardedPair.Symbol)
abbrev literalEncoding := ResetUnionReduction.literalEncoding
abbrev clauseEncoding := ResetUnionReduction.clauseEncoding
abbrev cnfEncoding := ResetUnionReduction.cnfEncoding

theorem var_polyTime : ComputableInPolyTime (fun j : ℕ => (.var j : Tree)) encNat termEncoding :=
  FiniteTermMachines.var_polyTime

theorem guarded_polyTime : ComputableInPolyTime
    (fun p : Bool × (Tree × (Tree × Tree)) => KFOL.GuardedPair.Term.guarded p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encBool (encPair termEncoding (encPair termEncoding termEncoding))) termEncoding := by
  let input := encPair encBool (encPair termEncoding (encPair termEncoding termEncoding))
  have hs := fst encBool (encPair termEncoding (encPair termEncoding termEncoding))
  have hx : ComputableInPolyTime (fun p : Bool × (Tree × (Tree × Tree)) => p.2.1) input termEncoding := by fun_prop
  have hy : ComputableInPolyTime (fun p : Bool × (Tree × (Tree × Tree)) => p.2.2.1) input termEncoding := by fun_prop
  have hz : ComputableInPolyTime (fun p : Bool × (Tree × (Tree × Tree)) => p.2.2.2) input termEncoding := by fun_prop
  have hop := (ComputableInPolyTime.of_finite (fun sign : Bool =>
      (⟨3, KFOL.GuardedPair.Symbol.guarded sign⟩ : Operation KFOL.GuardedPair.Symbol))
      (encIn := encBool) (encOut := FiniteTermMachines.operationEncoding)).comp hs
  have h := FiniteTermMachines.construct_polyTime.comp (hop.prod (cons' hx (cons' hy (cons' hz (const [])))))
  convert h using 1
  funext p
  unfold KFOL.GuardedPair.Term.guarded FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp

noncomputable def header (sign : Bool) : ℕ :=
  1 + (Words.delimit (encodeOperation KFOL.GuardedPair.Symbol ⟨3, .guarded sign⟩)).length
noncomputable def headerBound : ℕ := max (header false) (header true)

private theorem header_le (sign : Bool) : header sign ≤ headerBound := by
  cases sign
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

theorem guarded_length (sign : Bool) (x y z : Tree) :
    (termEncoding (KFOL.GuardedPair.Term.guarded sign x y z)).length =
      (termEncoding x).length + (termEncoding y).length + (termEncoding z).length + header sign := by
  simp [termEncoding, FiniteTermMachines.termEncoding, KFOL.GuardedPair.Term.guarded,
    encode_func, List.ofFn_succ, header, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem reset_polyTime : ComputableInPolyTime
    (fun p : Tree × Tree => KFOL.GuardedPair.Term.reset p.1 p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have hs := fst termEncoding termEncoding
  have ht := snd termEncoding termEncoding
  exact guarded_polyTime.comp ((const true).prod (ht.prod (hs.prod hs)))

theorem rightComb_polyTime : ComputableInPolyTime
    (fun p : List Tree × Tree => KFOL.GuardedPair.Term.rightComb p.1 p.2)
    (encPair (encList termEncoding) termEncoding) termEncoding := by
  let input := encPair (encList termEncoding) termEncoding
  have hl := fst (encList termEncoding) termEncoding
  have hr := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse termEncoding)).comp hl
  have hs : ComputableInPolyTime (fun p : ((List Tree × Tree) × Tree) × Tree => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input termEncoding) termEncoding
  have hstep := reset_polyTime.comp (ht.prod hs)
  have hg := ((PolyBounded.const 2).mul hl.polyBounded_length).add (PolyBounded.const (header true))
  have h := foldlWithInput_of_bounded_growth
    (list := fun p : List Tree × Tree => p.1.reverse) (init := fun p => p.2)
    (step := fun _ state term => KFOL.GuardedPair.Term.reset term state)
    (snd (encList termEncoding) termEncoding) ⟨hr, hstep, inferInstance, inferInstance⟩
    (growth := fun p => 2 * (encList termEncoding p.1).length + header true)
    ⟨hg, ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse]
    rfl
  · intro p state term hterm
    have ht := SizedListEncoding.length_elem_le (encA := termEncoding)
      (encL := encList termEncoding) p.1 term (List.mem_reverse.mp hterm)
    have hl := guarded_length true state term term
    change (termEncoding (KFOL.GuardedPair.Term.guarded true state term term)).length ≤ _
    omega

theorem booleanName_polyTime : ComputableInPolyTime GuardedPair.booleanName encNat encNat :=
  binary_add.comp ((id' (encIn := encNat)).prod (const 2))

private theorem booleanTerm_polyTime : ComputableInPolyTime
    (fun literal : Literal => (.var (GuardedPair.booleanName literal.1) : Tree)) literalEncoding termEncoding :=
  var_polyTime.comp (booleanName_polyTime.comp (fst encNat encBool))

private theorem clause_fold (clause : Clause) :
    GuardedPair.clause clause = clause.foldr
      (fun literal continuation => KFOL.GuardedPair.Term.guarded literal.2 (.var 0)
        (.var (GuardedPair.booleanName literal.1)) continuation) (.var 1) := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [GuardedPair.clause, List.foldr_cons, ih]

theorem clause_polyTime : ComputableInPolyTime GuardedPair.clause clauseEncoding termEncoding := by
  have hvalues := mapWithInput (f := fun (_ : Clause) (literal : Literal) =>
    (.var (GuardedPair.booleanName literal.1) : Tree)) (id' (encIn := clauseEncoding))
    (booleanTerm_polyTime.comp (snd clauseEncoding literalEncoding))
  have hr := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse literalEncoding)
  let input := encPair (encPair clauseEncoding termEncoding) literalEncoding
  have hsign : ComputableInPolyTime (fun p : (Clause × Tree) × Literal => p.2.2) input encBool := by fun_prop
  have hvalue := booleanTerm_polyTime.comp (snd (encPair clauseEncoding termEncoding) literalEncoding)
  have hstate : ComputableInPolyTime (fun p : (Clause × Tree) × Literal => p.1.2) input termEncoding := by fun_prop
  have hstep := guarded_polyTime.comp (hsign.prod ((const (.var 0 : Tree)).prod (hvalue.prod hstate)))
  have hg := (hvalues.polyBounded_length.add (PolyBounded.const ((termEncoding (.var 0 : Tree)).length))).add
    (PolyBounded.const headerBound)
  have h := foldlWithInput_of_bounded_growth (list := List.reverse) (init := fun (_ : Clause) => (.var 1 : Tree))
    (step := fun _ state literal => KFOL.GuardedPair.Term.guarded literal.2 (.var 0)
      (.var (GuardedPair.booleanName literal.1)) state)
    (const (.var 1 : Tree)) ⟨hr, hstep, inferInstance, inferInstance⟩
    (growth := fun clause => (encList termEncoding
      (clause.map (fun literal => (.var (GuardedPair.booleanName literal.1) : Tree)))).length +
      (termEncoding (.var 0 : Tree)).length + headerBound)
    ⟨hg, ?_⟩
  · convert h using 1
    funext clause
    rw [List.foldl_reverse, clause_fold]
  · intro clause state literal hliteral
    have hm : (.var (GuardedPair.booleanName literal.1) : Tree) ∈
        clause.map (fun literal => (.var (GuardedPair.booleanName literal.1) : Tree)) :=
      List.mem_map.mpr ⟨literal, List.mem_reverse.mp hliteral, rfl⟩
    have hb := SizedListEncoding.length_elem_le (encA := termEncoding) (encL := encList termEncoding) _ _ hm
    have hs := guarded_length literal.2 (.var 0) (.var (GuardedPair.booleanName literal.1)) state
    have hh := header_le literal.2
    omega

theorem baseline_polyTime : ComputableInPolyTime GuardedPair.baseline cnfEncoding termEncoding := by
  have ht := (var_polyTime.comp booleanName_polyTime).comp (snd cnfEncoding encNat)
  have hvars := mapWithInput (f := fun (_ : CNF) j => (.var (GuardedPair.booleanName j) : Tree))
    ResetUnionReduction.support_polyTime ht
  exact rightComb_polyTime.comp (hvars.prod (const (.var 0 : Tree)))

theorem right_polyTime : ComputableInPolyTime GuardedPair.right cnfEncoding termEncoding := by
  have hclauses := mapWithInput (f := fun (_ : CNF) clause => GuardedPair.clause clause)
    (id' (encIn := cnfEncoding)) (clause_polyTime.comp (snd cnfEncoding clauseEncoding))
  exact rightComb_polyTime.comp (hclauses.prod baseline_polyTime)

theorem reduction_polyTime : ComputableInPolyTime GuardedPair.equation cnfEncoding equationEncoding := by
  have hl := reset_polyTime.comp ((const (.var 1 : Tree)).prod right_polyTime)
  exact FiniteTermMachines.equationRecode_polyTime.comp (hl.prod right_polyTime)

end KFOL.Complexity.GuardedPairMachines
