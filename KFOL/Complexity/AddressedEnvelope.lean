module

public import KFOL.Complexity.FullSparseEvaluation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-! # A polynomial-time machine for an addressed group entry

Names and roles are listed binary natural numbers. Each loss gives its
marked name and the names posted at the group owner. The endpoint is
another list of names. The input menu at each name is a list of roles.
List lengths, rather than the magnitudes of names, bound the loop.
-/

@[expose] public section
namespace KFOL.Complexity.AddressedEnvelope

open Turing.MultiTapeTM ComputableInPolyTime

abbrev Names := List ℕ
abbrev Rule := Names × Names
abbrev Entry := ℕ × Names
abbrev Roles := ℕ × ℕ
abbrev RowData := Names × List Entry
abbrev Data := RowData × List Entry
abbrev Input := Roles × Data

abbrev namesEncoding := encList encNat
abbrev ruleEncoding := encPair namesEncoding namesEncoding
abbrev entryEncoding := encPair encNat namesEncoding
abbrev rolesEncoding := encPair encNat encNat
abbrev rowEncoding := encPair namesEncoding (encList entryEncoding)
abbrev dataEncoding := encPair rowEncoding (encList entryEncoding)
abbrev inputEncoding := encPair rolesEncoding dataEncoding

def member (j : ℕ) (xs : Names) : Bool := xs.any (fun i => decide (j = i))

@[simp] theorem member_iff (j : ℕ) (xs : Names) : member j xs = true ↔ j ∈ xs := by
  simp [member, List.any_eq_true]

theorem member_polyTime : ComputableInPolyTime (fun p : ℕ × Names => member p.1 p.2)
    entryEncoding encBool := by
  apply anyWithInput (test := fun (p : ℕ × Names) j => decide (p.1 = j)) (snd _ _)
  apply decide_eq' <;> fun_prop

def overlaps (a b : Names) : Bool := a.any fun i => member i b

@[simp] theorem overlaps_iff (a b : Names) : overlaps a b = true ↔ ∃ j ∈ a, j ∈ b := by
  simp [overlaps, List.any_eq_true]

theorem overlaps_polyTime : ComputableInPolyTime (fun p : Rule => overlaps p.1 p.2)
    ruleEncoding encBool := by
  apply anyWithInput (test := fun (p : Rule) i => member i p.2) (fst _ _)
  exact member_polyTime.comp ((snd _ _).prod (by fun_prop))

/-- A rule drops its violating inputs when no relieving input remains. -/
def sweep (rules : List Rule) (pool : Names) : Names :=
  pool.filter fun i => rules.all (fun row => !member i row.1 || overlaps row.2 pool)

theorem sweep_polyTime : ComputableInPolyTime (fun p : List Rule × Names => sweep p.1 p.2)
    (encPair (encList ruleEncoding) namesEncoding) namesEncoding := by
  let stateCode := encPair (encList ruleEncoding) namesEncoding
  let indexedCode := encPair stateCode encNat
  let tripleCode := encPair indexedCode ruleEncoding
  have hname : ComputableInPolyTime (fun p : ((List Rule × Names) × ℕ) × Rule => p.1.2)
      tripleCode encNat := by fun_prop
  have hbad : ComputableInPolyTime (fun p : ((List Rule × Names) × ℕ) × Rule => p.2.1)
      tripleCode namesEncoding := by fun_prop
  have hrelief : ComputableInPolyTime (fun p : ((List Rule × Names) × ℕ) × Rule => p.2.2)
      tripleCode namesEncoding := by fun_prop
  have hpool : ComputableInPolyTime (fun p : ((List Rule × Names) × ℕ) × Rule => p.1.1.2)
      tripleCode namesEncoding := by fun_prop
  have test := bool_or.comp ((bool_not.comp (member_polyTime.comp (hname.prod hbad))).prod
    (overlaps_polyTime.comp (hrelief.prod hpool)))
  have pass := allWithInput (test := fun (p : (List Rule × Names) × ℕ) (row : Rule) =>
    !member p.2 row.1 || overlaps row.2 p.1.2) (by fun_prop :
      ComputableInPolyTime (fun p : (List Rule × Names) × ℕ => p.1.1) indexedCode (encList ruleEncoding)) test
  exact filterWithInput (test := fun (p : List Rule × Names) i =>
    p.1.all (fun row => !member i row.1 || overlaps row.2 p.2)) (snd _ _) pass

private theorem filter_storage (test : ℕ → Bool) (pool : Names) :
    (namesEncoding (pool.filter test)).length ≤ (namesEncoding pool).length := by
  induction pool with
  | nil => rfl
  | cons i tail ih =>
    simp only [List.filter_cons]
    split <;> simp only [namesEncoding, encList_cons, List.length_append] at * <;> omega

def survivors (rules : List Rule) (pool : Names) : Names := (sweep rules)^[pool.length] pool

theorem survivors_polyTime : ComputableInPolyTime (fun p : List Rule × Names => survivors p.1 p.2)
    (encPair (encList ruleEncoding) namesEncoding) namesEncoding := by
  apply ComputableInPolyTime.iterateWith_of_bounded_growth (fst _ _)
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length encNat)).comp (snd _ _))
    (snd _ _) sweep_polyTime (PolyBounded.const 0)
  intro _ _
  exact (filter_storage _ _).trans (Nat.le_add_right _ _)

/-- Encode the endpoint and then each monochromatic loss as a rule. -/
def rules (data : Data) : List Rule :=
  (((data.2.map Prod.fst).filter fun i => !member i data.1.1), data.1.1) ::
    data.1.2.map (fun p => ([p.1], p.2))

theorem rules_polyTime : ComputableInPolyTime rules dataEncoding (encList ruleEncoding) := by
  have hMenus := snd rowEncoding (encList entryEncoding)
  have hNames := (ComputableInPolyTime.map (fst encNat namesEncoding)).comp hMenus
  have hEnd : ComputableInPolyTime (fun d : Data => d.1.1) dataEncoding namesEncoding := by fun_prop
  have hbad := filterWithInput (test := fun (d : Data) i => !member i d.1.1) hNames
    (bool_not.comp (member_polyTime.comp ((snd _ _).prod (hEnd.comp (fst dataEncoding encNat)))))
  have record := (cons' (fst encNat namesEncoding) (const [])).prod (snd encNat namesEncoding)
  have hLosses : ComputableInPolyTime (fun d : Data => d.1.2) dataEncoding (encList entryEncoding) := by fun_prop
  exact cons' (hbad.prod hEnd) ((ComputableInPolyTime.map record).comp hLosses)

def eligible (roles : Roles) (value : Names) : Bool :=
  decide (roles.1 = roles.2) || !FullSparseEvaluation.singletonB roles.1 value

def pool (p : Input) : Names := ((p.2.2.filter fun v => eligible p.1 v.2).map Prod.fst)

def sources (p : Input) : Names := ((p.2.2.filter fun v => member p.1.2 v.2).map Prod.fst)

theorem pool_polyTime : ComputableInPolyTime pool inputEncoding namesEncoding := by
  let code := encPair inputEncoding entryEncoding
  have hr : ComputableInPolyTime (fun p : Input × Entry => p.1.1.1) code encNat := by fun_prop
  have hk : ComputableInPolyTime (fun p : Input × Entry => p.1.1.2) code encNat := by fun_prop
  have hm : ComputableInPolyTime (fun p : Input × Entry => p.2.2) code namesEncoding := by fun_prop
  have test := bool_or.comp ((decide_eq' hr hk).prod
    (bool_not.comp (FullSparseEvaluation.singleton_polyTime.comp (hr.prod hm))))
  have menu : ComputableInPolyTime (fun p : Input => p.2.2) inputEncoding (encList entryEncoding) := by fun_prop
  exact (ComputableInPolyTime.map (fst encNat namesEncoding)).comp
    (filterWithInput (test := fun (p : Input) (entry : Entry) => eligible p.1 entry.2) menu test)

theorem sources_polyTime : ComputableInPolyTime sources inputEncoding namesEncoding := by
  let code := encPair inputEncoding entryEncoding
  have hk : ComputableInPolyTime (fun p : Input × Entry => p.1.1.2) code encNat := by fun_prop
  have hm : ComputableInPolyTime (fun p : Input × Entry => p.2.2) code namesEncoding := by fun_prop
  have menu : ComputableInPolyTime (fun p : Input => p.2.2) inputEncoding (encList entryEncoding) := by fun_prop
  exact (ComputableInPolyTime.map (fst encNat namesEncoding)).comp
    (filterWithInput (test := fun (p : Input) (entry : Entry) => member p.1.2 entry.2) menu
      (member_polyTime.comp (hk.prod hm)))

/-- Decide one winner in the greatest group. This is a total machine,
including on duplicate or otherwise unvalidated names. -/
def evaluate (p : Input) : Bool := overlaps (survivors (rules p.2) (pool p)) (sources p)

@[fun_prop] theorem evaluate_polyTime : ComputableInPolyTime evaluate inputEncoding encBool :=
  overlaps_polyTime.comp ((survivors_polyTime.comp
    ((rules_polyTime.comp (snd _ _)).prod pool_polyTime)).prod sources_polyTime)

end KFOL.Complexity.AddressedEnvelope
