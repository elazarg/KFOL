module

public import KFOL.Core.AddressedRails
public import KFOL.Core.AddressedCubeCut

/-! # Physical observations for a rectangle of logical rows

One evaluation groups all marked rails of an address. Their common mark
is the owner opposite the primary posting. The other two atom fibers are
the primary posting and the available complementary rails of the address.
-/

@[expose] public section
namespace KFOL.Core.AddressedRectangle

open AddressedRails ProfileBudgets Bichain
attribute [local instance] Equational.coreStructure

variable {Role RailType Label Track Bit Row : Type*} [DecidableEq Role]

/-- Switch the primary and observed owner for a right-side row. -/
def orient (three : Fin 3 ↪ Role) (left : Bool) : Fin 3 ↪ Role :=
  if left then three else (Equiv.swap 0 1).toEmbedding.trans three

omit [DecidableEq Role] in
@[simp] theorem orient_zero (three : Fin 3 ↪ Role) (left : Bool) :
    orient three left 0 = if left then three 0 else three 1 := by
  cases left <;> simp [orient]
omit [DecidableEq Role] in
@[simp] theorem orient_one (three : Fin 3 ↪ Role) (left : Bool) :
    orient three left 1 = if left then three 1 else three 0 := by
  cases left <;> simp [orient]
omit [DecidableEq Role] in
@[simp] theorem orient_two (three : Fin 3 ↪ Role) (left : Bool) :
    orient three left 2 = three 2 := by
  cases left <;> simp [orient, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
    (by decide : (2 : Fin 3) ≠ 1)]

private theorem neutral_ambiguous (three : Fin 3 ↪ Role) (k r : Role) :
    Sources.representative three k .neutral ≠ WinnerSet.singleton r := by
  intro atom
  by_cases h : r = k
  · subst r
    exact Sources.representative_omits three k .neutral (by rw [atom]; rfl)
  · have bad := (Sources.representative_atom_iff three k .neutral ⟨r,h⟩).mp atom
    cases bad

/-- The grouped probe for a logical label f marked by a row with posting P.
The primary owner is 0, the mark is 1, and the address helper belongs to 2. -/
noncomputable def joint (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (P : Set Label) (f : Label) (u : Rail Track Bit) : WinnerSet Role := by
  classical
  exact if B.On f u then WinnerSet.singleton (three 1)
    else if u.1 = B.track f then WinnerSet.singleton (three 2)
    else if B.Posted P u then WinnerSet.singleton (three 0)
    else Sources.representative three (three 1) .neutral

omit [DecidableEq Role] in
theorem joint_mark (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (P : Set Label) (f : Label) (u : Rail Track Bit) :
    three 1 ∈ (joint three B P f u).val ↔ B.On f u := by
  classical
  have n10 : three 1 ≠ three 0 := three.injective.ne (by decide)
  have n12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  unfold joint
  split_ifs <;> simp_all [WinnerSet.singleton]

theorem joint_primary (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (P : Set Label) (f : Label) (u : Rail Track Bit) :
    joint three B P f u = WinnerSet.singleton (three 0) ↔ u.1 ≠ B.track f ∧ B.Posted P u := by
  classical
  unfold joint
  split_ifs with on tr post
  · simp [on.1, WinnerSet.singleton_inj]
  · simp [tr, WinnerSet.singleton_inj]
  · simp [tr, post]
  · simp [neutral_ambiguous, post]

theorem joint_aux (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (P : Set Label) (f : Label) (u : Rail Track Bit) :
    joint three B P f u = WinnerSet.singleton (three 2) ↔ u.1 = B.track f ∧ ¬ B.On f u := by
  classical
  unfold joint
  split_ifs <;> simp_all [neutral_ambiguous, WinnerSet.singleton_inj]

theorem joint_owners (three : Fin 3 ↪ Role) (B : Book Label Track Bit) (P : Set Label)
    (f : Label) (u : Rail Track Bit) (r : Role) (atom : joint three B P f u = WinnerSet.singleton r) :
    r = three 0 ∨ r = three 1 ∨ r = three 2 := by
  classical
  unfold joint at atom
  split_ifs at atom <;> simp_all [neutral_ambiguous, WinnerSet.singleton_inj]

/-- On a track shared in full, the grouped probe for its logical mark rules
out the auxiliary singleton test. This argument needs no assumptions on
other tracks or on the owner's unused roles. -/
theorem lock_at_shared (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (A D C : Rail Track Bit → Bool) (P : Set Label) (f : Label)
    (inside : ∀ u, C u = true → u.1 = B.track f)
    (shared : ∀ u : Rail Track Bit, u.1 = B.track f → A u = true → D u = true → B.On f u)
    (t : CoreTerm Role (Rail Track Bit)) (ha : profile (three 0) A t = true)
    (hd : profile (three 1) D t = true) (hc : profile (three 2) C t = true)
    (quiet : three 1 ∉ (t.realize (joint three B P f)).val) : False := by
  apply quiet
  apply OfferLock.mark_of_three_profiles three A D C _ _ _ _ t ha hd hc
  · intro u au du cu
    exact (joint_mark three B P f u).mpr (shared u (inside u cu) au du)
  · intro u cu atom
    exact ((joint_primary three B P f u).mp atom).1 (inside u cu)
  · intro u au du atom
    obtain ⟨tr, absent⟩ := (joint_aux three B P f u).mp atom
    exact absent (shared u tr au du)


/-- One logical side per row. The posting of each vertex is rainbow in the
track colors, and its distinguished mark lies on a different track. -/
structure Rows (B : Book Label Track Bit) (Row : Type*) where
  left : Row → Bool
  mark : Row → Label
  posted : Row → Set Label
  sparseLeft : ∀ z, left z = true → B.Sparse (posted z)
  sparseRight : ∀ z, left z = false → B.SparseOrFull (posted z)
  apart : ∀ z f, f ∈ posted z → B.track f ≠ B.track (mark z)

namespace Rows
variable {B : Book Label Track Bit} (R : Rows B Row)
noncomputable def cube (z : Row) (f : Label) : Value := by
  classical
  exact if f = R.mark z then .possible else
    if f ∈ R.posted z then (if R.left z then .c else .b) else .neutral

theorem cube_mark (z : Row) (f : Label) : R.cube z f = .possible ↔ f = R.mark z := by
  classical
  unfold cube
  split_ifs <;> simp_all

theorem cube_pos (z : Row) (hz : R.left z = true) :
    {f | cubeLower (R.cube z) f = true} = R.posted z := by
  classical
  ext f
  by_cases mark : f = R.mark z
  · subst f
    have absent : R.mark z ∉ R.posted z := fun h => R.apart z _ h rfl
    simp [cubeLower, cube, absent]
  · by_cases p : f ∈ R.posted z <;> simp [cubeLower, cube, mark, p, hz]

theorem cube_neg (z : Row) (hz : R.left z = false) :
    {f | cubeUpper (R.cube z) f = false} = R.posted z := by
  classical
  ext f
  by_cases mark : f = R.mark z
  · subst f
    have absent : R.mark z ∉ R.posted z := fun h => R.apart z _ h rfl
    simp [cubeUpper, cube, absent]
  · by_cases p : f ∈ R.posted z <;> simp [cubeUpper, cube, mark, p, hz]

end Rows

abbrev Static (Track Bit : Type*) := (u : Rail Track Bit) × {i : Bit // i ≠ u.2.1}
abbrev Probe (Row Track Bit : Type*) := Sum Row (Static Track Bit)

noncomputable def staticValues (three : Fin 3 ↪ Role) (p : Static Track Bit)
    (v : Rail Track Bit) : WinnerSet Role := by
  classical
  exact if v = p.1 then WinnerSet.singleton (three 1)
    else if v.1 = p.1.1 ∧ v.2.1 = p.2.val then WinnerSet.singleton (three 2)
    else Sources.representative three (three 1) .neutral

theorem static_atom (three : Fin 3 ↪ Role) (p : Static Track Bit) (v : Rail Track Bit) (r : Role)
    (h : staticValues three p v = WinnerSet.singleton r) :
    (v = p.1 ∧ r = three 1) ∨ (v.1 = p.1.1 ∧ v.2.1 = p.2.val ∧ r = three 2) := by
  classical
  unfold staticValues at h
  split_ifs at h <;> simp_all [WinnerSet.singleton_inj, neutral_ambiguous]

namespace Rows
variable {B : Book Label Track Bit} (R : Rows B Row) (three : Fin 3 ↪ Role)

def tag : Probe Row Track Bit → Option Row
  | .inl z => some z
  | .inr _ => none

def observer : Probe Row Track Bit → Role
  | .inl z => orient three (R.left z) 1
  | .inr _ => three 1

noncomputable def values : Probe Row Track Bit → Rail Track Bit → WinnerSet Role
  | .inl z => joint (orient three (R.left z)) B (R.posted z) (R.mark z)
  | .inr p => staticValues three p

noncomputable def flags (F : Set Label) : Rail Track Bit → Bool := by
  classical
  exact fun u => decide (B.Posted F u)

variable [Nontrivial Bit]
noncomputable def encoding :
    AddressedCubeCut.Encoding Role (Rail Track Bit) Label Row (Probe Row Track Bit) R.cube := by
  classical
  refine { left := three 0, right := three 1, aux := three 2,
           distinct := three.injective.ne (by decide), pos := fun x => flags (B := B) {f | x f = true},
           neg := fun y => flags (B := B) {f | y f = false}, tag := tag,
           values := R.values three, observe := R.observer three,
           head := ?_, owners := ?_, posRow := ?_, negRow := ?_ }
  · intro u
    obtain ⟨i, diff⟩ := exists_ne u.2.1
    exact ⟨.inr ⟨u, i, diff⟩, rfl, by simp [observer, values, staticValues, WinnerSet.singleton]⟩
  · rintro (z | p) u r atom
    · have own := joint_owners _ _ _ _ _ _ atom
      cases h : R.left z <;> simp_all [observer, orient]
      all_goals tauto
    · obtain ⟨_, h⟩ | ⟨_, _, h⟩ := static_atom _ _ _ _ atom
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · rintro (z | p) ne ⟨u, atom⟩
    · have side : R.left z = true := by
        cases h : R.left z <;> simp_all [observer]
      refine ⟨z, rfl, ?_⟩
      intro v hv
      change joint (orient three (R.left z)) B _ _ _ = _ at hv
      simp only [side, orient, ite_true] at hv
      have post := ((joint_primary three _ _ _ _).mp hv).2
      simpa [flags, R.cube_pos z side] using post
    · obtain ⟨_, h⟩ | ⟨_, _, h⟩ := static_atom _ _ _ _ atom <;> simp at h
  · rintro (z | p) ne ⟨u, atom⟩
    · have side : R.left z = false := by
        cases h : R.left z <;> simp_all [observer]
      refine ⟨z, rfl, ?_⟩
      intro v hv
      have same : orient three (R.left z) 0 = three 1 := by simp [side]
      change joint (orient three (R.left z)) B _ _ _ = _ at hv
      rw [← same] at hv
      have post := ((joint_primary _ _ _ _ _).mp hv).2
      simpa [flags, R.cube_neg z side] using post
    · exact (ne rfl).elim


private noncomputable def budget (p : Static Track Bit) : Budget Role (Rail Track Bit) :=
  ⟨staticValues three p, {k | k ≠ three 1}⟩

omit [Nontrivial Bit] in
private theorem single : SingleAbsorber (budget (Track := Track) (Bit := Bit) three) (three 2) := by
  intro p k hk diff u atom
  obtain ⟨_, eq⟩ | ⟨_, _, eq⟩ := static_atom three p u k atom
  · exact hk eq
  · exact diff eq

omit [Nontrivial Bit] in
private theorem static_spans {S : Set (Rail Track Bit)} (safe : SafeSupport (budget three) (three 2) S) :
    ∀ u ∈ S, ∀ i : Bit, ∃ v ∈ S, v.1 = u.1 ∧ v.2.1 = i := by
  apply safe_spans (three 2) (budget three) _ S safe
  intro u i ne
  let p : Static Track Bit := ⟨u, i, ne⟩
  refine ⟨p, ?_, ?_⟩
  · intro all
    apply all (a := three 1) _ rfl
    simp [budget, staticValues, p, WinnerSet.singleton]
  · intro v atom
    obtain ⟨_, eq⟩ | ⟨vt, vb, _⟩ := static_atom three p v (three 2) atom
    · simp at eq
    · exact ⟨vt, vb⟩

omit [Nontrivial Bit] in
private theorem aux_track (p : Probe Row Track Bit) :
    ∃ g : Track, ∀ u, R.values three p u = WinnerSet.singleton (three 2) → u.1 = g := by
  cases p with
  | inr q =>
    refine ⟨q.1.1, ?_⟩
    intro u atom
    obtain ⟨_, eq⟩ | ⟨ht, _, _⟩ := static_atom three q u (three 2) atom
    · simp at eq
    · exact ht
  | inl z =>
    refine ⟨B.track (R.mark z), ?_⟩
    intro u atom
    have atom' : joint (orient three (R.left z)) B (R.posted z) (R.mark z) u = WinnerSet.singleton (orient three (R.left z) 2) := by
      simpa only [values, orient_two] using atom
    exact ((joint_aux _ _ _ _ _).mp atom').1

variable [Fintype Track] [Fintype Bit] [DecidableEq Row]

/-- A logical losing rectangle cut rules out *every* physical core word
on the rails. Both endpoint sets are sparse on each track. The obstruction
applies to an arbitrary finite set of logical rows and to either orientation
of every row, using only the three distinguished owner gates for its tests. -/
theorem no_word_of_rectangle_cut {Z : Finset Row} {x y : Label → Bool}
    (cut : CubeCut R.cube Z (.separate x y))
    (hx : B.Sparse {f | x f = true}) (hy : B.SparseOrFull {f | y f = false}) :
    ∀ t : CoreTerm Role (Rail Track Bit), (R.encoding three).Quiet Z t →
      ¬ (R.encoding three).Demands x y t := by
  classical
  let E := R.encoding three
  apply E.no_word_of_cut (fun x => B.Sparse {f | x f = true}) (fun y => B.SparseOrFull {f | y f = false})
    _ _ _ cut hx hy
  · rintro (w | p) z tag ⟨u, atom⟩
    · have eq : w = z := Option.some.inj tag
      subst z
      by_cases side : R.left w = true
      · rw [R.cube_pos w side]
        exact R.sparseLeft w side
      · have h : {f | cubeLower (R.cube w) f = true} = ∅ := by
          ext f
          by_cases a : f = R.mark w <;> by_cases b : f ∈ R.posted w <;>
            simp [cubeLower, cube, a, b, side]
        simp [h, Book.Sparse]
    · cases tag
  · rintro (w | p) z tag ⟨u, atom⟩
    · have eq : w = z := Option.some.inj tag
      subst z
      by_cases side : R.left w = false
      · rw [R.cube_neg w side]
        exact R.sparseRight w side
      · have h : {f | cubeUpper (R.cube w) f = false} = ∅ := by
          ext f
          by_cases a : f = R.mark w <;> by_cases b : f ∈ R.posted w <;>
            simp [cubeUpper, cube, a, b, Bool.eq_true_of_not_eq_false side]
        simp [h, Book.SparseOrFull]
    · cases tag
  · intro S x y a d covered t quiet h p _ atom
    let C (u : Rail Track Bit) := decide (R.values three p u = WinnerSet.singleton (three 2))
    let A : Set Label := {f | x f = true}
    let D : Set Label := {f | y f = false}
    let af := flags (B := B) A
    let df := flags (B := B) D
    have ha : profile (three 0) af t = true := h.1
    have hd : profile (three 1) df t = true := h.2
    have hc : profile (three 2) C t = true := (winnerSet_eq_singleton_iff_profile t _ _).mp atom
    have safe : Satisfies (budget (Track := Track) (Bit := Bit) three) t := by
      intro row k mem eq
      subst k
      exact quiet (.inr row) (by intro z h; cases h) mem
    obtain ⟨sup, ssafe, within, first, hfirst, inC⟩ :=
      support_of_three three (budget three) (single three) af df C t safe ha hd hc
    obtain ⟨g, track⟩ := R.aux_track three p
    have inside u (cu : C u = true) := track u (of_decide_eq_true cu)
    obtain ⟨f, hf, df', tr, shared⟩ := B.shared_address A D g sup a d
        (fun u hu => ⟨of_decide_eq_true (within u hu).1, of_decide_eq_true (within u hu).2⟩)
        ⟨first, hfirst, inside _ inC⟩ (static_spans three ssafe)
    obtain ⟨z, zmem, mark⟩ := covered f hf df'
    have fm := (R.cube_mark z f).mp mark
    subst f
    have agree (u : Rail Track Bit) (ug : u.1 = B.track (R.mark z))
        (au : af u = true) (du : df u = true) : B.On (R.mark z) u :=
      (shared u (ug.trans tr)).mp ⟨of_decide_eq_true au, of_decide_eq_true du⟩
    have localQuiet := quiet (.inl z) (by
      intro w tag
      exact (Option.some.inj tag) ▸ zmem)
    change orient three (R.left z) 1 ∉ (t.realize (joint (orient three (R.left z)) B _ _)).val at localQuiet
    cases side : R.left z with
    | true =>
      simp only [side, orient, ite_true] at localQuiet
      exact lock_at_shared three B af df C (R.posted z) (R.mark z)
        (fun u cu => (inside u cu).trans tr.symm) agree t ha hd hc localQuiet
    | false =>
      rw [side] at localQuiet
      apply lock_at_shared (orient three false) B df af C (R.posted z) (R.mark z)
        (fun u cu => (inside u cu).trans tr.symm) (fun u ug du au => agree u ug au du)
        t _ _ _ localQuiet
      · simpa only [orient_zero, Bool.false_eq_true, ite_false] using hd
      · simpa only [orient_one, Bool.false_eq_true, ite_false] using ha
      · simpa only [orient_two] using hc

end Rows
end KFOL.Core.AddressedRectangle
