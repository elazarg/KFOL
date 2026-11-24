module

public import KFOL.Core.AddressedSubstitution
public import KFOL.Core.OneOwnerSelector

/-! # The two logical groups of an addressed rectangle

One endpoint and all active omissions of the same orientation are budgets
with a single possible absorbing owner. A greatest group word is determined
by the one-owner Horn computation at each valuation.
-/

@[expose] public section
namespace KFOL.Core.AddressedLogicalGroups

open AddressedRails AddressedRectangle ProfileBudgets WinnerSet MonochromaticCutObstruction
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Label Track Bit Row : Type*} [DecidableEq Role] {B : Book Label Track Bit}

omit [DecidableEq Role] in
theorem primary_ne_aux (three : Fin 3 ↪ Role) (side : Bool) : orient three side 0 ≠ three 2 := by
  rw [← orient_two three side]
  exact (orient three side).injective.ne (by decide)

theorem mark_off (R : Rows B Row) (z : Row) : R.mark z ∉ R.posted z :=
  fun h => R.apart z _ h rfl

/-- Each raw row has the same logical observer, the auxiliary role. -/
noncomputable def rawValues (three : Fin 3 ↪ Role) (R : Rows B Row) (z : Row) :
    Label → WinnerSet Role :=
  pureProbe three (three 2) (R.mark z) (orient three (R.left z) 0)
    (primary_ne_aux three _) (fun f => decide (f ∈ R.posted z))

def Good (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row) (side : Bool)
    (A : Label → Bool) (t : CoreTerm Role Label) : Prop :=
  profile (orient three side 0) A t = true ∧
    ∀ z ∈ S, R.left z = side → three 2 ∉ (t.realize (rawValues three R z)).val

def Envelope (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row) (side : Bool)
    (A : Label → Bool) (t : CoreTerm Role Label) : Prop :=
  Good three R S side A t ∧ ∀ g, Good three R S side A g →
    ∀ v : Label → WinnerSet Role, (g.realize v).val ⊆ (t.realize v).val

abbrev Index (R : Rows B Row) (S : Finset Row) (side : Bool) :=
  Option {z : Row // z ∈ S ∧ R.left z = side}

noncomputable def endpointValues (three : Fin 3 ↪ Role) (r : Role) (A : Label → Bool)
    (f : Label) : WinnerSet Role :=
  if A f then singleton r else Sources.representative three r .neutral

omit [DecidableEq Role] in
theorem endpoint_flags (three : Fin 3 ↪ Role) (r : Role) (A : Label → Bool) :
    (fun f => decide (endpointValues three r A f = singleton r)) = A := by
  have miss : Sources.representative three r .neutral ≠ singleton r := fun eq =>
    Sources.representative_omits three r .neutral (by rw [eq]; rfl)
  funext f
  cases h : A f <;> simp [endpointValues, h, miss]

noncomputable def bounds (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (A : Label → Bool) : Index R S side → Budget Role Label
  | none => ⟨endpointValues three (orient three side 0) A, {orient three side 0}⟩
  | some z => ⟨rawValues three R z.val, {r | r ≠ three 2}⟩

theorem bounds_single (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (A : Label → Bool) :
    SingleAbsorber (bounds three R S side A) (orient three side 0) := by
  rintro (_ | ⟨z, hz, eq⟩) s ok other j atom
  · exact other ok
  · have same := ((pure_atom three (three 2) (.var j) (R.mark z) (orient three (R.left z) 0) (primary_ne_aux three _)
      s (fun f => decide (f ∈ R.posted z)) (decide_eq_false (mark_off R z)) ok).mp atom).1
    exact other (eq ▸ same)

theorem satisfies_iff (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (A : Label → Bool) (t : CoreTerm Role Label) :
    Satisfies (bounds three R S side A) t ↔ Good three R S side A t := by
  let r := orient three side 0
  have eq : t.realize (endpointValues three r A) = singleton r ↔ profile r A t = true := by
    rw [winnerSet_eq_singleton_iff_profile, endpoint_flags]
  constructor
  · intro h
    exact ⟨eq.mp (eq_singleton_of_subset _ _ (h none)), fun z hz sidez hit =>
      h (some ⟨z,hz,sidez⟩) hit rfl⟩
  · rintro ⟨win,quiet⟩ (_ | ⟨z,hz,sidez⟩)
    · change (t.realize (endpointValues three r A)).val ⊆ {r}
      rw [eq.mpr win]
      rfl
    · intro k hk he
      exact quiet z hz sidez (he ▸ hk)

/-- Evaluating the Horn rule at each winner gives the operation of the
greatest group word. -/
theorem exists_envelope [Fintype Role] [Fintype Label] (three : Fin 3 ↪ Role)
    (R : Rows B Row) (S : Finset Row) (side : Bool) (A : Label → Bool)
    (possible : ∃ g, Good three R S side A g) :
    ∃ t, Envelope three R S side A t ∧ ∀ (v : Label → WinnerSet Role) k, k ∈ (t.realize v).val ↔
      ∃ f ∈ greatestSupport (bounds three R S side A) (orient three side 0)
        (OneOwnerSelector.eligible (orient three side 0) k v), k ∈ (v f).val := by
  obtain ⟨g,hg⟩ := possible
  have spec := satisfies_iff three R S side A
  obtain ⟨t,hb,formula⟩ := OneOwnerSelector.exists_envelope three _ _ (bounds_single three R S side A)
    ⟨g, (spec g).mpr hg⟩
  refine ⟨t, ⟨(spec t).mp hb, fun u hu v k hk => (formula v k).mpr ?_⟩, formula⟩
  exact (OneOwnerSelector.winner_iff _ _ (bounds_single three R S side A) k v).mp
    ⟨u,(spec u).mpr hu,hk⟩


/-- A full fold duplicates the distinguished input as the final leaf. -/
noncomputable def fullFold [Fintype Label] (r : Role) (d : Label) : CoreTerm Role Label :=
  foldTerm r (Finset.univ.toList.map .var) (.var d)

theorem fullFold_owner [Fintype Label] (r : Role) (d : Label) (A : Label → Bool) :
    profile r A (fullFold r d) = true ↔ ∃ f, A f = true := by
  simp only [fullFold, profile_fold_owner, profile_var, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨t, ⟨f, rfl⟩, h⟩)
    · exact ⟨d,h⟩
    · exact ⟨f,h⟩
  · rintro ⟨f, h⟩
    exact Or.inr ⟨.var f, ⟨f,rfl⟩, h⟩

theorem fullFold_foreign [Fintype Label] (r k : Role) (d : Label) (A : Label → Bool)
    (diff : r ≠ k) : profile k A (fullFold r d) = true ↔ ∀ f, A f = true := by
  simp only [fullFold, profile_fold_other r k diff, profile_var, List.forall_mem_map,
    Finset.mem_toList, Finset.mem_univ, forall_const, profile_var]
  exact ⟨And.right, fun h => ⟨h d, h⟩⟩

/-- The side fold is a legal group word whenever the endpoint and each
active row of that side contain a posting. -/
theorem exists_good [Fintype Label] (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (A : Label → Bool) (endHit : ∃ f, A f = true)
    (rowHit : ∀ z ∈ S, R.left z = side → (R.posted z).Nonempty) :
    ∃ t, Good three R S side A t := by
  obtain ⟨d, hd⟩ := endHit
  let r := orient three side 0
  let t := fullFold r d
  refine ⟨t,(fullFold_owner r d A).mpr ⟨d,hd⟩,?_⟩
  intro z hz sidez
  obtain ⟨f, hf⟩ := rowHit z hz sidez
  have test := (fullFold_owner r d (fun f => decide (f ∈ R.posted z))).mpr ⟨f,decide_eq_true hf⟩
  have atom : t.realize (rawValues three R z) = singleton r := by
    apply (pure_atom three (three 2) t (R.mark z) (orient three (R.left z) 0) _
      r (fun f => decide (f ∈ R.posted z)) (decide_eq_false (mark_off R z)) (primary_ne_aux three _)).mpr
    simpa only [sidez, r, true_and] using test
  rw [atom]
  exact Ne.symm (primary_ne_aux three _)

private theorem profile_every (k : Role) (t : CoreTerm Role Label) (A : Label → Bool)
    (all : ∀ f, A f = true) : profile k A t = true := by
  induction t using induction_choice with
  | var i => exact all i
  | choice q _ _ hx hy => simp [profile_choice, hx, hy]

/-- Two private postings give a shared logical witness the unanimous
auxiliary profile. A right private input suffices when every left row
already contains a posting. -/
theorem pad_witness [Fintype Label] (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (x y : Label → Bool) (d : Label) (inRight : y d = false)
    (unmarked : ∀ z ∈ S, d ≠ R.mark z)
    (rightPosts : ∀ z ∈ S, R.left z = false → d ∈ R.posted z)
    (leftPosts : ∀ z ∈ S, R.left z = true → (R.posted z).Nonempty)
    (w : CoreTerm Role Label) (goodL : Good three R S true x w)
    (goodR : Good three R S false (fun i => !(y i)) w) :
    ∃ g, Good three R S true x g ∧ Good three R S false (fun i => !(y i)) g ∧
      ∀ A : Label → Bool, profile (three 2) A g = true ↔ ∀ f, A f = true := by
  let a := three 0
  let b := three 1
  let c := three 2
  let F := fullFold a d
  let U := choiceTerm b F (.var d)
  let g := choiceTerm a w U
  have ab : a ≠ b := three.injective.ne (by decide)
  have ac : a ≠ c := three.injective.ne (by decide)
  have bc : b ≠ c := three.injective.ne (by decide)
  have quietU (z : Row) (hz : z ∈ S) : c ∉ (U.realize (rawValues three R z)).val := by
    by_cases side : R.left z = true
    · obtain ⟨f, hf⟩ := leftPosts z hz side
      have pass := (fullFold_owner a d (fun f => decide (f ∈ R.posted z))).mpr ⟨f, decide_eq_true hf⟩
      have atom : F.realize (rawValues three R z) = singleton a := by
        apply (pure_atom three c F (R.mark z) _ (primary_ne_aux three (R.left z)) a
          (fun f => decide (f ∈ R.posted z)) (decide_eq_false (mark_off R z)) ac).mpr
        simpa only [side, orient_zero, ite_true, true_and, F, a] using pass
      intro hit
      rcases choice_subset_union b (F.realize (rawValues three R z)) (rawValues three R z d) hit with h | h
      · exact ac.symm (by simpa [atom] using h)
      · exact unmarked z hz ((Sources.mem_probe_iff three (three 2) (R.mark z) _ d).mp h)
    · have notLeft := Bool.eq_false_of_not_eq_true side
      have posted := rightPosts z hz notLeft
      have atom : rawValues three R z d = WinnerSet.singleton b := by
        unfold rawValues pureProbe
        rw [Sources.probe_other _ _ _ _ d (unmarked z hz)]
        simp [posted, notLeft, Sources.representative, b]
      have uAtom : U.realize (rawValues three R z) = WinnerSet.singleton b :=
        (choice_eq_owner_iff _ _ b).mpr (Or.inr atom)
      rw [uAtom]
      exact Ne.symm bc
  have keep (z : Row) (hz : z ∈ S)
      (quiet : c ∉ (w.realize (rawValues three R z)).val) :
      c ∉ (g.realize (rawValues three R z)).val := fun hit =>
    (choice_subset_union a _ _ hit).elim quiet (quietU z hz)
  have leftWin : profile a x w = true := by simpa [a] using goodL.1
  have rightWin : profile b (fun i => !(y i)) w = true := by simpa [b] using goodR.1
  refine ⟨g, ⟨?_, fun z hz hs => keep z hz (goodL.2 z hz hs)⟩,
    ⟨?_, fun z hz hs => keep z hz (goodR.2 z hz hs)⟩, ?_⟩
  · simpa [g, profile_choice, a] using (show profile a x w = true ∨ profile a x U = true from Or.inl leftWin)
  · change profile b (fun i => !(y i)) g = true
    simp [g, U, profile_choice, ab, rightWin, inRight]
  · intro A
    constructor
    · intro hit
      change profile c A g = true at hit
      have parts : profile c A w = true ∧ profile c A F = true ∧ A d = true := by
        simpa [g, U, profile_choice, ac, bc, profile_var] using hit
      exact (fullFold_foreign a c d A ac).mp parts.2.1
    · exact profile_every c g A

end KFOL.Core.AddressedLogicalGroups
