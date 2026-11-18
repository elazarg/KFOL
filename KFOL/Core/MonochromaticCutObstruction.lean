module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Core.SourceProbes
import Mathlib.Tactic.FinCases

/-! # Five monochromatic source losses forcing a fourth-owner singleton -/

@[expose] public section
namespace KFOL.Core.MonochromaticCutObstruction

inductive Input | x | y | a | b | c deriving DecidableEq
instance : Fintype Input := ⟨{.x,.y,.a,.b,.c}, by intro i; cases i <;> simp⟩

/-- Owners 0, 1, 2 and 3 denote a, b, c and d. -/
def owner : Input → Fin 4
  | .a => 0 | .b => 1 | .c => 2 | .x | .y => 3

/-- On its loss probe, each head posts its entire tail at its owner. -/
def tail : Input → Input → Bool
  | .x, .b | .x, .y => true
  | .y, .x | .y, .a => true
  | .a, .x | .a, .b | .a, .c => true
  | .b, .y | .b, .a | .b, .c => true
  | .c, .x | .c, .a | .c, .b => true
  | _, _ => false

/-- Every same-owner dependency is reciprocal. -/
theorem same_owner_reciprocity :
    ∀ i j, owner i = owner j → tail i j = true → tail j i = true := by decide

/-- Every set of heads containing an internal edge and having consistent
outside postings already contains a monochromatic two-cycle. -/
theorem compatible_cut_has_cycle :
    ∀ H : Finset Input,
      (∀ k ∉ H, ∀ i ∈ H, ∀ j ∈ H, tail i k = true → tail j k = true → owner i = owner j) →
      (∃ i ∈ H, ∃ j ∈ H, tail i j = true) →
      ∃ i ∈ H, ∃ j ∈ H, i ≠ j ∧ owner i = owner j ∧ tail i j = true ∧ tail j i = true := by
  decide

def observer (r : Fin 4) : Fin 4 := if r = 0 then 1 else 0

theorem owner_ne_observer (r : Fin 4) : r ≠ observer r := by fin_cases r <;> decide

/-- A canonical source probe with a single posting owner. -/
noncomputable def pureProbe {Role Var : Type*} (three : Fin 3 ↪ Role) (k : Role)
    (j : Var) (r : Role) (hr : r ≠ k) (T : Var → Bool) : Var → WinnerSet Role :=
  Sources.probe three k j (fun i => if T i.val then .atom ⟨r,hr⟩ else .neutral)

attribute [local instance] Equational.coreStructure

/-- A foreign singleton on a one-color probe is exactly a win at its posting color. -/
theorem pure_atom {Role Var : Type*} [DecidableEq Role] (three : Fin 3 ↪ Role) (k : Role)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (j : Var) (r : Role) (hr : r ≠ k)
    (s : Role) (T : Var → Bool)
    (hj : T j = false) (hs : s ≠ k) :
    t.realize (pureProbe three k j r hr T) = WinnerSet.singleton s ↔ s = r ∧ profile r T t = true := by
  classical
  rw [winnerSet_eq_singleton_iff_profile]
  have flags : (fun i => decide (pureProbe three k j r hr T i = WinnerSet.singleton s)) =
      (fun i => if s = r then T i else false) := by
    funext i
    by_cases he : i = j
    · subst i
      simp [pureProbe, Sources.probe_source, Ne.symm hs, hj]
    · unfold pureProbe
      rw [Sources.probe_other _ _ _ _ i he]
      by_cases sr : s = r
      · subst s
        simp only [ite_true]
        cases hh : T i
        · apply decide_eq_false
          intro he
          cases (Sources.representative_atom_iff _ _ .neutral ⟨r,hs⟩).mp he
        · exact decide_eq_true rfl
      · simp only [ite_eq_right sr]
        apply decide_eq_false
        intro equal
        have h := (Sources.representative_atom_iff _ _ _ ⟨s,hs⟩).mp equal
        cases hh : T i
        · simp [hh] at h
        · simp [hh, Subtype.ext_iff] at h
          exact sr h.symm
  rw [flags]
  by_cases sr : s = r
  · subst s; simp
  · simp [sr,profile_false]

/-- When the posting color loses its singleton test, an omission passes to both children. -/
theorem pass_row {Role Var : Type*} [DecidableEq Role] (three : Fin 3 ↪ Role)
    (j : Var) (k r : Role) (hr : r ≠ k) (T : Var → Bool) (hj : T j = false)
    {s t : Equational.Term (Equational.CoreSymbol Role) Var} {q : Role}
    (quiet : k ∉ ((choiceTerm q s t).realize (pureProbe three k j r hr T)).val)
    (loses : profile r T (choiceTerm q s t) = false) :
    k ∉ (s.realize (pureProbe three k j r hr T)).val ∧
      k ∉ (t.realize (pureProbe three k j r hr T)).val := by
  let v := pureProbe three k j r hr T
  have hn : (choiceTerm q s t).realize v ≠ WinnerSet.singleton q := by
    intro he
    by_cases hq : q = k
    · exact quiet (by change k ∈ ((choiceTerm q s t).realize v).val; rw [he,hq]; rfl)
    · have ha := (pure_atom three k _ j r hr q T hj hq).mp he
      rw [loses] at ha
      exact Bool.noConfusion ha.2
  have hu : (choiceTerm q s t).realize v = (s.realize v).union (t.realize v) := by
    rw [realize_choice_winner]
    unfold WinnerSet.choice
    split
    · rename_i h
      exact (hn ((WinnerSet.choice_eq_owner_iff _ _ q).mpr h)).elim
    · rfl
  change k ∉ ((choiceTerm q s t).realize v).val at quiet
  rw [hu] at quiet
  exact ⟨fun hm => quiet (Or.inl hm),fun hm => quiet (Or.inr hm)⟩

noncomputable def values (j : Input) (r : Fin 4) (T : Input → Bool) : Input → WinnerSet (Fin 4) :=
  pureProbe (Fin.castLEEmb (by decide)) (observer r) j r (owner_ne_observer r) T

private abbrev Word := Equational.Term (Equational.CoreSymbol (Fin 4)) Input

private def Quiet (t : Word) (j : Input) : Prop :=
  observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val

private theorem head_wins (j : Input) (r : Fin 4) (T : Input → Bool) :
    observer r ∈ (values j r T j).val := (Sources.mem_probe_iff _ _ _ _ _).2 rfl

private theorem pass {s t : Word} {q : Fin 4} {j : Input} (quiet : Quiet (choiceTerm q s t) j)
    (loses : profile (owner j) (tail j) (choiceTerm q s t) = false) : Quiet s j ∧ Quiet t j :=
  pass_row _ j _ _ _ _ ((by decide : ∀ j, tail j j = false) j) quiet loses

private def away (j i : Input) := decide (i ≠ j)

/-- Omitting the sole marked head forces the owner test on its complement. -/
private theorem veto (t : Word) (j : Input) (quiet : Quiet t j) :
    profile (owner j) (away j) t = true := by
  induction t using induction_choice with
  | var i =>
    apply decide_eq_true
    rintro rfl
    exact quiet (head_wins _ _ _)
  | choice q s t hs ht =>
    by_contra! hn
    have less : ∀ i, tail j i = true → away j i = true :=
      (by decide : ∀ j i, tail j i = true → away j i = true) j
    have loses : profile (owner j) (tail j) (choiceTerm q s t) = false := by
      cases h : profile (owner j) (tail j) (choiceTerm q s t) with
      | false => rfl
      | true => exact (hn (profile_mono _ _ _ less _ h)).elim
    obtain ⟨hq,hq'⟩ := pass quiet loses
    simp [profile_choice,hs hq,ht hq'] at hn

private theorem rainbow (t : Word) (A B C D : Input → Bool)
    (no : ∀ i, (A i && B i && C i && D i) = false)
    (ha : profile 0 A t = true) (hb : profile 1 B t = true)
    (hc : profile 2 C t = true) (hd : profile 3 D t = true) : False := by
  let F : Fin 4 → Input → Bool := ![A,B,C,D]
  have h (r : Fin 4) : profile r (F r) t = true := by fin_cases r <;> assumption
  obtain ⟨i, hi⟩ := profile_common_source id Function.injective_id F t h
  have bad := no i
  have hA : A i = true := hi 0
  have hB : B i = true := hi 1
  have hC : C i = true := hi 2
  have hD : D i = true := hi 3
  simp [hA,hB,hC,hD] at bad

/-- Each foreign tail is covered by a rainbow of excluded inputs. For B the
winning test on the Y-tail can replace the exclusion of Y. -/
private theorem foreign_loses (t : Word) (quiet : ∀ j, j ≠ .y → Quiet t j)
    (bridge : profile 3 (away .y) t = true ∨ profile 3 (tail .y) t = true) :
    ∀ j, j ≠ .x → j ≠ .y → profile (owner j) (tail j) t = false := by
  have ha := veto t .a (quiet _ (by decide))
  have hb := veto t .b (quiet _ (by decide))
  have hc := veto t .c (quiet _ (by decide))
  have hx := veto t .x (quiet _ (by decide))
  intro j hnx hny
  apply Bool.eq_false_of_not_eq_true
  intro hw
  cases j with
  | x => exact hnx rfl
  | y => exact hny rfl
  | a => exact rainbow t (tail .a) (away .b) (away .c) (away .x) (by decide) hw hb hc hx
  | b =>
    rcases bridge with hy | hy
    · exact rainbow t (away .a) (tail .b) (away .c) (away .y) (by decide) ha hw hc hy
    · exact rainbow t (away .a) (tail .b) (away .c) (tail .y) (by decide) ha hw hc hy
  | c => exact rainbow t (away .a) (away .b) (tail .c) (away .x) (by decide) ha hb hw hx

/-- Dropping just the Y loss still precludes winning its d-test while
losing the X test. Both sides of this profile gap pass to one child. -/
private theorem no_gap (t : Word) (quiet : ∀ j, j ≠ .y → Quiet t j)
    (hy : profile 3 (tail .y) t = true) (hx : profile 3 (tail .x) t = false) : False := by
  induction t using induction_choice with
  | var i =>
    by_cases he : i = .y
    · subst i; cases hy
    · exact quiet i he (head_wins i _ _)
  | choice r s t ihs iht =>
    have children (j : Input) (hj : j ≠ .y) : Quiet s j ∧ Quiet t j := by
      apply pass (quiet j hj)
      by_cases he : j = .x
      · subst j; exact hx
      · exact foreign_loses _ quiet (Or.inr hy) j he hj
    have left := ihs (fun j hj => (children j hj).1)
    have right := iht (fun j hj => (children j hj).2)
    by_cases hr : r = 3
    · simp only [profile_choice,ite_eq_left hr,Bool.or_eq_true,Bool.or_eq_false_iff] at hy hx
      exact hy.elim (fun a => left a hx.1) (fun a => right a hx.2)
    · simp only [profile_choice,ite_eq_right hr,Bool.and_eq_true,Bool.and_eq_false_imp] at hy hx
      cases hs : profile 3 (tail .x) s with
      | false => exact left hy.1 hs
      | true => exact right hy.2 (by simpa [profile_choice,hr,hs] using hx)

/-- Every word satisfying the five losses already forces d when just B and
Y are posted at d. The statement uses the full, isolated-source probes. -/
theorem forced_profile (t : Equational.Term (Equational.CoreSymbol (Fin 4)) Input)
    (quiet : ∀ j, observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val) :
    profile 3 (tail .x) t = true := by
  change ∀ j, Quiet t j at quiet
  induction t using induction_choice with
  | var i => exact (quiet i (head_wins i _ _)).elim
  | choice q s t ihs iht =>
    by_contra nhx
    have hx := Bool.eq_false_of_not_eq_true nhx
    have hy : profile 3 (tail .y) (choiceTerm q s t) = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun win => no_gap _ (fun j _ => quiet j) win hx
    have hforeign := foreign_loses _ (fun j _ => quiet j) (Or.inl (veto _ .y (quiet .y)))
    have children (j : Input) : Quiet s j ∧ Quiet t j := by
      apply pass (quiet j)
      by_cases ex : j = .x
      · subst j; exact hx
      by_cases ey : j = .y
      · subst j; exact hy
      exact hforeign j ex ey
    simp [profile_choice,ihs (fun j => (children j).1),iht (fun j => (children j).2)] at hx

/-- The five pure losses and the positive C-mark on B,Y posted at d
cannot be realized simultaneously by a core word. -/
theorem no_core_witness (t : Equational.Term (Equational.CoreSymbol (Fin 4)) Input)
    (quiet : ∀ j, observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val) :
    observer 3 ∉ (t.realize (values .c 3 (tail .x))).val := by
  have he := (pure_atom (Fin.castLEEmb (by decide)) (observer 3) t .c 3 (owner_ne_observer 3) 3
    (tail .x) rfl (owner_ne_observer 3)).mpr ⟨rfl,forced_profile t quiet⟩
  unfold values
  rw [he]
  exact fun hm => owner_ne_observer 3 hm.symm

namespace ThreeOwners

inductive Input | x | y | z | w | a | b deriving DecidableEq
instance : Fintype Input := ⟨{.x,.y,.z,.w,.a,.b}, by intro i; cases i <;> simp⟩

/-- Owners 0, 1 and 2 denote a, b and d. -/
def owner : Input → Fin 3
  | .a => 0 | .b => 1 | _ => 2

def tail : Input → Input → Bool
  | .x, .y | .x, .b => true
  | .y, .x | .y, .a => true
  | .z, .w | .z, .a | .z, .b => true
  | .w, .z => true
  | .a, .b | .a, .x | .a, .z => true
  | .b, .a | .b, .y | .b, .z => true
  | _, _ => false

/-- The positive query posts y, z and B at d. -/
def positiveTail : Input → Bool
  | .y | .z | .b => true
  | _ => false

theorem same_owner_reciprocity :
    ∀ i j, owner i = owner j → tail i j = true → tail j i = true := by decide

private def consistent (H : Finset Input) : Bool := decide
  (∀ k ∉ H, ∀ i ∈ H, ∀ j ∈ H, tail i k = true → tail j k = true → owner i = owner j)
private def omits (r : Fin 3) (H : Finset Input) : Bool := decide
  (∀ i ∈ H, owner i = r → ∀ k ∉ H, tail i k = false)
private def encloses (H : Finset Input) : Bool := decide (∃ i ∈ H, ∃ j ∈ H, tail i j = true)
private def hasPair (H : Finset Input) : Bool := decide
  (∃ i ∈ H, ∃ j ∈ H, i ≠ j ∧ owner i = owner j ∧ tail i j = true ∧ tail j i = true)

/-- A consistent boundary omitting at least one color cannot enclose an
edge unless it also encloses a monochromatic two-cycle. -/
theorem compatible_proper_cut_has_cycle (missing : Fin 3) :
    ∀ H : Finset Input,
      (∀ k ∉ H, ∀ i ∈ H, ∀ j ∈ H, tail i k = true → tail j k = true → owner i = owner j) →
      (∀ i ∈ H, owner i = missing → ∀ k ∉ H, tail i k = false) →
      (∃ i ∈ H, ∃ j ∈ H, tail i j = true) →
      ∃ i ∈ H, ∃ j ∈ H, i ≠ j ∧ owner i = owner j ∧ tail i j = true ∧ tail j i = true := by
  have check : ∀ (r : Fin 3) (H : Finset Input),
      (consistent H && omits r H && encloses H && !hasPair H) = false := by decide
  intro H hc ho he
  by_contra hn
  have h1 : consistent H = true := decide_eq_true hc
  have h2 : omits missing H = true := decide_eq_true ho
  have h3 : encloses H = true := decide_eq_true he
  have h4 : hasPair H = false := decide_eq_false hn
  simpa [h1,h2,h3,h4] using check missing H

def observer (r : Fin 3) : Fin 3 := if r = 0 then 1 else 0

theorem owner_ne_observer (r : Fin 3) : r ≠ observer r := by fin_cases r <;> decide

noncomputable def values (j : Input) (r : Fin 3) (T : Input → Bool) : Input → WinnerSet (Fin 3) :=
  pureProbe (Function.Embedding.refl _) (observer r) j r (owner_ne_observer r) T

private abbrev Word := Equational.Term (Equational.CoreSymbol (Fin 3)) Input
private def Quiet (t : Word) (j : Input) : Prop :=
  observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val
private abbrev Safe (t : Word) (R : Finset Input) := ∀ j ∈ R, Quiet t j
private def outside (G : Finset Input) (i : Input) := decide (i ∉ G)

private theorem head_wins (j : Input) :
    observer (owner j) ∈ (values j (owner j) (tail j) j).val := (Sources.mem_probe_iff _ _ _ _ _).2 rfl

private theorem pass {s t : Word} {q : Fin 3} {j : Input} (quiet : Quiet (choiceTerm q s t) j)
    (loses : profile (owner j) (tail j) (choiceTerm q s t) = false) : Quiet s j ∧ Quiet t j :=
  pass_row _ j _ _ _ _ ((by decide : ∀ j, tail j j = false) j) quiet loses

/-- Simultaneously omitting independently posted heads forces the complement
of the whole group to be a positive coalition for their common owner. -/
private theorem group_veto {R : Finset Input} (t : Word) (r : Fin 3) (G : Finset Input)
    (sub : G ⊆ R) (data : ∀ j ∈ G, owner j = r ∧ ∀ i ∈ G, tail j i = false)
    (safe : Safe t R) : profile r (outside G) t = true := by
  suffices aux : ∀ t : Word, Safe t G → profile r (outside G) t = true from
    aux t (fun j hj => safe j (sub hj))
  intro e
  induction e using induction_choice with
  | var i => exact fun h => decide_eq_true (fun hi => h i hi (head_wins i))
  | choice q s t hs ht =>
    intro h
    by_contra hn
    have both (j) (hj : j ∈ G) : Quiet s j ∧ Quiet t j := by
      apply pass (h j hj)
      rw [(data j hj).1]
      apply Bool.eq_false_of_not_eq_true
      apply fun win => hn (profile_mono r (tail j) (outside G) (fun i hi => decide_eq_true (fun hmem => ?_)) _ win)
      rw [(data j hj).2 i hmem] at hi
      contradiction
    simp [profile_choice, hs (fun j hj => (both j hj).1), ht (fun j hj => (both j hj).2)] at hn

private theorem incompatible {t : Word} {A B D : Input → Bool} (ha : profile 0 A t = true)
    (hb : profile 1 B t = true) (hd : profile 2 D t = true)
    (empty : ∀ i, (A i && B i && D i) = false) : False := by
  let F : Fin 3 → Input → Bool := ![A,B,D]
  have hp (r : Fin 3) : profile r (F r) t = true := by fin_cases r <;> assumption
  obtain ⟨i, hi⟩ := profile_common_source id Function.injective_id F t hp
  have hA : A i = true := hi 0
  have hB : B i = true := hi 1
  have hD : D i = true := hi 2
  simpa [hA,hB,hD] using empty i

private theorem loses_subset {t : Word} (B : Input → Bool)
    (sub : ∀ i, B i = true → positiveTail i = true) (hn : profile 2 positiveTail t = false) :
    profile 2 B t = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hw
  rw [show profile 2 positiveTail t = true from profile_mono _ _ _ sub t hw] at hn
  contradiction

/-- A surviving positive and negative profile at d pass jointly to one
child whenever every constrained row takes union. -/
private theorem no_gap (R : Finset Input) (D : Input → Bool)
    (leaf : ∀ i, D i = true → positiveTail i = false → i ∈ R)
    (noAtom : ∀ t : Word, Safe t R → profile 2 D t = true → profile 2 positiveTail t = false →
      ∀ j ∈ R, profile (owner j) (tail j) t = false)
    (t : Word) (safe : Safe t R) (win : profile 2 D t = true) (loss : profile 2 positiveTail t = false) :
    False := by
  induction t using induction_choice with
  | var i => exact safe i (leaf i win loss) (head_wins i)
  | choice q s t ihs iht =>
    have child (j) (hj : j ∈ R) := pass (safe j hj) (noAtom _ safe win loss j hj)
    have left := ihs (fun j hj => (child j hj).1)
    have right := iht (fun j hj => (child j hj).2)
    by_cases he : q = 2
    · simp only [profile_choice,ite_eq_left he,Bool.or_eq_true,Bool.or_eq_false_iff] at win loss
      exact win.elim (fun a => left a loss.1) (fun a => right a loss.2)
    · simp only [profile_choice,ite_eq_right he,Bool.and_eq_true] at win
      cases hs : profile 2 positiveTail s with
      | false => exact left win.1 hs
      | true => exact right win.2 (by simpa [profile_choice,he,hs] using loss)

private abbrev zRows : Finset Input := {.w,.a,.b}
private abbrev yRows : Finset Input := {.x,.z,.w,.a,.b}

private theorem no_z_gap (t : Word) (safe : Safe t zRows) (win : profile 2 (tail .z) t = true)
    (loss : profile 2 positiveTail t = false) : False := by
  apply no_gap zRows (tail .z) (by decide) _ t safe win loss
  intro e he hz hl j hj
  have ha := group_veto e 0 {.a} (by decide) (by decide) he
  have hb := group_veto e 1 {.b} (by decide) (by decide) he
  cases j with
  | x | y | z => simp [zRows] at hj
  | w => exact loses_subset _ (by decide) hl
  | a => exact Bool.eq_false_of_not_eq_true fun h => incompatible h hb hz (by decide)
  | b => exact Bool.eq_false_of_not_eq_true fun h => incompatible ha h hz (by decide)

private theorem no_y_gap (t : Word) (safe : Safe t yRows) (win : profile 2 (tail .y) t = true)
    (loss : profile 2 positiveTail t = false) : False := by
  apply no_gap yRows (tail .y) (by decide) _ t safe win loss
  intro e he hy hl j hj
  have ha := group_veto e 0 {.a} (by decide) (by decide) he
  have hb := group_veto e 1 {.b} (by decide) (by decide) he
  have hdx := group_veto e 2 {.x,.z} (by decide) (by decide) he
  cases j with
  | y => simp [yRows] at hj
  | x | w => exact loses_subset _ (by decide) hl
  | z => exact Bool.eq_false_of_not_eq_true fun h =>
      no_z_gap e (fun j hj => he j ((by decide : zRows ⊆ yRows) hj)) h hl
  | a => exact Bool.eq_false_of_not_eq_true fun h => incompatible h hb hdx (by decide)
  | b => exact Bool.eq_false_of_not_eq_true fun h => incompatible ha h hy (by decide)

/-- The six losses force the d-singleton even when only y, z and B are
posted there. -/
theorem forced_profile (t : Equational.Term (Equational.CoreSymbol (Fin 3)) Input)
    (quiet : ∀ j, observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val) :
    profile 2 positiveTail t = true := by
  change ∀ j, Quiet t j at quiet
  induction t using induction_choice with
  | var i => exact (quiet i (head_wins i)).elim
  | choice q s t ihs iht =>
    by_contra hn
    have hl := Bool.eq_false_of_not_eq_true hn
    let e := choiceTerm q s t
    have safe : Safe e Finset.univ := fun j _ => quiet j
    have ha := group_veto e 0 {.a} (by decide) (by decide) safe
    have hb := group_veto e 1 {.b} (by decide) (by decide) safe
    have hdx := group_veto e 2 {.x,.z} (by decide) (by decide) safe
    have hdy := group_veto e 2 {.y,.z} (by decide) (by decide) safe
    have child (j) : Quiet s j ∧ Quiet t j := by
      apply pass (quiet j)
      cases j with
      | x | w => exact loses_subset _ (by decide) hl
      | z => exact Bool.eq_false_of_not_eq_true fun h => no_z_gap e (fun j _ => quiet j) h hl
      | y => exact Bool.eq_false_of_not_eq_true fun h => no_y_gap e (fun j _ => quiet j) h hl
      | a => exact Bool.eq_false_of_not_eq_true fun h => incompatible h hb hdx (by decide)
      | b => exact Bool.eq_false_of_not_eq_true fun h => incompatible ha h hdy (by decide)
    simp [profile_choice,ihs (fun j => (child j).1),iht (fun j => (child j).2)] at hl

/-- No core word can omit the marked winners on all six losses and retain
A when just y, z and B are posted at d. -/
theorem no_core_witness (t : Equational.Term (Equational.CoreSymbol (Fin 3)) Input)
    (quiet : ∀ j, observer (owner j) ∉ (t.realize (values j (owner j) (tail j))).val) :
    observer 2 ∉ (t.realize (values .a 2 positiveTail)).val := by
  have he := (pure_atom (Function.Embedding.refl _) (observer 2) t .a 2 (owner_ne_observer 2)
    2 positiveTail rfl (owner_ne_observer 2)).mpr ⟨rfl,forced_profile t quiet⟩
  unfold values
  rw [he]
  exact fun hm => owner_ne_observer 2 hm.symm

end ThreeOwners
end KFOL.Core.MonochromaticCutObstruction
