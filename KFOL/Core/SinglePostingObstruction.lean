module

public import KFOL.Core.MonochromaticCutObstruction
import Mathlib.Tactic.FinCases

/-! # A single posting forced by seven monochromatic losses -/

@[expose] public section
namespace KFOL.Core.SinglePostingObstruction

open MonochromaticCutObstruction (pureProbe pure_atom pass_row)
open MonochromaticCutObstruction.ThreeOwners (observer)
attribute [local instance] Equational.coreStructure

inductive Input | a | a' | x | b | y | b' | z deriving DecidableEq

instance : Fintype Input := ⟨{.a,.a',.x,.b,.y,.b',.z}, by intro i; cases i <;> simp⟩

/-- The three distinguished owners are α, β and d. -/
def owner : Input → Fin 3
  | .a | .a' => 0 | .b | .b' => 1 | _ => 2

def tail : Input → Input → Bool
  | .a, .x | .a, .b | .a, .b' | .a, .z => true
  | .a', .b | .a', .b' | .a', .z => true
  | .x, .a | .x, .b | .x, .y => true
  | .b, .a | .b, .a' | .b, .y | .b, .z => true
  | .y, .a' | .y, .x | .y, .b => true
  | .b', .a | .b', .x | .b', .z => true
  | .z, .a | .z, .b' => true
  | _, _ => false

/-- The only same-owner edges are x→y and y→x. -/
theorem same_owner_edges :
    ∀ i j, owner i = owner j ∧ tail i j = true ↔
      (i = .x ∧ j = .y) ∨ (i = .y ∧ j = .x) := by decide

set_option maxRecDepth 4096 in
/-- Every consistent cut enclosing any edge already contains the unique
monochromatic two-cycle, regardless of how many colors occur outside. -/
theorem compatible_cut_contains_pair :
    ∀ H : Finset Input,
      (∀ k ∉ H, ∀ i ∈ H, ∀ j ∈ H, tail i k = true → tail j k = true → owner i = owner j) →
      (∃ i ∈ H, ∃ j ∈ H, tail i j = true) → .x ∈ H ∧ .y ∈ H := by decide

variable {Role : Type*} [DecidableEq Role] (three : Fin 3 ↪ Role)

/-- The canonical probe posting precisely T at the indicated owner and
marking j at a different observer. -/
noncomputable def values (j : Input) (r : Fin 3) (T : Input → Bool) : Input → WinnerSet Role :=
  pureProbe three (three (observer r)) j (three r)
    (three.injective.ne (MonochromaticCutObstruction.ThreeOwners.owner_ne_observer r)) T

private abbrev Word (Role : Type*) := Equational.Term (Equational.CoreSymbol Role) Input
private def Quiet (t : Word Role) (j : Input) :=
  three (observer (owner j)) ∉ (t.realize (values three j (owner j) (tail j))).val

private abbrev Safe (t : Word Role) (R : Finset Input) := ∀ j ∈ R, Quiet three t j

omit [DecidableEq Role] in
private theorem head_wins (j : Input) :
    three (observer (owner j)) ∈ (values three j (owner j) (tail j) j).val :=
  (Sources.mem_probe_iff _ _ _ _ _).2 rfl

private theorem pass {s t : Word Role} {q : Role} {j : Input} (hq : Quiet three (choiceTerm q s t) j)
    (hn : profile (three (owner j)) (tail j) (choiceTerm q s t) = false) :
    Quiet three s j ∧ Quiet three t j :=
  pass_row three j _ _ _ _ ((by decide : ∀ j, tail j j = false) j) hq hn

private def outside (G : Finset Input) (i : Input) := decide (i ∉ G)

/-- A group of same-owner heads with no internal posting forces one
positive coalition excluding the whole group. -/
private theorem veto {R : Finset Input} (t : Word Role) (r : Fin 3) (G : Finset Input)
    (sub : G ⊆ R) (data : ∀ j ∈ G, owner j = r ∧ ∀ i ∈ G, tail j i = false)
    (safe : Safe three t R) : profile (three r) (outside G) t = true := by
  suffices aux : ∀ t : Word Role, Safe three t G → profile (three r) (outside G) t = true from
    aux t (fun j hj => safe j (sub hj))
  intro e
  induction e using induction_choice with
  | var i => exact fun h => decide_eq_true (fun hi => h i hi (head_wins three i))
  | choice q s t hs ht =>
    intro h
    by_contra hn
    have both (j) (hj : j ∈ G) : Quiet three s j ∧ Quiet three t j := by
      apply pass three (h j hj)
      rw [(data j hj).1]
      apply Bool.eq_false_of_not_eq_true
      intro win
      apply hn (profile_mono _ (tail j) (outside G) (fun i hi => decide_eq_true (fun hmem => ?_)) _ win)
      rw [(data j hj).2 i hmem] at hi
      contradiction
    simp [profile_choice,hs (fun j hj => (both j hj).1),ht (fun j hj => (both j hj).2)] at hn

private theorem incompatible {t : Word Role} {A B D : Input → Bool}
    (ha : profile (three 0) A t = true) (hb : profile (three 1) B t = true)
    (hd : profile (three 2) D t = true) (empty : ∀ i, (A i && B i && D i) = false) : False := by
  let F : Fin 3 → Input → Bool := ![A,B,D]
  have hp (r : Fin 3) : profile (three r) (F r) t = true := by fin_cases r <;> assumption
  obtain ⟨i,hi⟩ := profile_common_source three three.injective F t hp
  have a : A i = true := hi 0
  have b : B i = true := hi 1
  have d : D i = true := hi 2
  simpa [a,b,d] using empty i

/-- Each of these profile requests descends to at least one child. -/
private inductive Request
  | loss | gap (h : Input) | pair

private def Request.accepts (v : Fin 3 → (Input → Bool) → Bool) : Request → Prop
  | .loss => v 2 (fun i => decide (i = .x)) = false
  | .gap h => v 2 (tail h) = true ∧ v 2 (fun i => decide (i = .x)) = false
  | .pair => v 1 (tail .b) = true ∧ v 2 (tail .x) = true

private abbrev Meets (t : Word Role) (p : Request) := p.accepts (fun r A => profile (three r) A t)

private theorem inherits (p : Request) (q : Role) (s t : Word Role)
    (h : Meets three (choiceTerm q s t) p) : Meets three s p ∨ Meets three t p := by
  have ne : three 1 ≠ three 2 := three.injective.ne (by decide)
  cases p with
  | loss =>
    by_cases hd : q = three 2 <;> simp only [Meets,Request.accepts,profile_choice,hd,
      ite_true,ite_false,Bool.or_eq_false_iff,Bool.and_eq_false_imp] at h ⊢
    · exact Or.inl h.1
    · cases hs : profile (three 2) (fun i : Input => decide (i = .x)) s with
      | false => exact Or.inl rfl
      | true => exact Or.inr (by simpa [hs] using h)
  | gap j =>
    by_cases hd : q = three 2
    · simp only [Meets,Request.accepts,profile_choice,ite_eq_left hd,
        Bool.or_eq_true,Bool.or_eq_false_iff] at h ⊢
      exact h.1.elim (fun a => Or.inl ⟨a,h.2.1⟩) (fun a => Or.inr ⟨a,h.2.2⟩)
    · simp only [Meets,Request.accepts,profile_choice,ite_eq_right hd,Bool.and_eq_true] at h ⊢
      cases hs : profile (three 2) (fun i : Input => decide (i = .x)) s with
      | false => exact Or.inl ⟨h.1.1,rfl⟩
      | true => exact Or.inr ⟨h.1.2,by simpa [hs] using h.2⟩
  | pair =>
    by_cases hb : q = three 1 <;> by_cases hd : q = three 2
    · exact (ne (hb.symm.trans hd)).elim
    all_goals simp only [Meets,Request.accepts,profile_choice,hb,hd,ite_true,ite_false,
      ne,ne.symm,Bool.or_eq_true,Bool.and_eq_true] at h ⊢
    all_goals tauto

/-- Descent on a quiet budget whose rows cannot absorb would reach a
projection violating the loss at its own head. -/
private theorem exclude (R : Finset Input) (p : Request)
    (leaves : ∀ i : Input, p.accepts (fun _ A => A i) → i ∈ R)
    (noAtom : ∀ t : Word Role, Safe three t R → Meets three t p →
      ∀ j ∈ R, profile (three (owner j)) (tail j) t = false)
    (t : Word Role) (safe : Safe three t R) (w : Meets three t p) : False := by
  induction t using induction_choice with
  | var i => exact safe i (leaves i w) (head_wins three i)
  | choice q s t hs ht =>
    have child (j) (hj : j ∈ R) := pass three (safe j hj) (noAtom _ safe w j hj)
    exact (inherits three p q s t w).elim (hs (fun j hj => (child j hj).1))
      (ht (fun j hj => (child j hj).2))

private abbrev zRows : Finset Input := {.a,.b'}
private abbrev yRows : Finset Input := {.a',.b}
private abbrev pairRows : Finset Input := {.a,.a',.y}
private abbrev xRows : Finset Input := {.a,.a',.b,.y}

private theorem no_z (t : Word Role) (safe : Safe three t zRows) (w : Meets three t (.gap .z)) :
    False := by
  apply exclude three zRows (.gap .z) (by simp only [Request.accepts]; decide) _ t safe w
  intro e h win j hj
  have a := veto three e 0 {.a} (by decide) (by decide) h
  have b := veto three e 1 {.b'} (by decide) (by decide) h
  cases j with
  | a => exact Bool.eq_false_of_not_eq_true fun v => incompatible three v b win.1 (by decide)
  | b' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three a v win.1 (by decide)
  | _ => simp [zRows] at hj

private theorem no_y (t : Word Role) (safe : Safe three t yRows) (w : Meets three t (.gap .y)) :
    False := by
  apply exclude three yRows (.gap .y) (by simp only [Request.accepts]; decide) _ t safe w
  intro e h win j hj
  have a := veto three e 0 {.a'} (by decide) (by decide) h
  have b := veto three e 1 {.b} (by decide) (by decide) h
  cases j with
  | a' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three v b win.1 (by decide)
  | b => exact Bool.eq_false_of_not_eq_true fun v => incompatible three a v win.1 (by decide)
  | _ => simp [yRows] at hj

private theorem no_pair (t : Word Role) (safe : Safe three t pairRows) (w : Meets three t .pair) :
    False := by
  apply exclude three pairRows .pair (by simp only [Request.accepts]; decide) _ t safe w
  intro e h win j hj
  have a := veto three e 0 {.a'} (by decide) (by decide) h
  cases j with
  | a | a' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three v win.1 win.2 (by decide)
  | y => exact Bool.eq_false_of_not_eq_true fun v => incompatible three a win.1 v (by decide)
  | _ => simp [pairRows] at hj

private theorem no_x (t : Word Role) (safe : Safe three t xRows) (w : Meets three t (.gap .x)) :
    False := by
  apply exclude three xRows (.gap .x) (by simp only [Request.accepts]; decide) _ t safe w
  intro e h win j hj
  have b := veto three e 1 {.b} (by decide) (by decide) h
  cases j with
  | a | a' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three v b win.1 (by decide)
  | b => exact Bool.eq_false_of_not_eq_true fun v =>
      no_pair three e (fun j hj => h j ((by decide : pairRows ⊆ xRows) hj)) ⟨v,win.1⟩
  | y => exact Bool.eq_false_of_not_eq_true fun v =>
      no_y three e (fun j hj => h j ((by decide : yRows ⊆ xRows) hj)) ⟨v,win.2⟩
  | _ => simp [xRows] at hj

/-- Every core word satisfying the seven losses wins d's singleton test
on the one-element coalition {x}, for any ambient set of at least three owners. -/
theorem forced_profile (t : Equational.Term (Equational.CoreSymbol Role) Input)
    (quiet : ∀ j, three (observer (owner j)) ∉ (t.realize (values three j (owner j) (tail j))).val) :
    profile (three 2) (fun i : Input => decide (i = .x)) t = true := by
  by_contra hn
  apply exclude three Finset.univ .loss (by simp) _ t (fun j _ => quiet j) (Bool.eq_false_of_not_eq_true hn)
  intro e h loss j _
  have a := veto three e 0 {.a,.a'} (by decide) (by decide) h
  have b := veto three e 1 {.b,.b'} (by decide) (by decide) h
  have dx := veto three e 2 {.x,.z} (by decide) (by decide) h
  have dy := veto three e 2 {.y,.z} (by decide) (by decide) h
  cases j with
  | a | a' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three v b dx (by decide)
  | b => exact Bool.eq_false_of_not_eq_true fun v => incompatible three a v dy (by decide)
  | b' => exact Bool.eq_false_of_not_eq_true fun v => incompatible three a v dx (by decide)
  | x => exact Bool.eq_false_of_not_eq_true fun v => no_x three e (fun j _ => h j (Finset.mem_univ j)) ⟨v,loss⟩
  | y => exact Bool.eq_false_of_not_eq_true fun v => no_y three e (fun j _ => h j (Finset.mem_univ j)) ⟨v,loss⟩
  | z => exact Bool.eq_false_of_not_eq_true fun v => no_z three e (fun j _ => h j (Finset.mem_univ j)) ⟨v,loss⟩

/-- At the prescribed positive observation, the single posting x:d
already absorbs the marked input A. -/
theorem no_core_witness (t : Equational.Term (Equational.CoreSymbol Role) Input)
    (quiet : ∀ j, three (observer (owner j)) ∉ (t.realize (values three j (owner j) (tail j))).val) :
    three (observer 2) ∉ (t.realize (values three .a 2 (fun i => decide (i = .x)))).val := by
  have ne := three.injective.ne (MonochromaticCutObstruction.ThreeOwners.owner_ne_observer 2)
  have he := (pure_atom three (three (observer 2)) t .a (three 2) ne (three 2)
    (fun i => decide (i = .x)) rfl ne).mpr ⟨rfl,forced_profile three t quiet⟩
  unfold values
  rw [he]
  exact fun hm => ne hm.symm

end KFOL.Core.SinglePostingObstruction
