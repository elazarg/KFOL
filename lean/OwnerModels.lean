/- Four-state completeness for guarded owned choice. The three-state
obstruction is a finite certificate; reduction of arbitrary smaller
generators to this certificate uses the published order-algebra theorem. -/
import OwnerFragments
set_option autoImplicit false
namespace MinimalChoice.OwnerFragments

inductive Four where
  | owner | other | ambiguous | winning
  deriving DecidableEq, Repr

def Four.reset (x y : Four) : Four :=
  if y = .ambiguous ∧ x = .winning then .winning else y

def Four.h (x y z : Four) : Four :=
  if x = .ambiguous then
    if y ≠ .owner ∧ z ≠ .owner ∧ (y = .winning ∨ z = .winning)
      then .winning else .ambiguous
  else x

def View.four : View → Four
  | .ownerAtom => .owner
  | .otherAtom => .other
  | .otherAmbiguous => .ambiguous
  | .seenAtom | .seenAmbiguous => .winning

def Four.embed : Four → View
  | .owner => .ownerAtom
  | .other => .otherAtom
  | .ambiguous => .otherAmbiguous
  | .winning => .seenAmbiguous

theorem Four.retract (x : Four) : x.embed.four = x := by cases x <;> rfl
theorem View.four_reset (x y : View) : (x.reset y).four = x.four.reset y.four := by
  cases x <;> cases y <;> decide
theorem View.four_h (x y z : View) : (View.h x y z).four = Four.h x.four y.four z.four := by
  cases x <;> cases y <;> cases z <;> decide
theorem Four.embed_reset (x y : Four) : (x.reset y).embed = x.embed.reset y.embed := by
  cases x <;> cases y <;> decide
theorem Four.embed_h (x y z : Four) : (Four.h x y z).embed = View.h x.embed y.embed z.embed := by
  cases x <;> cases y <;> cases z <;> decide
theorem View.four_seen (x : View) : x.four = .winning ↔ x.Seen := by cases x <;> decide

def Term.fourDenote {α β : Type} (v : β → Four) : Term α β → Four
  | .input j => v j
  | .reset l r => (l.fourDenote v).reset (r.fourDenote v)
  | .h _ x y z => Four.h (x.fourDenote v) (y.fourDenote v) (z.fourDenote v)

theorem Term.four_correct {α β : Type} (t : Term α β) (v : β → View) :
    (t.viewDenote v).four = t.fourDenote (fun j => (v j).four) := by
  induction t with
  | input j => rfl
  | reset l r hl hr => simp only [viewDenote, fourDenote, View.four_reset, hl, hr]
  | h a x y z hx hy hz => simp only [viewDenote, fourDenote, View.four_h, hx, hy, hz]

theorem Term.embed_correct {α β : Type} (t : Term α β) (v : β → Four) :
    (t.fourDenote v).embed = t.viewDenote (fun j => (v j).embed) := by
  induction t with
  | input j => rfl
  | reset l r hl hr => simp only [viewDenote, fourDenote, Four.embed_reset, hl, hr]
  | h a x y z hx hy hz => simp only [viewDenote, fourDenote, Four.embed_h, hx, hy, hz]

theorem Term.four_element_complete {α β : Type} (three : Three α)
    (left right : Term α β) (owner outsider : α) (ho : outsider ≠ owner)
    (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    (∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v) ↔
      ∀ w, left.fourDenote w = right.fourDenote w := by
  constructor
  · intro he w
    have hh := (left.five_element_complete three right owner outsider ho hl hr).mp he
      (fun j => (w j).embed)
    have hh' := congrArg View.four hh
    simpa only [left.four_correct, right.four_correct, Four.retract] using hh'
  · intro he
    obtain ⟨background, hbo, hbk⟩ := third_outside (three_others three) owner outsider
    rw [left.single_table_equation_iff three right owner outsider ho hl hr]
    have ll := left.owners_mono _ (fun r => r = outsider ∨ r = owner) hl (fun _ h => Or.inr h)
    have rr := right.owners_mono _ (fun r => r = outsider ∨ r = owner) hr (fun _ h => Or.inr h)
    apply (left.observation_equation_iff right outsider owner background ho
      (Ne.symm hbk) (Ne.symm hbo) ll rr).mpr
    intro v _
    have hh := he (fun j => (view owner outsider (v j)).four)
    rw [← left.four_correct, ← right.four_correct,
      ← left.view_correct owner outsider ho hl, ← right.view_correct owner outsider ho hr] at hh
    rw [← view_seen owner outsider ho (left.denote v),
      ← view_seen owner outsider ho (right.denote v), ← View.four_seen, ← View.four_seen, hh]

theorem Four.conservative (x y z : Four) :
    (x.reset y = x ∨ x.reset y = y) ∧
      (Four.h x y z = x ∨ Four.h x y z = y ∨ Four.h x y z = z) := by
  cases x <;> cases y <;> cases z <;> decide

/-- Every nonassociative three-element reset reduct is the known chain.
Here is the remaining obstruction, independently of that external step. -/
def chainReset (x y : Fin 3) : Fin 3 := if y = 1 then if x = 2 then 2 else 1 else y
def MinorLaws (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y c, h x y y = chainReset y x ∧
    h y y c = chainReset c y ∧ h x y x = chainReset y x
def FirstLaw (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y c, chainReset (h x y c) (chainReset (chainReset c y) x) =
    chainReset (chainReset c y) x
def SecondLaw (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y c, chainReset (chainReset c x) (h x y c) = h x y c

theorem three_absorption_bounds (h : Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (ha : ∀ x y z, chainReset (h x y z) x = h x y z ∧
      chainReset x (h x y z) = h x y z) :
    (∀ y z, h 0 y z = 0) ∧ (∀ y z, h 2 y z = 2) ∧
      (∀ y z, h 1 y z = 1 ∨ h 1 y z = 2) := by
  refine ⟨fun y z => ?_, (fun y z => ?_), fun y z => ?_⟩
  · have hh := (ha 0 y z).1
    simpa [chainReset] using hh.symm
  · have hh := ha 2 y z
    by_cases he : h 2 y z = 1
    · simp [chainReset, he] at hh
    · simpa [chainReset, he] using hh.1.symm
  · have hh := (ha 1 y z).1
    simp only [chainReset, ↓reduceIte] at hh
    split at hh <;> omega

theorem three_state_obstruction (h : Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (hz : ∀ y z, h 0 y z = 0) (ht : ∀ y z, h 2 y z = 2)
    (hu : ∀ y z, h 1 y z = 1 ∨ h 1 y z = 2) (hm : MinorLaws h) :
    FirstLaw h ∨ SecondLaw h := by
  have cases3 (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hd (x y : Fin 3) := (hm x y y).1
  have hl (y c : Fin 3) := (hm y y c).2.1
  have hr (x y : Fin 3) := (hm x y x).2.2
  by_cases he : h 1 0 2 = 1
  · left
    intro x y c
    rcases cases3 x with rfl | rfl | rfl <;>
      rcases cases3 y with rfl | rfl | rfl <;>
      rcases cases3 c with rfl | rfl | rfl <;>
      simp_all [chainReset]
  · have he' : h 1 0 2 = 2 := (hu 0 2).resolve_left he
    right
    intro x y c
    rcases cases3 x with rfl | rfl | rfl <;>
      rcases cases3 y with rfl | rfl | rfl <;>
      rcases cases3 c with rfl | rfl | rfl <;>
      simp_all [chainReset]

theorem Four.required_nonidentities :
    (∃ x y c, (Four.h x y c).reset ((c.reset y).reset x) ≠ (c.reset y).reset x) ∧
    (∃ x y c, (c.reset x).reset (Four.h x y c) ≠ Four.h x y c) := by
  exact ⟨⟨.ambiguous, .other, .winning, by decide⟩,
    ⟨.ambiguous, .owner, .winning, by decide⟩⟩

theorem Four.generator_identities (x y z : Four) :
    (Four.h x y z).reset x = Four.h x y z ∧
    x.reset (Four.h x y z) = Four.h x y z ∧
    Four.h x y y = y.reset x ∧ Four.h y y z = z.reset y ∧
    Four.h x y x = y.reset x := by
  cases x <;> cases y <;> cases z <;> decide

end MinimalChoice.OwnerFragments
#print axioms MinimalChoice.OwnerFragments.Term.four_element_complete
#print axioms MinimalChoice.OwnerFragments.three_state_obstruction
