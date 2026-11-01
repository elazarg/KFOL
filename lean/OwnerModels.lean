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

/-- On the three-state subalgebra without the owner atom, H is a reset term.
This is the finite certificate used to lift every reset model. -/
theorem Four.owner_free_h (x y z : Four)
    (hx : x ≠ .owner) (hy : y ≠ .owner) (hz : z ≠ .owner) :
    Four.h x y z = (y.reset x).reset (z.reset x) := by
  cases x <;> cases y <;> cases z <;> simp_all [Four.h, Four.reset]

theorem Four.owner_free_closed (x y z : Four)
    (hx : x ≠ .owner) (hy : y ≠ .owner) (hz : z ≠ .owner) :
    x.reset y ≠ .owner ∧ Four.h x y z ≠ .owner := by
  cases x <;> cases y <;> cases z <;> simp_all [Four.h, Four.reset]

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

/-- A valid four-variable identity that cannot follow from the three-variable
theory. The countermodel and the generic transfer proof follow below. -/
theorem Four.root_expansion (u r y z : Four) :
    Four.h (u.reset r) y z = (u.reset r).reset (Four.h r y z) := by
  cases u <;> cases r <;> cases y <;> cases z <;> decide

/-- Soundness certificates for the finite presentation within conservative
algebras. Completeness in that class is a written guard-threshold proof;
these identities are not asserted to form a basis over arbitrary algebras. -/
theorem Four.h_symmetry (x y z : Four) : Four.h x y z = Four.h x z y := by
  cases x <;> cases y <;> cases z <;> decide

theorem Four.h_common_root (x y z : Four) :
    Four.h x (y.reset x) (z.reset x) = (y.reset x).reset (z.reset x) := by
  cases x <;> cases y <;> cases z <;> decide

theorem Four.h_common_ancestor (x y z : Four) :
    Four.h x ((z.reset y).reset x) y = (z.reset y).reset x := by
  cases x <;> cases y <;> cases z <;> decide

theorem Four.h_split (r u y z : Four) :
    Four.h r (u.reset r) (y.reset z) =
      (Four.h r (u.reset r) z).reset ((y.reset z).reset r) := by
  cases r <;> cases u <;> cases y <;> cases z <;> decide

theorem Four.h_linear (r u y z : Four) :
    Four.h r ((u.reset r).reset (y.reset r)) z =
      (Four.h r (u.reset r) z).reset (Four.h r (y.reset r) z) := by
  cases r <;> cases u <;> cases y <;> cases z <;> decide

theorem Four.h_reroot (r y u z : Four) :
    (Four.h y u z).reset r = ((Four.h r u z).reset y).reset r := by
  cases r <;> cases y <;> cases u <;> cases z <;> decide

theorem Four.h_insert_root (x y z : Four) :
    Four.h x y z = Four.h x (x.reset y) z := by
  cases x <;> cases y <;> cases z <;> decide

namespace PresentationObstruction

inductive Carrier where
  | top | p | q | r
  deriving DecidableEq

def reset (x y : Carrier) : Carrier := if x = y then x else .top

def h (x y z : Carrier) : Carrier :=
  if x = .r ∧ ((y = .p ∧ z = .q) ∨ (y = .q ∧ z = .p)) then .r
  else reset (reset x y) z

theorem reset_laws (x y z : Carrier) :
    reset x x = x ∧ reset (reset x y) x = reset y x ∧
    reset (reset x y) y = reset x y ∧
    reset x (reset (reset x y) z) = reset x (reset y z) ∧
    reset (reset (reset x y) z) y = reset (reset x z) y ∧
    reset x (reset y z) = reset y (reset x z) := by
  cases x <;> cases y <;> cases z <;> decide

theorem small_h_laws (x y z : Carrier) :
    h x y z = h x z y ∧ h x y y = reset y x ∧ h x x y = reset y x ∧
    reset (h x y z) x = h x y z ∧ reset x (h x y z) = h x y z ∧
    h x (reset y x) (reset z x) = reset (reset y x) (reset z x) ∧
    h x (reset (reset z y) x) y = reset (reset z y) x := by
  cases x <;> cases y <;> cases z <;> decide

theorem root_expansion (u base y z : Carrier) :
    h (reset u base) y z = reset (reset u base) (h base y z) := by
  cases u <;> cases base <;> cases y <;> cases z <;> decide

theorem split (base u y z : Carrier) :
    h base (reset u base) (reset y z) =
      reset (h base (reset u base) z) (reset (reset y z) base) := by
  cases base <;> cases u <;> cases y <;> cases z <;> decide

theorem linear (base u y z : Carrier) :
    h base (reset (reset u base) (reset y base)) z =
      reset (h base (reset u base) z) (h base (reset y base) z) := by
  cases base <;> cases u <;> cases y <;> cases z <;> decide

theorem reroot (base y u z : Carrier) :
    reset (h y u z) base = reset (reset (h base u z) y) base := by
  cases base <;> cases y <;> cases u <;> cases z <;> decide

theorem insertion_failure : h .r .p .q ≠ h .r (reset .r .p) .q := by decide

end PresentationObstruction

namespace NonconservativeWitness

inductive Carrier where
  | low | left | right | high
  deriving DecidableEq, Repr

def reset (x y : Carrier) : Carrier :=
  if y = .low ∧ x ≠ .low then .high else y

def h (x y z : Carrier) : Carrier :=
  if x ≠ .low then x
  else if (y = .low ∧ z = .low) ∨ (y = .left ∧ z = .right) ∨
      (y = .right ∧ z = .left) then .low else .high

inductive Six where
  | low | left | right | first | second | high
  deriving DecidableEq

def embed : Six → Four × Four
  | .low => (.ambiguous, .ambiguous)
  | .left => (.winning, .owner)
  | .right => (.owner, .winning)
  | .first => (.winning, .ambiguous)
  | .second => (.ambiguous, .winning)
  | .high => (.winning, .winning)

def decode : Four × Four → Six
  | (.winning, .owner) => .left
  | (.owner, .winning) => .right
  | (.winning, .ambiguous) => .first
  | (.ambiguous, .winning) => .second
  | (.winning, .winning) => .high
  | _ => .low

def sixReset (x y : Six) : Six :=
  decode ((embed x).1.reset (embed y).1, (embed x).2.reset (embed y).2)

def sixH (x y z : Six) : Six :=
  decode (Four.h (embed x).1 (embed y).1 (embed z).1,
    Four.h (embed x).2 (embed y).2 (embed z).2)

def project : Six → Carrier
  | .low => .low | .left => .left | .right => .right
  | .first | .second | .high => .high

theorem embed_reset (x y : Six) :
    embed (sixReset x y) =
      ((embed x).1.reset (embed y).1, (embed x).2.reset (embed y).2) := by
  cases x <;> cases y <;> decide

theorem embed_h (x y z : Six) :
    embed (sixH x y z) =
      (Four.h (embed x).1 (embed y).1 (embed z).1,
        Four.h (embed x).2 (embed y).2 (embed z).2) := by
  cases x <;> cases y <;> cases z <;> decide

theorem project_reset (x y : Six) :
    project (sixReset x y) = reset (project x) (project y) := by
  cases x <;> cases y <;> decide

theorem project_h (x y z : Six) :
    project (sixH x y z) = h (project x) (project y) (project z) := by
  cases x <;> cases y <;> cases z <;> decide

theorem project_surjective (x : Carrier) : ∃ y, project y = x := by
  cases x
  · exact ⟨.low, rfl⟩
  · exact ⟨.left, rfl⟩
  · exact ⟨.right, rfl⟩
  · exact ⟨.high, rfl⟩

theorem not_conservative : reset .left .low ≠ .left ∧ reset .left .low ≠ .low := by
  decide

def collapse : Carrier → Fin 3
  | .low | .high => 0 | .left => 1 | .right => 2

theorem collapse_reset (x y : Carrier) : collapse (reset x y) = collapse y := by
  cases x <;> cases y <;> decide

theorem collapse_h (x y z : Carrier) : collapse (h x y z) = collapse x := by
  cases x <;> cases y <;> cases z <;> decide

def context (i : Fin 4) (x : Carrier) : Carrier :=
  if i = 0 then x else if i = 1 then reset x .low
  else if i = 2 then h .low x .left else h .low x .right

/-- Every unequal pair forces the proposed monolith under a unary context. -/
theorem pair_forces (x y : Carrier) (hne : x ≠ y) :
    ∃ i : Fin 4, (context i x = .low ∧ context i y = .high) ∨
      (context i x = .high ∧ context i y = .low) := by
  cases x <;> cases y <;> first | exact False.elim (hne rfl) | decide

end NonconservativeWitness

namespace BasisObstruction

inductive Carrier where
  | low | middle | high | isolated
  deriving DecidableEq, Repr

def rank : Carrier → Nat
  | .low => 0 | .middle => 1 | .high => 2 | .isolated => 3

def reset (x y : Carrier) : Carrier :=
  if x = .isolated ∨ y = .isolated then y
  else if rank x ≤ rank y then y else x

def h (x y z : Carrier) : Carrier :=
  if x = .isolated then x
  else if y = .isolated ∨ z = .isolated then
    let other := if y = .isolated then z else y
    if x = .low ∧ other = .high then .high else x
  else reset (reset x y) z

theorem conservative (x y z : Carrier) :
    (reset x y = x ∨ reset x y = y) ∧
    (h x y z = x ∨ h x y z = y ∨ h x y z = z) := by
  cases x <;> cases y <;> cases z <;> decide

/-- Each proper subset embeds in F squared. Three deletions are diagonal
copies of three-state subalgebras; the fourth is a three-element semilattice. -/
def embed : Carrier → Carrier → Four × Four
  | .isolated, .low => (.ambiguous, .ambiguous)
  | .isolated, .middle => (.winning, .ambiguous)
  | .isolated, .high => (.winning, .winning)
  | .middle, .low => (.ambiguous, .ambiguous)
  | .middle, .high => (.winning, .winning)
  | .middle, .isolated => (.other, .other)
  | .low, .middle => (.ambiguous, .ambiguous)
  | .low, .high => (.winning, .winning)
  | .low, .isolated => (.owner, .owner)
  | .high, .low => (.ambiguous, .ambiguous)
  | .high, .middle => (.winning, .winning)
  | .high, .isolated => (.owner, .owner)
  | _, _ => (.owner, .owner)

theorem embed_injective (e x y : Carrier) (hx : x ≠ e) (hy : y ≠ e)
    (he : embed e x = embed e y) : x = y := by
  cases e <;> cases x <;> cases y <;> simp_all [embed]

theorem embed_reset (e x y : Carrier) (hx : x ≠ e) (hy : y ≠ e) :
    embed e (reset x y) =
      ((embed e x).1.reset (embed e y).1, (embed e x).2.reset (embed e y).2) := by
  cases e <;> cases x <;> cases y <;>
    simp_all [embed, reset, rank, Four.reset]

theorem embed_h (e x y z : Carrier) (hx : x ≠ e) (hy : y ≠ e) (hz : z ≠ e) :
    embed e (h x y z) =
      (Four.h (embed e x).1 (embed e y).1 (embed e z).1,
       Four.h (embed e x).2 (embed e y).2 (embed e z).2) := by
  cases e <;> cases x <;> cases y <;> cases z <;>
    simp_all [embed, h, reset, rank, Four.h]

def denote {α β : Type} (v : β → Carrier) : Term α β → Carrier
  | .input j => v j
  | .reset l r => reset (denote v l) (denote v r)
  | .h _ x y z => h (denote v x) (denote v y) (denote v z)

theorem denote_ne {α β : Type} (t : Term α β) (v : β → Carrier)
    (e : Carrier) (hv : ∀ j, v j ≠ e) : denote v t ≠ e := by
  induction t with
  | input j => exact hv j
  | reset l r hl hr =>
    rcases (conservative (denote v l) (denote v r) e).1 with he | he
    · simpa only [denote, he] using hl
    · simpa only [denote, he] using hr
  | h a x y z hx hy hz =>
    rcases (conservative (denote v x) (denote v y) (denote v z)).2 with he | he | he
    · simpa only [denote, he] using hx
    · simpa only [denote, he] using hy
    · simpa only [denote, he] using hz

theorem embed_denote {α β : Type} (t : Term α β) (v : β → Carrier)
    (e : Carrier) (hv : ∀ j, v j ≠ e) :
    embed e (denote v t) =
      (t.fourDenote (fun j => (embed e (v j)).1),
       t.fourDenote (fun j => (embed e (v j)).2)) := by
  induction t with
  | input j => rfl
  | reset l r hl hr =>
    rw [denote, embed_reset e _ _ (denote_ne l v e hv) (denote_ne r v e hv), hl, hr]
    rfl
  | h a x y z hx hy hz =>
    rw [denote, embed_h e _ _ _ (denote_ne x v e hv) (denote_ne y v e hv)
      (denote_ne z v e hv), hx, hy, hz]
    rfl

theorem missing (a b c : Carrier) : ∃ e, a ≠ e ∧ b ≠ e ∧ c ≠ e := by
  cases a <;> cases b <;> cases c <;>
    first
    | exact ⟨.low, by decide⟩
    | exact ⟨.middle, by decide⟩
    | exact ⟨.high, by decide⟩
    | exact ⟨.isolated, by decide⟩

/-- The countermodel satisfies every F identity on three variables, with no
bound on the depth or size of its terms. -/
theorem three_variable_transfer {α : Type} (s t : Term α (Fin 3))
    (valid : ∀ w, s.fourDenote w = t.fourDenote w) (v : Fin 3 → Carrier) :
    denote v s = denote v t := by
  obtain ⟨e, h0, h1, h2⟩ := missing (v 0) (v 1) (v 2)
  have hv : ∀ j : Fin 3, v j ≠ e := by
    intro j
    have cases3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases cases3 with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  apply embed_injective e _ _ (denote_ne s v e hv) (denote_ne t v e hv)
  rw [embed_denote s v e hv, embed_denote t v e hv,
    valid (fun j => (embed e (v j)).1), valid (fun j => (embed e (v j)).2)]

theorem root_expansion_failure :
    h (reset .middle .low) .high .isolated ≠
      reset (reset .middle .low) (h .low .high .isolated) := by decide

end BasisObstruction

namespace FiniteBasis

/- Expanded soundness certificates for the forty-equation unrestricted basis.
The generic completeness argument is in appendix-owner-basis.tex. -/

/-- Basis equation 1: R1. -/
theorem law_R1 (r : Four) :
    (r.reset r) =
      r := by
  cases r <;> decide

/-- Basis equation 2: R2. -/
theorem law_R2 (r a : Four) :
    ((r.reset a).reset r) =
      (a.reset r) := by
  cases r <;> cases a <;> decide

/-- Basis equation 3: R3. -/
theorem law_R3 (r a : Four) :
    ((r.reset a).reset a) =
      (r.reset a) := by
  cases r <;> cases a <;> decide

/-- Basis equation 4: R4. -/
theorem law_R4 (r a b : Four) :
    (r.reset ((r.reset a).reset b)) =
      (r.reset (a.reset b)) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 5: R5. -/
theorem law_R5 (r a b : Four) :
    (((r.reset a).reset b).reset a) =
      ((r.reset b).reset a) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 6: R6. -/
theorem law_R6 (r a b : Four) :
    (r.reset (a.reset b)) =
      (a.reset (r.reset b)) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 7: h_sym. -/
theorem law_h_sym (r a b : Four) :
    (Four.h r a b) =
      (Four.h r b a) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 8: h_minor. -/
theorem law_h_minor (r a : Four) :
    (Four.h r a a) =
      (a.reset r) := by
  cases r <;> cases a <;> decide

/-- Basis equation 9: h_root. -/
theorem law_h_root (r a b : Four) :
    ((Four.h r a b).reset r) =
      (Four.h r a b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 10: h_expand. -/
theorem law_h_expand (r a b u : Four) :
    (Four.h (u.reset r) a b) =
      ((u.reset r).reset (Four.h r a b)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 11: h_split. -/
theorem law_h_split (r a b u v : Four) :
    (Four.h r (u.reset a) (v.reset b)) =
      (((Four.h r (u.reset a) b).reset r).reset ((Four.h r a (v.reset b)).reset r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> cases v <;> decide

/-- Basis equation 12: h_back. -/
theorem law_h_back (r a b u : Four) :
    (Four.h r (u.reset a) b) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 13: h_reroot. -/
theorem law_h_reroot (r a b u : Four) :
    ((Four.h a u b).reset r) =
      (((Four.h r u b).reset a).reset r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 14: h_insert. -/
theorem law_h_insert (r a b : Four) :
    (Four.h r a b) =
      (Four.h r (r.reset a) b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 15: project_join. -/
theorem law_project_join (r a u v : Four) :
    (((u.reset a).reset (v.reset a)).reset r) =
      ((((u.reset a).reset r).reset r).reset (((v.reset a).reset r).reset r)) := by
  cases r <;> cases a <;> cases u <;> cases v <;> decide

/-- Basis equation 16: reset_split. -/
theorem law_reset_split (a u v : Four) :
    (u.reset (v.reset a)) =
      ((u.reset a).reset (v.reset a)) := by
  cases a <;> cases u <;> cases v <;> decide

/-- Basis equation 17: reset_back. -/
theorem law_reset_back (r a u : Four) :
    ((u.reset a).reset r) =
      (((u.reset r).reset a).reset r) := by
  cases r <;> cases a <;> cases u <;> decide

/-- Basis equation 18: project_idem. -/
theorem law_project_idem (r u : Four) :
    ((u.reset r).reset r) =
      (u.reset r) := by
  cases r <;> cases u <;> decide

/-- Basis equation 19: root_preserve. -/
theorem law_root_preserve (r u v : Four) :
    ((u.reset (v.reset r)).reset r) =
      (u.reset (v.reset r)) := by
  cases r <;> cases u <;> cases v <;> decide

/-- Basis equation 20: F_closed. -/
theorem law_F_closed (r a b u : Four) :
    ((Four.h r ((u.reset r).reset a) b).reset r) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 21: F_join. -/
theorem law_F_join (r a b u v : Four) :
    (Four.h r ((((u.reset r).reset r).reset ((v.reset r).reset r)).reset a) b) =
      (((Four.h r ((u.reset r).reset a) b).reset r).reset ((Four.h r ((v.reset r).reset a) b).reset r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> cases v <;> decide

/-- Basis equation 22: F_contract. -/
theorem law_F_contract (r a b u : Four) :
    (((Four.h r ((u.reset r).reset a) b).reset r).reset ((((Four.h r (r.reset a) b).reset r).reset ((u.reset r).reset r)).reset r)) =
      (((Four.h r (r.reset a) b).reset r).reset ((u.reset r).reset r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 23: F_idem. -/
theorem law_F_idem (r a b u : Four) :
    (Four.h r ((Four.h r ((u.reset r).reset a) b).reset a) b) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 24: F_band. -/
theorem law_F_band (r a b c d u : Four) :
    (Four.h r ((Four.h r ((Four.h r ((u.reset r).reset a) b).reset c) d).reset a) b) =
      (Four.h r ((Four.h r ((u.reset r).reset c) d).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases c <;> cases d <;> cases u <;> decide

/-- Basis equation 25: F_Ga. -/
theorem law_F_Ga (r a b u : Four) :
    (Four.h r ((((u.reset r).reset a).reset r).reset a) b) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 26: F_Ka. -/
theorem law_F_Ka (r a b u : Four) :
    (Four.h r ((Four.h r (u.reset r) a).reset a) b) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 27: F_Kb. -/
theorem law_F_Kb (r a b u : Four) :
    (Four.h r ((Four.h r (u.reset r) b).reset a) b) =
      (Four.h r ((u.reset r).reset a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 28: F_ca. -/
theorem law_F_ca (r a b : Four) :
    (Four.h r ((a.reset r).reset a) b) =
      (Four.h r (r.reset a) b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 29: F_cb. -/
theorem law_F_cb (r a b : Four) :
    (Four.h r ((b.reset r).reset a) b) =
      (Four.h r (r.reset a) b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 30: capture. -/
theorem law_capture (r a b u : Four) :
    (((Four.h r (Four.h r ((u.reset r).reset a) b) b).reset a).reset r) =
      (((Four.h r (u.reset r) b).reset a).reset r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 31: weak_gate. -/
theorem law_weak_gate (r a b u : Four) :
    (((Four.h r ((u.reset r).reset a) b).reset a).reset r) =
      (((Four.h r (u.reset r) b).reset a).reset r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> decide

/-- Basis equation 32: terminal. -/
theorem law_terminal (r a b : Four) :
    (Four.h r (Four.h r a b) b) =
      (Four.h r (a.reset r) b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 33: terminal_bound. -/
theorem law_terminal_bound (r a b : Four) :
    (((Four.h r a b).reset r).reset ((((a.reset r).reset r).reset ((b.reset r).reset r)).reset r)) =
      (((a.reset r).reset r).reset ((b.reset r).reset r)) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 34: terminal_weak. -/
theorem law_terminal_weak (r a b : Four) :
    (((Four.h r a b).reset r).reset ((Four.h r (a.reset r) b).reset r)) =
      (Four.h r (a.reset r) b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 35: G_def. -/
theorem law_G_def (r a u : Four) :
    (((u.reset r).reset a).reset r) =
      (Four.h r ((u.reset r).reset a) a) := by
  cases r <;> cases a <;> cases u <;> decide

/-- Basis equation 36: K_def. -/
theorem law_K_def (r a u : Four) :
    (Four.h r (u.reset r) a) =
      (Four.h r ((u.reset r).reset r) a) := by
  cases r <;> cases a <;> cases u <;> decide

/-- Basis equation 37: G_zero. -/
theorem law_G_zero (r a : Four) :
    ((r.reset a).reset r) =
      (a.reset r) := by
  cases r <;> cases a <;> decide

/-- Basis equation 38: F_zero. -/
theorem law_F_zero (r a b : Four) :
    (Four.h r (r.reset a) b) =
      (Four.h r a b) := by
  cases r <;> cases a <;> cases b <;> decide

/-- Basis equation 39: G_root. -/
theorem law_G_root (r u : Four) :
    (((u.reset r).reset r).reset r) =
      (u.reset r) := by
  cases r <;> cases u <;> decide

/-- Basis equation 40: K_root. -/
theorem law_K_root (r u : Four) :
    (Four.h r (u.reset r) r) =
      (u.reset r) := by
  cases r <;> cases u <;> decide

end FiniteBasis

end MinimalChoice.OwnerFragments
#print axioms MinimalChoice.OwnerFragments.Term.four_element_complete
#print axioms MinimalChoice.OwnerFragments.three_state_obstruction
#print axioms MinimalChoice.OwnerFragments.Four.owner_free_h
#print axioms MinimalChoice.OwnerFragments.Four.owner_free_closed
#print axioms MinimalChoice.OwnerFragments.Four.root_expansion
#print axioms MinimalChoice.OwnerFragments.Four.h_split
#print axioms MinimalChoice.OwnerFragments.Four.h_linear
#print axioms MinimalChoice.OwnerFragments.Four.h_insert_root
#print axioms MinimalChoice.OwnerFragments.PresentationObstruction.split
#print axioms MinimalChoice.OwnerFragments.PresentationObstruction.linear
#print axioms MinimalChoice.OwnerFragments.PresentationObstruction.insertion_failure
#print axioms MinimalChoice.OwnerFragments.NonconservativeWitness.embed_h
#print axioms MinimalChoice.OwnerFragments.NonconservativeWitness.project_h
#print axioms MinimalChoice.OwnerFragments.NonconservativeWitness.pair_forces
#print axioms MinimalChoice.OwnerFragments.BasisObstruction.three_variable_transfer
#print axioms MinimalChoice.OwnerFragments.BasisObstruction.root_expansion_failure

#print axioms MinimalChoice.OwnerFragments.FiniteBasis.law_F_band
#print axioms MinimalChoice.OwnerFragments.FiniteBasis.law_capture
#print axioms MinimalChoice.OwnerFragments.FiniteBasis.law_weak_gate
