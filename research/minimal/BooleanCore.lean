/-
The Boolean encoding underlying the coNP-hardness reduction. These are
ordinary owned-choice terms, without a role-switch constructor. The SAT
complexity argument itself is a mathematical proof in general.tex.
-/
import Synthesis

set_option autoImplicit false
namespace MinimalChoice

def topSet {α : Type} : S α := fun _ => True

@[simp] theorem join_topSet {α : Type} (A : S α) : join A topSet = topSet := by
  funext x
  simp [join, topSet]

@[simp] theorem topSet_join {α : Type} (A : S α) : join topSet A = topSet := by
  funext x
  simp [join, topSet]

@[simp] theorem join_self {α : Type} (A : S α) : join A A = A := by
  funext x
  simp [join]

theorem topSet_ne_atom {α : Type} (r s : α) (hrs : r ≠ s) :
    topSet ≠ atom r := by
  intro he
  have hs : topSet s := True.intro
  rw [he] at hs
  exact hrs hs.symm

def boolValue {α : Type} (a : α) (b : Bool) : S α :=
  if b then atom a else topSet

theorem boolValue_injective {α : Type} (a b : α) (hab : a ≠ b) :
    Function.Injective (boolValue a) := by
  intro x y he
  cases x <;> cases y
  · rfl
  · exact False.elim (topSet_ne_atom a b hab he)
  · exact False.elim (topSet_ne_atom a b hab he.symm)
  · rfl

theorem boolean_or {α : Type} (a b : α) (hab : a ≠ b) (x y : Bool) :
    own a (boolValue a x) (boolValue a y) = boolValue a (x || y) := by
  have hn := topSet_ne_atom a b hab
  cases x <;> cases y <;> simp [boolValue, own, hn]

theorem boolean_and {α : Type} (a b : α) (hab : a ≠ b) (x y : Bool) :
    own b (boolValue a x) (boolValue a y) = boolValue a (x && y) := by
  have hn := topSet_ne_atom b a hab.symm
  have ha : atom a ≠ atom b := fun he => hab (atom_inj.mp he)
  cases x <;> cases y <;> simp [boolValue, own, hn, ha]

noncomputable def gateBit {α : Type} (a : α) (A : S α) : Bool := by
  classical
  exact decide (A = atom a)

theorem boolean_gate {α : Type} (a b : α) (hab : a ≠ b) (A : S α) :
    own a A topSet = boolValue a (gateBit a A) := by
  classical
  have hn := topSet_ne_atom a b hab
  by_cases he : A = atom a <;> simp [own, hn, he, gateBit, boolValue]

theorem gateBit_boolValue {α : Type} (a b : α) (hab : a ≠ b) (x : Bool) :
    gateBit a (boolValue a x) = x := by
  classical
  have hn := topSet_ne_atom a b hab
  cases x <;> simp [gateBit, boolValue, hn]

noncomputable def topTerm {α β : Type} (h : Three α) (roles : List α) : Term α β :=
  collect h roles (fun _ => True) (fun i => .win i) (.win h.r)

theorem denote_topTerm {α β : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (v : β → S α) :
    denote (topTerm h roles) v = topSet := by
  funext w
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    rw [topTerm, denote_collect]
    exact Or.inr ⟨w, covers w, True.intro, rfl⟩

inductive Positive (β : Type) where
  | value : Bool → Positive β
  | var : β → Positive β
  | and : Positive β → Positive β → Positive β
  | or : Positive β → Positive β → Positive β

def Positive.eval {β : Type} (f : Positive β) (v : β → Bool) : Bool :=
  match f with
  | .value b => b
  | .var i => v i
  | .and p q => p.eval v && q.eval v
  | .or p q => p.eval v || q.eval v

noncomputable def Positive.compile {α β : Type} (h : Three α) (roles : List α)
    (f : Positive β) : Term α β :=
  match f with
  | .value true => .win h.r
  | .value false => topTerm h roles
  | .var i => .node h.r (.var i) (topTerm h roles)
  | .and p q => .node h.s (p.compile h roles) (q.compile h roles)
  | .or p q => .node h.r (p.compile h roles) (q.compile h roles)

theorem Positive.compile_correct {α β : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (f : Positive β) (v : β → S α) :
    denote (f.compile h roles) v = boolValue h.r (f.eval (fun i => gateBit h.r (v i))) := by
  induction f with
  | value b => cases b <;> simp [Positive.compile, Positive.eval, boolValue, denote,
      denote_topTerm h roles covers]
  | var i =>
    simp only [Positive.compile, denote, denote_topTerm h roles covers, Positive.eval]
    exact boolean_gate h.r h.s h.rs _
  | and p q hp hq =>
    simp only [Positive.compile, denote, hp, hq, Positive.eval]
    exact boolean_and h.r h.s h.rs _ _
  | or p q hp hq =>
    simp only [Positive.compile, denote, hp, hq, Positive.eval]
    exact boolean_or h.r h.s h.rs _ _

theorem Positive.equation_embedding {α β : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (p q : Positive β) :
    (∀ v : β → S α, (∀ i, NE (v i)) →
      denote (p.compile h roles) v = denote (q.compile h roles) v) ↔
    (∀ v : β → Bool, p.eval v = q.eval v) := by
  constructor
  · intro he v
    have hne : ∀ i, NE (boolValue h.r (v i)) := by
      intro i
      cases hb : v i
      · exact ⟨h.r, True.intro⟩
      · exact atom_ne h.r
    have eq := he (fun i => boolValue h.r (v i)) hne
    rw [p.compile_correct h roles covers, q.compile_correct h roles covers] at eq
    have hg : (fun i => gateBit h.r (boolValue h.r (v i))) = v := by
      funext i
      exact gateBit_boolValue h.r h.s h.rs _
    rw [hg] at eq
    exact boolValue_injective h.r h.s h.rs eq
  · intro he v _
    rw [p.compile_correct h roles covers, q.compile_correct h roles covers, he]

end MinimalChoice

#print axioms MinimalChoice.boolean_gate
#print axioms MinimalChoice.boolean_or
#print axioms MinimalChoice.boolean_and
#print axioms MinimalChoice.Positive.compile_correct
#print axioms MinimalChoice.Positive.equation_embedding
