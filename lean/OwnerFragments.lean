/-
Exact guard semantics for reset and owner-labelled H terms. For an observer,
one other owner yields a three-status chain and a complete polynomial guard
comparison. All native operations compile to the existing full owned-choice
syntax. No constants or internal switches occur in this fragment.
-/
import FullAlgebra
import Fragments

set_option autoImplicit false
namespace MinimalChoice.OwnerFragments
open ResetCalculus

inductive Term (α β : Type) where
  | input : β → Term α β
  | reset : Term α β → Term α β → Term α β
  | h : α → Term α β → Term α β → Term α β → Term α β

def Term.root {α β : Type} : Term α β → β
  | .input j => j
  | .reset _ right => right.root
  | .h _ root _ _ => root.root

noncomputable def Term.denote {α β : Type} (v : β → S α) : Term α β → S α
  | .input j => v j
  | .reset left right => ResetCalculus.reset (left.denote v) (right.denote v)
  | .h r root left right => SmallFragments.H r (root.denote v) (left.denote v) (right.denote v)

def Term.OwnersIn {α β : Type} (P : α → Prop) : Term α β → Prop
  | .input _ => True
  | .reset left right => left.OwnersIn P ∧ right.OwnersIn P
  | .h r root left right => P r ∧ root.OwnersIn P ∧ left.OwnersIn P ∧ right.OwnersIn P

theorem reset_eq_atom {α : Type} (A B : S α) (r : α) :
    ResetCalculus.reset A B = atom r ↔ B = atom r := by
  classical
  by_cases hm : Multiple B
  · have hout := (reset_multiple A B).mpr hm
    have ha : ResetCalculus.reset A B ≠ atom r := by
      intro he
      exact not_multiple_atom r (he ▸ hout)
    have hb : B ≠ atom r := by intro he; exact not_multiple_atom r (he ▸ hm)
    simp [ha, hb]
  · simp [ResetCalculus.reset, hm]

theorem Term.multiple_iff {α β : Type} (t : Term α β) (v : β → S α) :
    Multiple (t.denote v) ↔ Multiple (v t.root) := by
  induction t with
  | input j => rfl
  | reset left right _ hr => exact (reset_multiple _ _).trans hr
  | h r root left right hx _ _ => exact (reset_multiple _ _).trans hx

theorem Term.atom_iff {α β : Type} (t : Term α β) (v : β → S α) (r : α) :
    t.denote v = atom r ↔ v t.root = atom r := by
  induction t with
  | input j => rfl
  | reset left right _ hr => exact (reset_eq_atom _ _ r).trans hr
  | h owner root left right hx _ _ => exact (reset_eq_atom _ _ r).trans hx

theorem Term.denote_ne {α β : Type} (t : Term α β) (v : β → S α)
    (hv : ∀ j, NE (v j)) : NE (t.denote v) := by
  induction t with
  | input j => exact hv j
  | reset left right _ hr => exact reset_ne _ _ hr
  | h r root left right hx _ _ => exact reset_ne _ _ hx

structure Guard (β : Type) where
  source : β
  many : List β := []
  outside : List β := []

def Guard.Holds {β : Type} (M N V : β → Prop) (g : Guard β) : Prop :=
  (∀ j ∈ g.many, M j) ∧ (∀ j ∈ g.outside, N j) ∧ V g.source

def Guard.addMany {β : Type} (j : β) (g : Guard β) : Guard β :=
  { g with many := j :: g.many }

def Guard.addOutside {β : Type} (j : β) (g : Guard β) : Guard β :=
  { g with outside := j :: g.outside }

def Eval {β : Type} (guards : List (Guard β)) (M N V : β → Prop) : Prop :=
  ∃ g ∈ guards, g.Holds M N V

theorem eval_append {β : Type} (first second : List (Guard β)) (M N V : β → Prop) :
    Eval (first ++ second) M N V ↔ Eval first M N V ∨ Eval second M N V := by
  simp [Eval, List.mem_append, or_and_right, exists_or]

theorem eval_many {β : Type} (j : β) (guards : List (Guard β)) (M N V : β → Prop) :
    Eval (guards.map (Guard.addMany j)) M N V ↔ M j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hm j (by simp [Guard.addMany]), s, hs,
      (fun i hi => hm i (by simp [Guard.addMany, hi])), hn, hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addMany j, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_, hn, hv⟩
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · exact hi ▸ hj
    · exact hm i hi

theorem eval_outside {β : Type} (j : β) (guards : List (Guard β)) (M N V : β → Prop) :
    Eval (guards.map (Guard.addOutside j)) M N V ↔ N j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hn j (by simp [Guard.addOutside]), s, hs, hm,
      (fun i hi => hn i (by simp [Guard.addOutside, hi])), hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addOutside j, List.mem_map.mpr ⟨g, hg, rfl⟩, hm, ?_, hv⟩
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · exact hi ▸ hj
    · exact hn i hi

noncomputable def Term.guards {α β : Type} (observer : α) : Term α β → List (Guard β) := by
  classical
  exact fun t => match t with
  | .input j => [⟨j, [], []⟩]
  | .reset left right => right.guards observer ++
      (left.guards observer).map (Guard.addMany right.root)
  | .h r root left right =>
      let children := left.guards observer ++ right.guards observer
      let eligible := if r = observer then children else
        (children.map (Guard.addOutside left.root)).map (Guard.addOutside right.root)
      root.guards observer ++ eligible.map (Guard.addMany root.root)

/-- The only negative tests visible to an observer concern the one other owner. -/
theorem Term.guard_semantics {α β : Type} (t : Term α β) (observer other : α)
    (ht : t.OwnersIn (fun r => r = observer ∨ r = other)) (v : β → S α) :
    t.denote v observer ↔ Eval (t.guards observer)
      (fun j => Multiple (v j)) (fun j => v j ≠ atom other) (fun j => v j observer) := by
  classical
  induction t with
  | input j => simp [denote, guards, Eval, Guard.Holds]
  | reset left right hl hr =>
    simp only [denote, guards, reset_membership, eval_append, eval_many,
      hr ht.2, hl ht.1, Term.multiple_iff]
  | h r root left right hx hl hr =>
    by_cases he : r = observer
    · subst r
      simp only [denote, SmallFragments.H, reset_membership, own_mem_owner,
        guards, ite_true, eval_append, eval_many,
        hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2, Term.multiple_iff]
    · have ho : r = other := ht.1.resolve_left he
      subst r
      simp only [denote, SmallFragments.H, reset_membership, own_mem_other other observer he,
        guards, ite_eq_right he, eval_append, eval_many, eval_outside,
        hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2, Term.multiple_iff]
      have hy := left.atom_iff v other
      have hz := right.atom_iff v other
      grind

/-- A weaker guard covers the stronger one. The source is already known
to contain the observed winner, so it cannot be the other owner's atom. -/
def Guard.Dominates {β : Type} (weak strong : Guard β) : Prop :=
  weak.source = strong.source ∧
  (∀ j ∈ weak.many, j ∈ strong.many) ∧
  (∀ j ∈ weak.outside, j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source)

def Covers {β : Type} (left right : List (Guard β)) : Prop :=
  ∀ g ∈ left, ∃ h ∈ right, h.Dominates g

theorem Guard.dominates_sound {β : Type} (weak strong : Guard β)
    (h : weak.Dominates strong) (M N V : β → Prop)
    (hmn : ∀ j, M j → N j) (hvn : ∀ j, V j → N j)
    (hs : strong.Holds M N V) : weak.Holds M N V := by
  refine ⟨fun j hj => hs.1 j (h.2.1 j hj), ?_, h.1 ▸ hs.2.2⟩
  intro j hj
  rcases h.2.2 j hj with hm | hn | he
  · exact hmn j (hs.1 j hm)
  · exact hs.2.1 j hn
  · exact he ▸ hvn strong.source hs.2.2

theorem covers_sound {β : Type} (left right : List (Guard β)) (h : Covers left right)
    (M N V : β → Prop) (hmn : ∀ j, M j → N j) (hvn : ∀ j, V j → N j) :
    Eval left M N V → Eval right M N V := by
  rintro ⟨g, hg, hs⟩
  obtain ⟨q, hq, hdom⟩ := h g hg
  exact ⟨q, hq, q.dominates_sound g hdom M N V hmn hvn hs⟩

@[simp] theorem pair_multiple {α : Type} (a b : α) :
    Multiple (join (atom a) (atom b)) ↔ a ≠ b := by
  constructor
  · intro hm he
    subst b
    have ha : join (atom a) (atom a) = atom a := by funext x; simp [join]
    exact not_multiple_atom a (ha ▸ hm)
  · intro hab
    exact ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩

@[simp] theorem pair_eq_atom {α : Type} (a b r : α) :
    join (atom a) (atom b) = atom r ↔ a = r ∧ b = r := by
  rw [join_eq_atom_iff _ _ (atom_ne a) (atom_ne b) r]
  simp only [atom_inj]

attribute [local simp] not_multiple_atom

noncomputable def minimalVal {α β : Type} (observer other background : α)
    (g : Guard β) (j : β) : S α := by
  classical
  exact if j = g.source then
      if j ∈ g.many then join (atom observer) (atom other) else atom observer
    else if j ∈ g.many then join (atom other) (atom background)
    else if j ∈ g.outside then atom background else atom other

theorem minimalVal_ne {α β : Type} (observer other background : α) (g : Guard β) (j : β) :
    NE (minimalVal observer other background g j) := by
  classical
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, NE, join, atom]

theorem minimalVal_multiple {α β : Type} (observer other background : α)
    (hko : observer ≠ other) (hob : other ≠ background) (g : Guard β) (j : β) :
    Multiple (minimalVal observer other background g j) ↔ j ∈ g.many := by
  classical
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal]

theorem minimalVal_outside {α β : Type} (observer other background : α)
    (hko : observer ≠ other) (hob : other ≠ background) (g : Guard β) (j : β) :
    minimalVal observer other background g j ≠ atom other ↔
      j ∈ g.many ∨ j ∈ g.outside ∨ j = g.source := by
  classical
  have hbo : background ≠ other := Ne.symm hob
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, atom_inj]

theorem minimalVal_marker {α β : Type} (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (g : Guard β) (j : β) :
    minimalVal observer other background g j observer ↔ j = g.source := by
  classical
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, atom, join]

theorem eval_minimalVal {α β : Type} (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (g : Guard β) (guards : List (Guard β)) :
    Eval guards (fun j => Multiple (minimalVal observer other background g j))
      (fun j => minimalVal observer other background g j ≠ atom other)
      (fun j => minimalVal observer other background g j observer) ↔
      ∃ h ∈ guards, h.Dominates g := by
  simp only [Eval, Guard.Holds, minimalVal_multiple observer other background hko hob,
    minimalVal_outside observer other background hko hob,
    minimalVal_marker observer other background hko hkb]
  constructor
  · rintro ⟨h, hh, hm, hn, hs⟩
    exact ⟨h, hh, hs, hm, hn⟩
  · rintro ⟨h, hh, hs, hm, hn⟩
    exact ⟨h, hh, hm, hn, hs⟩

/-- Guard implication is exactly pairwise coverage. Every failed coverage
test has a winner-set countervaluation over three roles and at most pairs. -/
theorem covers_iff {α β : Type} (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (left right : List (Guard β)) :
    Covers left right ↔ ∀ v : β → S α, (∀ j, NE (v j)) →
      Eval left (fun j => Multiple (v j)) (fun j => v j ≠ atom other) (fun j => v j observer) →
      Eval right (fun j => Multiple (v j)) (fun j => v j ≠ atom other) (fun j => v j observer) := by
  constructor
  · intro h v _
    apply covers_sound left right h
    · intro j hm he
      exact not_multiple_atom other (he ▸ hm)
    · intro j hj he
      rw [he] at hj
      exact hko hj
  · intro himp g hg
    let v := minimalVal observer other background g
    have hleft : Eval left (fun j => Multiple (v j)) (fun j => v j ≠ atom other)
        (fun j => v j observer) := by
      apply (eval_minimalVal observer other background hko hkb hob g left).mpr
      exact ⟨g, hg, rfl, (fun _ h => h), fun j h => Or.inr (Or.inl h)⟩
    have hright := himp v (minimalVal_ne observer other background g) hleft
    exact (eval_minimalVal observer other background hko hkb hob g right).mp hright

theorem Term.observation_implication_iff {α β : Type} (left right : Term α β)
    (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    Covers (left.guards observer) (right.guards observer) ↔
      ∀ v, (∀ j, NE (v j)) → left.denote v observer → right.denote v observer := by
  rw [covers_iff observer other background hko hkb hob]
  simp only [← left.guard_semantics observer other hl,
    ← right.guard_semantics observer other hr]

theorem Term.observation_equation_iff {α β : Type} (left right : Term α β)
    (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    (Covers (left.guards observer) (right.guards observer) ∧
      Covers (right.guards observer) (left.guards observer)) ↔
      ∀ v, (∀ j, NE (v j)) → (left.denote v observer ↔ right.denote v observer) := by
  rw [left.observation_implication_iff right observer other background hko hkb hob hl hr,
    right.observation_implication_iff left observer other background hko hkb hob hr hl]
  constructor
  · exact fun h v hv => ⟨h.1 v hv, h.2 v hv⟩
  · exact fun h => ⟨fun v hv => (h v hv).mp, fun v hv => (h v hv).mpr⟩

def Term.leaves {α β : Type} : Term α β → Nat
  | .input _ => 1
  | .reset left right => left.leaves + right.leaves
  | .h _ root left right => root.leaves + (left.leaves + right.leaves)

/-- Guard compilation never distributes a computed condition: it produces
exactly one conjunction for each variable occurrence in the original tree. -/
theorem Term.guards_length {α β : Type} (t : Term α β) (observer : α) :
    (t.guards observer).length = t.leaves := by
  classical
  induction t with
  | input j => rfl
  | reset left right hl hr => simp [guards, leaves, hl, hr, Nat.add_comm]
  | h r root left right hx hl hr =>
    by_cases he : r = observer <;> simp [guards, leaves, he, hx, hl, hr]

theorem Term.owners_mono {α β : Type} (t : Term α β) (P Q : α → Prop)
    (ht : t.OwnersIn P) (hpq : ∀ r, P r → Q r) : t.OwnersIn Q := by
  induction t with
  | input j => trivial
  | reset left right hl hr => exact ⟨hl ht.1, hr ht.2⟩
  | h r root left right hx hl hr =>
    exact ⟨hpq r ht.1, hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2⟩

theorem Term.guards_other {α β : Type} (t : Term α β) (owner first second : α)
    (ht : t.OwnersIn (fun r => r = owner)) (hf : first ≠ owner) (hs : second ≠ owner) :
    t.guards first = t.guards second := by
  classical
  induction t with
  | input j => rfl
  | reset left right hl hr => simp [guards, hl ht.1, hr ht.2]
  | h r root left right hx hl hr =>
    have he : r = owner := ht.1
    subst r
    simp [guards, Ne.symm hf, Ne.symm hs, hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2]

/-- Complete equality criterion for reset plus one fixed H operation.
Two observer tables suffice: the owner and any one other role. -/
theorem Term.one_owner_equation_iff {α β : Type} (three : Three α)
    (left right : Term α β) (owner outsider : α) (ho : outsider ≠ owner)
    (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    (∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v) ↔
      (Covers (left.guards owner) (right.guards owner) ∧
        Covers (right.guards owner) (left.guards owner)) ∧
      (Covers (left.guards outsider) (right.guards outsider) ∧
        Covers (right.guards outsider) (left.guards outsider)) := by
  have ownerL : left.OwnersIn (fun r => r = owner ∨ r = outsider) :=
    left.owners_mono _ _ hl (fun _ h => Or.inl h)
  have ownerR : right.OwnersIn (fun r => r = owner ∨ r = outsider) :=
    right.owners_mono _ _ hr (fun _ h => Or.inl h)
  have outL : left.OwnersIn (fun r => r = outsider ∨ r = owner) :=
    left.owners_mono _ _ hl (fun _ h => Or.inr h)
  have outR : right.OwnersIn (fun r => r = outsider ∨ r = owner) :=
    right.owners_mono _ _ hr (fun _ h => Or.inr h)
  obtain ⟨background, hbo, hbk⟩ := third_outside (three_others three) owner outsider
  have ownTest := left.observation_equation_iff right owner outsider background
    (Ne.symm ho) (Ne.symm hbo) (Ne.symm hbk) ownerL ownerR
  have outTest := left.observation_equation_iff right outsider owner background
    ho (Ne.symm hbk) (Ne.symm hbo) outL outR
  constructor
  · intro he
    exact ⟨ownTest.mpr (fun v hv => by rw [he v hv]),
      outTest.mpr (fun v hv => by rw [he v hv])⟩
  · rintro ⟨hown, hout⟩ v hv
    funext k
    apply propext
    by_cases hk : k = owner
    · subst k
      exact ownTest.mp hown v hv
    · have lallowed := left.owners_mono _ (fun r => r = k ∨ r = owner)
        hl (fun _ h => Or.inr h)
      have rallowed := right.owners_mono _ (fun r => r = k ∨ r = owner)
        hr (fun _ h => Or.inr h)
      obtain ⟨b, hbk', hbo'⟩ := third_outside (three_others three) k owner
      have kt := left.observation_equation_iff right k owner b hk
        (Ne.symm hbk') (Ne.symm hbo') lallowed rallowed
      have htables : Covers (left.guards k) (right.guards k) ∧
          Covers (right.guards k) (left.guards k) := by
        rw [left.guards_other owner k outsider hl hk ho,
          right.guards_other owner k outsider hr hk ho]
        exact hout
      exact kt.mp htables v hv

def Term.compile {α β : Type} (three : Three α) (roles : List α) : Term α β → FullTerm α β
  | .input j => .var j
  | .reset left right => (left.compile three roles).resetWith three roles (right.compile three roles)
  | .h r root left right =>
      (FullTerm.node r (left.compile three roles) (right.compile three roles)).resetWith
        three roles (root.compile three roles)

/-- The native fragment has the exact previously formalized owned-choice
meaning, including its SPE realization; the grammar is not a second model. -/
theorem Term.compile_correct {α β : Type} (three : Three α) (roles : List α)
    (covers : ∀ r, r ∈ roles) (t : Term α β) (v : β → S α) (hv : ∀ j, NE (v j)) :
    (t.compile three roles).denote v = t.denote v := by
  induction t with
  | input j => rfl
  | reset left right hl hr =>
    simp only [compile, FullTerm.denote_resetWith, hl, hr, denote]
    exact (reset_eq_owned roles covers _ _ (right.denote_ne v hv)).symm
  | h r root left right hx hl hr =>
    simp only [compile, FullTerm.denote_resetWith, FullTerm.denote, hl, hr, hx,
      denote, SmallFragments.H]
    exact (reset_eq_owned roles covers _ _ (root.denote_ne v hv)).symm

def dominatesB {β : Type} [DecidableEq β] (weak strong : Guard β) : Bool :=
  decide (weak.source = strong.source) &&
  weak.many.all (fun j => decide (j ∈ strong.many)) &&
  weak.outside.all (fun j => decide (j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source))

def coversB {β : Type} [DecidableEq β] (left right : List (Guard β)) : Bool :=
  left.all (fun g => right.any (fun h => dominatesB h g))

theorem dominatesB_correct {β : Type} [DecidableEq β] (weak strong : Guard β) :
    dominatesB weak strong = true ↔ weak.Dominates strong := by
  simp [dominatesB, Guard.Dominates, Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem coversB_correct {β : Type} [DecidableEq β] (left right : List (Guard β)) :
    coversB left right = true ↔ Covers left right := by
  simp [coversB, Covers, List.all_eq_true, List.any_eq_true, dominatesB_correct]

/-- Executable version of guard compilation with explicit role equality. -/
def Term.guardList {α β : Type} [DecidableEq α] (observer : α) : Term α β → List (Guard β)
  | .input j => [⟨j, [], []⟩]
  | .reset left right => right.guardList observer ++
      (left.guardList observer).map (Guard.addMany right.root)
  | .h r root left right =>
      let children := left.guardList observer ++ right.guardList observer
      let eligible := if r = observer then children else
        (children.map (Guard.addOutside left.root)).map (Guard.addOutside right.root)
      root.guardList observer ++ eligible.map (Guard.addMany root.root)

theorem Term.guardList_correct {α β : Type} [DecidableEq α] (t : Term α β) (observer : α) :
    t.guardList observer = t.guards observer := by
  induction t with
  | input j => rfl
  | reset left right hl hr => simp [guardList, guards, hl, hr]
  | h r root left right hx hl hr => simp [guardList, guards, hx, hl, hr]

def Guard.forget {β : Type} (g : Guard β) : Guard β := { g with outside := [] }

theorem covers_forget {β : Type} (left right : List (Guard β)) (h : Covers left right) :
    Covers (left.map Guard.forget) (right.map Guard.forget) := by
  intro g hg
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hg
  obtain ⟨target, ht, he⟩ := h source hs
  refine ⟨target.forget, List.mem_map.mpr ⟨target, ht, rfl⟩, he.1, he.2.1, ?_⟩
  simp [Guard.forget]

@[simp] theorem forget_addMany {β : Type} (j : β) (g : Guard β) :
    (g.addMany j).forget = g.forget.addMany j := rfl

@[simp] theorem forget_addOutside {β : Type} (j : β) (g : Guard β) :
    (g.addOutside j).forget = g.forget := rfl

/-- One owner's own table is recovered from the outsider's table simply
by forgetting the negative tests. No second observer table is needed. -/
theorem Term.owner_guards_from_other {α β : Type} (t : Term α β) (owner outsider : α)
    (ht : t.OwnersIn (fun r => r = owner)) (ho : outsider ≠ owner) :
    t.guards owner = (t.guards outsider).map Guard.forget := by
  classical
  induction t with
  | input j => rfl
  | reset left right hl hr =>
    simp [guards, List.map_append, List.map_map, hl ht.1, hr ht.2,
      Function.comp_def]
  | h r root left right hx hl hr =>
    have he : r = owner := ht.1
    subst r
    simp [guards, Ne.symm ho, List.map_append, List.map_map,
      hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2, Function.comp_def]

/-- A single outsider table decides all winner-set equations in the
one-owner fragment, including the owner's own possible-win observation. -/
theorem Term.single_table_equation_iff {α β : Type} (three : Three α)
    (left right : Term α β) (owner outsider : α) (ho : outsider ≠ owner)
    (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    (∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v) ↔
      Covers (left.guards outsider) (right.guards outsider) ∧
        Covers (right.guards outsider) (left.guards outsider) := by
  rw [left.one_owner_equation_iff three right owner outsider ho hl hr]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [left.owner_guards_from_other owner outsider hl ho,
      right.owner_guards_from_other owner outsider hr ho]
    exact ⟨covers_forget _ _ h.1, covers_forget _ _ h.2⟩

def Term.equationB {α β : Type} [DecidableEq α] [DecidableEq β]
    (outsider : α) (left right : Term α β) : Bool :=
  let l := left.guardList outsider
  let r := right.guardList outsider
  coversB l r && coversB r l

def Term.observationB {α β : Type} [DecidableEq α] [DecidableEq β]
    (observer : α) (left right : Term α β) : Bool := equationB observer left right

theorem Term.observationB_correct {α β : Type} [DecidableEq α] [DecidableEq β]
    (left right : Term α β) (observer other background : α)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    observationB observer left right = true ↔
      ∀ v, (∀ j, NE (v j)) → (left.denote v observer ↔ right.denote v observer) := by
  rw [← left.observation_equation_iff right observer other background hko hkb hob hl hr]
  simp [observationB, equationB, guardList_correct, Bool.and_eq_true, coversB_correct]

/-- Correctness of the executable single-table equality algorithm. -/
theorem Term.equationB_correct {α β : Type} [DecidableEq α] [DecidableEq β]
    (three : Three α) (owner outsider : α) (ho : outsider ≠ owner)
    (left right : Term α β) (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    equationB outsider left right = true ↔
      ∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v := by
  rw [left.single_table_equation_iff three right owner outsider ho hl hr]
  simp [equationB, guardList_correct, Bool.and_eq_true, coversB_correct]

inductive View where
  | ownerAtom
  | seenAtom
  | otherAtom
  | seenAmbiguous
  | otherAmbiguous
  deriving DecidableEq, Repr

def View.Many : View → Prop
  | .seenAmbiguous | .otherAmbiguous => True
  | _ => False

def View.Owner : View → Prop
  | .ownerAtom => True
  | _ => False

def View.Seen : View → Prop
  | .seenAtom | .seenAmbiguous => True
  | _ => False

instance (v : View) : Decidable v.Many := by cases v <;> unfold View.Many <;> infer_instance
instance (v : View) : Decidable v.Owner := by cases v <;> unfold View.Owner <;> infer_instance
instance (v : View) : Decidable v.Seen := by cases v <;> unfold View.Seen <;> infer_instance

def View.ambiguous (seen : Bool) : View := if seen then .seenAmbiguous else .otherAmbiguous

def View.reset (left right : View) : View :=
  if right.Many then .ambiguous (decide (left.Seen ∨ right.Seen)) else right

def View.h (root left right : View) : View :=
  if root.Many then .ambiguous
    (decide (root.Seen ∨ (¬left.Owner ∧ ¬right.Owner ∧ (left.Seen ∨ right.Seen))))
  else root

theorem View.ext (v w : View) (hm : v.Many ↔ w.Many) (ho : v.Owner ↔ w.Owner)
    (hs : v.Seen ↔ w.Seen) : v = w := by
  cases v <;> cases w <;> simp_all [Many, Owner, Seen]

theorem View.reset_many (x y : View) : (x.reset y).Many ↔ y.Many := by
  cases x <;> cases y <;> decide

theorem View.reset_owner (x y : View) : (x.reset y).Owner ↔ y.Owner := by
  cases x <;> cases y <;> decide

theorem View.reset_seen (x y : View) : (x.reset y).Seen ↔ y.Seen ∨ (y.Many ∧ x.Seen) := by
  cases x <;> cases y <;> decide

theorem View.h_many (x y z : View) : (View.h x y z).Many ↔ x.Many := by
  cases x <;> cases y <;> cases z <;> decide

theorem View.h_owner (x y z : View) : (View.h x y z).Owner ↔ x.Owner := by
  cases x <;> cases y <;> cases z <;> decide

theorem View.h_seen (x y z : View) : (View.h x y z).Seen ↔
    x.Seen ∨ (x.Many ∧ ¬y.Owner ∧ ¬z.Owner ∧ (y.Seen ∨ z.Seen)) := by
  cases x <;> cases y <;> cases z <;> decide

noncomputable def view {α : Type} (owner observer : α) (A : S α) : View := by
  classical
  exact if Multiple A then
      if A observer then .seenAmbiguous else .otherAmbiguous
    else if A = atom owner then .ownerAtom
    else if A observer then .seenAtom else .otherAtom

theorem view_many {α : Type} (owner observer : α) (A : S α) :
    (view owner observer A).Many ↔ Multiple A := by
  classical
  by_cases hm : Multiple A <;> by_cases ha : A = atom owner <;> by_cases hs : A observer <;>
    simp_all [view, View.Many]

theorem view_owner {α : Type} (owner observer : α) (A : S α) :
    (view owner observer A).Owner ↔ A = atom owner := by
  classical
  by_cases hm : Multiple A <;> by_cases ha : A = atom owner <;> by_cases hs : A observer <;>
    simp_all [view, View.Owner]

theorem view_seen {α : Type} (owner observer : α) (hne : observer ≠ owner) (A : S α) :
    (view owner observer A).Seen ↔ A observer := by
  classical
  by_cases hm : Multiple A <;> by_cases ha : A = atom owner <;> by_cases hs : A observer <;>
    simp_all [view, View.Seen, atom]

theorem view_reset {α : Type} (owner observer : α) (hne : observer ≠ owner) (A B : S α) :
    view owner observer (ResetCalculus.reset A B) = (view owner observer A).reset (view owner observer B) := by
  apply View.ext
  · rw [view_many, View.reset_many, view_many, reset_multiple]
  · rw [view_owner, View.reset_owner, view_owner, reset_eq_atom]
  · rw [view_seen owner observer hne, View.reset_seen, view_seen owner observer hne,
      view_many, view_seen owner observer hne, reset_membership]

theorem view_h {α : Type} (owner observer : α) (hne : observer ≠ owner) (A B C : S α) :
    view owner observer (SmallFragments.H owner A B C) =
      View.h (view owner observer A) (view owner observer B) (view owner observer C) := by
  apply View.ext
  · rw [view_many, View.h_many, view_many]
    exact reset_multiple _ _
  · rw [view_owner, View.h_owner, view_owner]
    exact reset_eq_atom _ _ owner
  · rw [view_seen owner observer hne, View.h_seen, view_seen owner observer hne,
      view_many, view_owner, view_owner, view_seen owner observer hne,
      view_seen owner observer hne]
    simp only [SmallFragments.H, reset_membership, own_mem_other owner observer (Ne.symm hne)]
    grind

def Term.viewDenote {α β : Type} (v : β → View) : Term α β → View
  | .input j => v j
  | .reset left right => (left.viewDenote v).reset (right.viewDenote v)
  | .h _ root left right => View.h (root.viewDenote v) (left.viewDenote v) (right.viewDenote v)

theorem Term.view_correct {α β : Type} (t : Term α β) (owner observer : α)
    (hne : observer ≠ owner) (ht : t.OwnersIn (fun r => r = owner)) (v : β → S α) :
    view owner observer (t.denote v) = t.viewDenote (fun j => view owner observer (v j)) := by
  induction t with
  | input j => rfl
  | reset left right hl hr =>
    simp only [denote, viewDenote, view_reset owner observer hne, hl ht.1, hr ht.2]
  | h r root left right hx hl hr =>
    have he : r = owner := ht.1
    subst r
    simp only [denote, viewDenote, view_h owner observer hne,
      hx ht.2.1, hl ht.2.2.1, hr ht.2.2.2]

def View.lift {α : Type} (owner observer background : α) : View → S α
  | .ownerAtom => atom owner
  | .seenAtom => atom observer
  | .otherAtom => atom background
  | .seenAmbiguous => join (atom observer) (atom owner)
  | .otherAmbiguous => join (atom owner) (atom background)

theorem View.lift_ne {α : Type} (owner observer background : α) (v : View) :
    NE (v.lift owner observer background) := by
  cases v <;> simp only [lift]
  · exact ⟨owner, rfl⟩
  · exact ⟨observer, rfl⟩
  · exact ⟨background, rfl⟩
  · exact ⟨observer, Or.inl rfl⟩
  · exact ⟨owner, Or.inl rfl⟩

theorem View.view_lift {α : Type} (owner observer background : α)
    (hko : observer ≠ owner) (hkb : observer ≠ background) (hob : owner ≠ background)
    (v : View) : view owner observer (v.lift owner observer background) = v := by
  apply View.ext
  · rw [view_many]
    cases v <;> simp [lift, Many, pair_multiple, hko, hob]
  · rw [view_owner]
    cases v <;> simp [lift, Owner, pair_eq_atom, atom_inj, hko, Ne.symm hob]
  · rw [view_seen owner observer hko]
    cases v <;> simp [lift, Seen, join, atom, hko, hkb]

/-- The same five-element algebra generates the identities of every
one-owner H fragment with at least three roles. -/
theorem Term.five_element_complete {α β : Type} (three : Three α)
    (left right : Term α β) (owner outsider : α) (ho : outsider ≠ owner)
    (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    (∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v) ↔
      ∀ w, left.viewDenote w = right.viewDenote w := by
  obtain ⟨background, hbo, hbk⟩ := third_outside (three_others three) owner outsider
  constructor
  · intro he w
    let v := fun j => (w j).lift owner outsider background
    have hv : ∀ j, NE (v j) := fun j => View.lift_ne owner outsider background (w j)
    have hview : (fun j => view owner outsider (v j)) = w := by
      funext j
      exact View.view_lift owner outsider background ho (Ne.symm hbk) (Ne.symm hbo) (w j)
    have hh := congrArg (view owner outsider) (he v hv)
    rw [left.view_correct owner outsider ho hl, right.view_correct owner outsider ho hr,
      hview] at hh
    exact hh
  · intro he
    rw [left.single_table_equation_iff three right owner outsider ho hl hr]
    have ll := left.owners_mono _ (fun r => r = outsider ∨ r = owner) hl (fun _ h => Or.inr h)
    have rr := right.owners_mono _ (fun r => r = outsider ∨ r = owner) hr (fun _ h => Or.inr h)
    apply (left.observation_equation_iff right outsider owner background ho
      (Ne.symm hbk) (Ne.symm hbo) ll rr).mpr
    intro v _
    have hh := he (fun j => view owner outsider (v j))
    rw [← left.view_correct owner outsider ho hl, ← right.view_correct owner outsider ho hr] at hh
    calc
      left.denote v outsider ↔ (view owner outsider (left.denote v)).Seen :=
        (view_seen owner outsider ho _).symm
      _ ↔ (view owner outsider (right.denote v)).Seen := by rw [hh]
      _ ↔ right.denote v outsider := view_seen owner outsider ho _

end MinimalChoice.OwnerFragments

#print axioms MinimalChoice.OwnerFragments.Term.guard_semantics
#print axioms MinimalChoice.OwnerFragments.covers_iff
#print axioms MinimalChoice.OwnerFragments.Term.observation_implication_iff
#print axioms MinimalChoice.OwnerFragments.Term.one_owner_equation_iff
#print axioms MinimalChoice.OwnerFragments.Term.compile_correct
#print axioms MinimalChoice.OwnerFragments.Term.equationB_correct
#print axioms MinimalChoice.OwnerFragments.Term.single_table_equation_iff
#print axioms MinimalChoice.OwnerFragments.view_h
#print axioms MinimalChoice.OwnerFragments.Term.five_element_complete
