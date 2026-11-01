/- The three-owner instance of the core variable-bound obstruction.
The arbitrary-K argument and binary classification are written proofs in
appendix-core-basis.tex. This module transfers ALL three-variable core
identities to the five-element countermodel, without a term-size cutoff. -/
import CoreModels

set_option autoImplicit false
namespace MinimalChoice.CoreObstruction

inductive Player where
  | a | b | c
  deriving DecidableEq, Repr

inductive Winner where
  | a | b | c | ab | ac | bc | abc
  deriving DecidableEq, Repr

def Winner.atom : Player → Winner
  | .a => .a | .b => .b | .c => .c

def Winner.embed : Winner → S Player
  | .a => MinimalChoice.atom .a
  | .b => MinimalChoice.atom .b
  | .c => MinimalChoice.atom .c
  | .ab => fun i => i = .a ∨ i = .b
  | .ac => fun i => i = .a ∨ i = .c
  | .bc => fun i => i = .b ∨ i = .c
  | .abc => fun _ => True

def Winner.join : Winner → Winner → Winner
  | .a, .a => .a | .b, .b => .b | .c, .c => .c
  | .a, .b | .b, .a | .a, .ab | .ab, .a | .b, .ab | .ab, .b | .ab, .ab => .ab
  | .a, .c | .c, .a | .a, .ac | .ac, .a | .c, .ac | .ac, .c | .ac, .ac => .ac
  | .b, .c | .c, .b | .b, .bc | .bc, .b | .c, .bc | .bc, .c | .bc, .bc => .bc
  | _, _ => .abc

def Winner.own (r : Player) (x y : Winner) : Winner :=
  if x = .atom r ∨ y = .atom r then .atom r else x.join y

theorem Winner.embed_ne (x : Winner) : NE x.embed := by
  cases x with
  | a => exact ⟨.a, rfl⟩
  | b => exact ⟨.b, rfl⟩
  | c => exact ⟨.c, rfl⟩
  | ab => exact ⟨.a, Or.inl rfl⟩
  | ac => exact ⟨.a, Or.inl rfl⟩
  | bc => exact ⟨.b, Or.inl rfl⟩
  | abc => exact ⟨.a, True.intro⟩

theorem Winner.embed_injective (x y : Winner) (h : x.embed = y.embed) : x = y := by
  have ha := congrFun h Player.a
  have hb := congrFun h Player.b
  have hc := congrFun h Player.c
  cases x <;> cases y <;> simp_all [embed, MinimalChoice.atom]

theorem Winner.embed_atom (r : Player) : (Winner.atom r).embed = MinimalChoice.atom r := by
  cases r <;> rfl

theorem Winner.embed_eq_atom (x : Winner) (r : Player) :
    x.embed = MinimalChoice.atom r ↔ x = Winner.atom r := by
  rw [← embed_atom r]
  exact ⟨embed_injective x (.atom r), congrArg embed⟩

theorem Winner.embed_join (x y : Winner) :
    (x.join y).embed = MinimalChoice.join x.embed y.embed := by
  cases x <;> cases y <;> funext i <;> apply propext <;>
    cases i <;> simp [join, embed, MinimalChoice.join, MinimalChoice.atom]

theorem Winner.embed_own (r : Player) (x y : Winner) :
    (x.own r y).embed = MinimalChoice.own r x.embed y.embed := by
  classical
  simp only [MinimalChoice.own, embed_eq_atom, Winner.own]
  split
  · exact embed_atom r
  · exact embed_join x y

inductive Marker where
  | a | b | c | n | p
  deriving DecidableEq, Repr

def Marker.atom : Player → Marker
  | .a => .a | .b => .b | .c => .c

def Marker.join (x y : Marker) : Marker :=
  if x = y then x else if x = .p ∨ y = .p then .p else .n

def Marker.own (r : Player) (x y : Marker) : Marker :=
  if x = .atom r ∨ y = .atom r then .atom r else x.join y

inductive Drop where
  | a | b | c | p
  deriving DecidableEq, Repr

def Drop.omitted : Drop → Marker
  | .a => .a | .b => .b | .c => .c | .p => .p

def Drop.quotient : Drop → Winner → Marker
  | .p, .a => .a | .p, .b => .b | .p, .c => .c | .p, _ => .n
  | .a, .b => .b | .a, .c => .c | .a, .bc => .n | .a, _ => .p
  | .b, .a => .a | .b, .c => .c | .b, .ac => .n | .b, _ => .p
  | .c, .a => .a | .c, .b => .b | .c, .ab => .n | .c, _ => .p

def Drop.representative : Drop → Marker → Winner
  | .p, .a => .a | .p, .b => .b | .p, .c => .c | .p, _ => .ab
  | .a, .b => .b | .a, .c => .c | .a, .n => .bc | .a, _ => .a
  | .b, .a => .a | .b, .c => .c | .b, .n => .ac | .b, _ => .b
  | .c, .a => .a | .c, .b => .b | .c, .n => .ab | .c, _ => .c

theorem Drop.quotient_own (e : Drop) (r : Player) (x y : Winner) :
    e.quotient (Winner.own r x y) = Marker.own r (e.quotient x) (e.quotient y) := by
  cases e <;> cases r <;> cases x <;> cases y <;> decide

theorem Drop.quotient_representative (e : Drop) (x : Marker) (h : x ≠ e.omitted) :
    e.quotient (e.representative x) = x := by
  cases e <;> cases x <;> simp_all [omitted, quotient, representative]

inductive CoreTerm (β : Type) where
  | input (v : β)
  | node (r : Player) (left right : CoreTerm β)

def CoreTerm.winner {β : Type} (v : β → Winner) : CoreTerm β → Winner
  | .input j => v j
  | .node r s t => Winner.own r (s.winner v) (t.winner v)

def CoreTerm.marker {β : Type} (v : β → Marker) : CoreTerm β → Marker
  | .input j => v j
  | .node r s t => Marker.own r (s.marker v) (t.marker v)

noncomputable def CoreTerm.sets {β : Type} (v : β → S Player) : CoreTerm β → S Player
  | .input j => v j
  | .node r s t => MinimalChoice.own r (s.sets v) (t.sets v)

theorem CoreTerm.embed_winner {β : Type} (t : CoreTerm β) (v : β → Winner) :
    (t.winner v).embed = t.sets (fun j => (v j).embed) := by
  induction t with
  | input j => rfl
  | node r s t hs ht => rw [winner, Winner.embed_own, hs, ht]; rfl

theorem CoreTerm.quotient_winner {β : Type} (t : CoreTerm β) (v : β → Winner)
    (e : Drop) : e.quotient (t.winner v) = t.marker (fun j => e.quotient (v j)) := by
  induction t with
  | input j => rfl
  | node r s t hs ht => rw [winner, Drop.quotient_own, hs, ht]; rfl

theorem missing (x y z : Marker) :
    ∃ e : Drop, x ≠ e.omitted ∧ y ≠ e.omitted ∧ z ≠ e.omitted := by
  cases x <;> cases y <;> cases z <;>
    first | exact ⟨.a, by decide⟩ | exact ⟨.b, by decide⟩
          | exact ⟨.c, by decide⟩ | exact ⟨.p, by decide⟩

/-- Every three-variable core identity holds in the five-element model. -/
theorem three_variable_transfer (s t : CoreTerm (Fin 3))
    (valid : ∀ v : Fin 3 → S Player, (∀ j, NE (v j)) → s.sets v = t.sets v)
    (v : Fin 3 → Marker) : s.marker v = t.marker v := by
  obtain ⟨e, h0, h1, h2⟩ := missing (v 0) (v 1) (v 2)
  have hv : ∀ j : Fin 3, v j ≠ e.omitted := by
    intro j
    have cases3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases cases3 with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  let w := fun j => e.representative (v j)
  have hw : (fun j => e.quotient (w j)) = v := by
    funext j
    exact e.quotient_representative (v j) (hv j)
  have he : s.winner w = t.winner w := by
    apply Winner.embed_injective
    rw [CoreTerm.embed_winner, CoreTerm.embed_winner]
    exact valid _ (fun j => (w j).embed_ne)
  have heq := congrArg e.quotient he
  simpa only [CoreTerm.quotient_winner, hw] using heq

theorem exhaustion_valid (c x y z : S Player) :
    join c (join (own Player.a c x) (join (own Player.b c y) (own Player.c c z))) =
      join (own Player.a c x) (join (own Player.b c y) (own Player.c c z)) := by
  funext i
  apply propext
  constructor
  · intro h
    rcases h with hc | h
    · cases i with
      | a => exact Or.inl ((own_mem_owner _ _ _).mpr (Or.inl hc))
      | b => exact Or.inr (Or.inl ((own_mem_owner _ _ _).mpr (Or.inl hc)))
      | c => exact Or.inr (Or.inr ((own_mem_owner _ _ _).mpr (Or.inl hc)))
    · exact h
  · exact Or.inr

/-- For a finite role type, this is the semantic nonempty sum in E_K. -/
theorem exhaustion_indexed {α : Type} (c : S α) (xs : α → S α) :
    join c (fun k => ∃ r, own r c (xs r) k) =
      (fun k => ∃ r, own r c (xs r) k) := by
  funext k
  apply propext
  constructor
  · rintro (hc | h)
    · exact ⟨k, (own_mem_owner k c (xs k)).mpr (Or.inl hc)⟩
    · exact h
  · exact Or.inr

theorem Marker.derived_join (x y : Marker) :
    own Player.c (own Player.a x y) (own Player.b x y) = x.join y := by
  cases x <;> cases y <;> decide

theorem exhaustion_failure :
    Marker.join .p
      (Marker.join (Marker.own .a .p .a)
        (Marker.join (Marker.own .b .p .b) (Marker.own .c .p .c))) ≠
    Marker.join (Marker.own .a .p .a)
      (Marker.join (Marker.own .b .p .b) (Marker.own .c .p .c)) := by decide

end MinimalChoice.CoreObstruction

#print axioms MinimalChoice.CoreObstruction.three_variable_transfer
#print axioms MinimalChoice.CoreObstruction.exhaustion_valid
#print axioms MinimalChoice.CoreObstruction.exhaustion_indexed
#print axioms MinimalChoice.CoreObstruction.exhaustion_failure
