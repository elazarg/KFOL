/- A core model in which every owner differs from union, obtained by
quotienting a subalgebra of two different observer factors. The transfer
theorem covers arbitrary terms and arities, not a bounded term search. -/
import CoreObstruction

set_option autoImplicit false
namespace MinimalChoice.CoreQuotients
open CoreObstruction

/-- Owner a stops absorbing at p; the other owners still absorb there. -/
def own (r : Player) (x y : Marker) : Marker :=
  if r = .a ∧ (x = .p ∨ y = .p) then .p else Marker.own r x y

theorem derived_join (x y : Marker) :
    own .c (own .a x y) (own .b x y) = Marker.join x y := by
  cases x <;> cases y <;> decide

inductive Source where
  | an | pb | cc | pn | nn | ap | pp | np
  deriving DecidableEq, Repr

def Source.first : Source → Marker
  | .an | .ap => .a
  | .pb | .pn | .pp => .p
  | .cc => .c
  | .nn | .np => .n

def Source.second : Source → Marker
  | .an | .pn | .nn => .n
  | .pb => .b
  | .cc => .c
  | .ap | .pp | .np => .p

def Source.decode : Marker → Marker → Source
  | .a, .n => .an | .p, .b => .pb | .c, .c => .cc
  | .p, .n => .pn | .a, .p => .ap | .p, .p => .pp
  | .n, .p => .np | _, _ => .nn

def Source.own (r : Player) (x y : Source) : Source :=
  decode (Marker.own r x.first y.first) (Marker.own r x.second y.second)

theorem Source.first_own (r : Player) (x y : Source) :
    (own r x y).first = Marker.own r x.first y.first := by
  cases r <;> cases x <;> cases y <;> decide

theorem Source.second_own (r : Player) (x y : Source) :
    (own r x y).second = Marker.own r x.second y.second := by
  cases r <;> cases x <;> cases y <;> decide

theorem Source.separate (x y : Source)
    (h₁ : x.first = y.first) (h₂ : x.second = y.second) : x = y := by
  cases x <;> cases y <;> simp_all [first, second]

theorem Source.first_omits (x : Source) : x.first ≠ Drop.b.omitted := by
  cases x <;> decide

theorem Source.second_omits (x : Source) : x.second ≠ Drop.a.omitted := by
  cases x <;> decide

def Source.project : Source → Marker
  | .an => .a | .pb => .b | .cc => .c
  | .pn | .nn => .n
  | .ap | .pp | .np => .p

def representative : Marker → Source
  | .a => .an | .b => .pb | .c => .cc | .n => .nn | .p => .pp

theorem project_representative (x : Marker) : (representative x).project = x := by
  cases x <;> rfl

theorem Source.project_own (r : Player) (x y : Source) :
    (own r x y).project = CoreQuotients.own r x.project y.project := by
  cases r <;> cases x <;> cases y <;> decide

def eval {β : Type} (v : β → Marker) : CoreTerm β → Marker
  | .input j => v j
  | .node r s t => own r (eval v s) (eval v t)

def evalSource {β : Type} (v : β → Source) : CoreTerm β → Source
  | .input j => v j
  | .node r s t => Source.own r (evalSource v s) (evalSource v t)

theorem eval_first {β : Type} (t : CoreTerm β) (v : β → Source) :
    (evalSource v t).first = t.marker (fun j => (v j).first) := by
  induction t with
  | input j => rfl
  | node r s t hs ht => rw [evalSource, Source.first_own, hs, ht]; rfl

theorem eval_second {β : Type} (t : CoreTerm β) (v : β → Source) :
    (evalSource v t).second = t.marker (fun j => (v j).second) := by
  induction t with
  | input j => rfl
  | node r s t hs ht => rw [evalSource, Source.second_own, hs, ht]; rfl

theorem eval_project {β : Type} (t : CoreTerm β) (v : β → Source) :
    (evalSource v t).project = eval (fun j => (v j).project) t := by
  induction t with
  | input j => rfl
  | node r s t hs ht => rw [evalSource, Source.project_own, hs, ht]; rfl

theorem factor_transfer {β : Type} (s t : CoreTerm β) (e : Drop)
    (valid : ∀ v : β → S Player, (∀ j, NE (v j)) → s.sets v = t.sets v)
    (v : β → Marker) (hv : ∀ j, v j ≠ e.omitted) : s.marker v = t.marker v := by
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

/-- Every core identity, in any number of variables, holds in the quotient. -/
theorem identity_transfer {β : Type} (s t : CoreTerm β)
    (valid : ∀ v : β → S Player, (∀ j, NE (v j)) → s.sets v = t.sets v)
    (v : β → Marker) : eval v s = eval v t := by
  let w := fun j => representative (v j)
  have he : evalSource w s = evalSource w t := by
    apply Source.separate
    · rw [eval_first, eval_first]
      exact factor_transfer s t .b valid _ (fun j => (w j).first_omits)
    · rw [eval_second, eval_second]
      exact factor_transfer s t .a valid _ (fun j => (w j).second_omits)
  have hw : (fun j => (w j).project) = v := by
    funext j
    exact project_representative (v j)
  have h := congrArg Source.project he
  simpa only [eval_project, hw] using h

theorem every_owner_differs (r : Player) :
    own r (Marker.atom r) .n ≠ Marker.join (Marker.atom r) .n := by
  cases r <;> decide

theorem not_conservative : own .a .b .c ≠ .b ∧ own .a .b .c ≠ .c := by decide

def reset (x y : Marker) : Marker :=
  [.a, .b, .c].foldl (fun z r => own r z y) (Marker.join x y)

theorem reset_commutation_not_transitive :
    reset .a .p = reset .p .a ∧ reset .p .n = reset .n .p ∧
      reset .a .n ≠ reset .n .a := by decide

def collapse : Marker → Fin 4
  | .a | .n => 0 | .b => 1 | .c => 2 | .p => 3

def lift (x : Fin 4) : Marker :=
  if x = 0 then .n else if x = 1 then .b else if x = 2 then .c else .p

theorem collapse_own (r : Player) (x y : Marker) :
    collapse (own r x y) = collapse (own r (lift (collapse x)) (lift (collapse y))) := by
  cases r <;> cases x <;> cases y <;> decide

def context (i : Fin 4) (x : Marker) : Marker :=
  if i = 0 then x else if i = 1 then own .a x .a
  else if i = 2 then own .a (own .b x .p) .a
  else own .a (own .c x .p) .a

theorem forcing_context (x y : Marker) (hne : x ≠ y) :
    ∃ i : Fin 4,
      (context i x = .a ∧ (context i y = .n ∨ context i y = .p)) ∨
      (context i y = .a ∧ (context i x = .n ∨ context i x = .p)) := by
  cases x <;> cases y <;> first | exact False.elim (hne rfl) | decide

/-- Every nonidentity compatible equivalence contains the pair (a,n). -/
theorem monolith_minimal (R : Marker → Marker → Prop) (he : Equivalence R)
    (hc : ∀ r x y u v, R x y → R u v → R (own r x u) (own r y v))
    (x y : Marker) (hne : x ≠ y) (hxy : R x y) : R .a .n := by
  have hadd (u v z : Marker) (h : R u v) : R (Marker.join u z) (Marker.join v z) := by
    rw [← derived_join, ← derived_join]
    exact hc .c _ _ _ _ (hc .a _ _ _ _ h (he.refl z)) (hc .b _ _ _ _ h (he.refl z))
  have hctx (i : Fin 4) : R (context i x) (context i y) := by
    simp only [context]
    split
    · exact hxy
    split
    · exact hc .a _ _ _ _ hxy (he.refl .a)
    split
    · exact hc .a _ _ _ _ (hc .b _ _ _ _ hxy (he.refl .p)) (he.refl .a)
    · exact hc .a _ _ _ _ (hc .c _ _ _ _ hxy (he.refl .p)) (he.refl .a)
  have hap (h : R .a .p) : R .a .n := by
    have hnp := hadd .a .p .n h
    change R .n .p at hnp
    exact he.trans h (he.symm hnp)
  obtain ⟨i, h | h⟩ := forcing_context x y hne
  · rcases h with ⟨ha, hn | hp⟩
    · simpa only [ha, hn] using hctx i
    · exact hap (by simpa only [ha, hp] using hctx i)
  · rcases h with ⟨ha, hn | hp⟩
    · exact he.symm (by simpa only [ha, hn] using hctx i)
    · exact hap (he.symm (by simpa only [ha, hp] using hctx i))

end MinimalChoice.CoreQuotients

#print axioms MinimalChoice.CoreQuotients.identity_transfer
#print axioms MinimalChoice.CoreQuotients.collapse_own
#print axioms MinimalChoice.CoreQuotients.monolith_minimal
#print axioms MinimalChoice.CoreQuotients.reset_commutation_not_transitive
