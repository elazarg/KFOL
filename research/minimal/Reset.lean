/-
The reset calculus, including all mixed valuations. The semantics theorem
and three-element-chain completeness are generic, with only Std.
-/
import Separation

set_option autoImplicit false
namespace MinimalChoice.ResetCalculus

noncomputable def reset {α : Type} (A B : S α) : S α := by
  classical
  exact if Multiple B then join A B else B

theorem not_multiple_atom {α : Type} (r : α) : ¬ Multiple (atom r) := by
  rintro ⟨u, v, hne, hu, hv⟩
  exact hne (hu.trans hv.symm)

theorem reset_multiple {α : Type} (A B : S α) :
    Multiple (reset A B) ↔ Multiple B := by
  classical
  by_cases hb : Multiple B
  · simp only [reset, ite_eq_left hb]
    constructor
    · intro _
      exact hb
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨u, v, huv, Or.inr hu, Or.inr hv⟩
  · simp only [reset, ite_eq_right hb]

theorem reset_membership {α : Type} (A B : S α) (w : α) :
    reset A B w ↔ B w ∨ (Multiple B ∧ A w) := by
  classical
  by_cases hb : Multiple B <;> simp [reset, hb, join, or_comm]

/-- Soundness of Freese et al. (2002), Theorem 3.7, in reset notation.
Completeness uses their published theorem and `Term.three_chain_complete`;
that equational-derivation argument is not formalized in this module. -/
theorem basis_idem {α : Type} (A : S α) : reset A A = A := by
  funext w
  apply propext
  simp only [reset_membership]
  grind

theorem basis_absorb {α : Type} (A B : S α) :
    reset (reset A B) A = reset B A := by
  funext w
  apply propext
  simp only [reset_membership]
  grind

theorem basis_repeat {α : Type} (A B : S α) :
    reset (reset A B) B = reset A B := by
  funext w
  apply propext
  simp only [reset_membership]
  grind

theorem basis_nested {α : Type} (A B C : S α) :
    reset A (reset (reset A B) C) = reset A (reset B C) := by
  funext w
  apply propext
  simp only [reset_membership, reset_multiple]
  grind

theorem basis_exchange {α : Type} (A B C : S α) :
    reset (reset (reset A B) C) B = reset (reset A C) B := by
  funext w
  apply propext
  simp only [reset_membership]
  grind

theorem basis_left_comm {α : Type} (A B C : S α) :
    reset A (reset B C) = reset B (reset A C) := by
  funext w
  apply propext
  simp only [reset_membership, reset_multiple]
  grind

theorem reset_ne {α : Type} (A B : S α) (hb : NE B) : NE (reset A B) := by
  classical
  by_cases hm : Multiple B
  · rcases hb with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [reset, ite_eq_left hm]
    exact Or.inr hx
  · simpa only [reset, ite_eq_right hm] using hb

theorem reset_eq_owned {α : Type} (roles : List α) (covers : ∀ r, r ∈ roles)
    (A B : S α) (hb : NE B) : reset A B = relativeReset roles A B := by
  classical
  rcases atom_or_multiple B hb with ⟨r, hr⟩ | hm
  · subst B
    rw [relativeReset_atom roles A r (covers r)]
    simp [reset, not_multiple_atom]
  · rw [relativeReset_multiple roles A B hm]
    simp only [reset, ite_eq_left hm]
    funext x
    exact propext Or.comm

inductive Term (β : Type) where
  | var : β → Term β
  | step : Term β → Term β → Term β

def Term.root {β : Type} : Term β → β
  | .var j => j
  | .step _ right => right.root

noncomputable def Term.denote {α β : Type} (t : Term β) (v : β → S α) : S α :=
  match t with
  | .var j => v j
  | .step left right => reset (left.denote v) (right.denote v)

def Term.selected {β : Type} (t : Term β) (ambiguous : β → Prop) (j : β) : Prop :=
  match t with
  | .var i => j = i
  | .step left right => right.selected ambiguous j ∨
      (ambiguous right.root ∧ left.selected ambiguous j)

theorem Term.root_selected {β : Type} (t : Term β) (b : β → Prop) :
    t.selected b t.root := by
  induction t with
  | var j => rfl
  | step left right _ hr => exact Or.inl hr

theorem Term.selected_congr {β : Type} (t : Term β) (b c : β → Prop)
    (h : ∀ i, b i ↔ c i) (j : β) : t.selected b j ↔ t.selected c j := by
  induction t with
  | var i => exact Iff.rfl
  | step left right hl hr => exact or_congr hr (and_congr (h right.root) hl)

/-- Whether an input is selected never depends on that input's own status. -/
theorem Term.selected_self_independent {β : Type} (t : Term β) (b c : β → Prop)
    (j : β) (h : ∀ i, i ≠ j → (b i ↔ c i)) :
    t.selected b j ↔ t.selected c j := by
  classical
  induction t with
  | var i => exact Iff.rfl
  | step left right hl hr =>
    by_cases he : j = right.root
    · subst j
      exact ⟨fun _ => Or.inl (right.root_selected c),
             fun _ => Or.inl (right.root_selected b)⟩
    · exact or_congr hr (and_congr (h right.root (Ne.symm he)) hl)

theorem Term.multiple_iff_root {α β : Type} (t : Term β) (v : β → S α) :
    Multiple (t.denote v) ↔ Multiple (v t.root) := by
  induction t with
  | var j => exact Iff.rfl
  | step left right _ hr => exact (reset_multiple _ _).trans hr

theorem Term.denote_ne {α β : Type} (t : Term β) (v : β → S α)
    (hv : ∀ j, NE (v j)) : NE (t.denote v) := by
  induction t with
  | var j => exact hv j
  | step left right _ hr => exact reset_ne _ _ hr

/-- Exact semantics, including mixed atomic and ambiguous inputs. -/
theorem Term.denote_membership {α β : Type} (t : Term β) (v : β → S α) (w : α) :
    t.denote v w ↔ ∃ j, t.selected (fun i => Multiple (v i)) j ∧ v j w := by
  classical
  induction t with
  | var i =>
    constructor
    · intro h
      exact ⟨i, rfl, h⟩
    · rintro ⟨j, he, hj⟩
      subst j
      exact hj
  | step left right hl hr =>
    by_cases hm : Multiple (v right.root)
    · have hm' : Multiple (right.denote v) := (right.multiple_iff_root v).mpr hm
      simp only [Term.denote, reset, ite_eq_left hm', join]
      constructor
      · rintro (hx | hx)
        · obtain ⟨j, hj, hv⟩ := hl.mp hx
          exact ⟨j, Or.inr ⟨hm, hj⟩, hv⟩
        · obtain ⟨j, hj, hv⟩ := hr.mp hx
          exact ⟨j, Or.inl hj, hv⟩
      · rintro ⟨j, hj, hv⟩
        rcases hj with hj | ⟨_, hj⟩
        · exact Or.inr (hr.mpr ⟨j, hj, hv⟩)
        · exact Or.inl (hl.mpr ⟨j, hj, hv⟩)
    · have hm' : ¬ Multiple (right.denote v) :=
        fun he => hm ((right.multiple_iff_root v).mp he)
      simp only [Term.denote, reset, ite_eq_right hm']
      constructor
      · intro hx
        obtain ⟨j, hj, hv⟩ := hr.mp hx
        exact ⟨j, Or.inl hj, hv⟩
      · rintro ⟨j, hj, hv⟩
        rcases hj with hj | ⟨he, _⟩
        · exact hr.mpr ⟨j, hj, hv⟩
        · exact False.elim (hm he)

def chain0 {α : Type} (h : Three α) : S α := atom h.s
def chain1 {α : Type} (h : Three α) : S α := join (atom h.s) (atom h.t)
def chain2 {α : Type} (h : Three α) : S α := join (atom h.r) (chain1 h)

theorem chain1_multiple {α : Type} (h : Three α) : Multiple (chain1 h) :=
  ⟨h.s, h.t, h.st, Or.inl rfl, Or.inr rfl⟩

theorem chain2_multiple {α : Type} (h : Three α) : Multiple (chain2 h) :=
  ⟨h.r, h.s, h.rs, Or.inl rfl, Or.inr (Or.inl rfl)⟩

noncomputable def chainVal {α β : Type} (h : Three α) (b : β → Prop)
    (j i : β) : S α := by
  classical
  exact if i = j then chain2 h else if b i then chain1 h else chain0 h

theorem chainVal_status {α β : Type} (h : Three α) (b : β → Prop) (j i : β) :
    Multiple (chainVal h b j i) ↔ i = j ∨ b i := by
  classical
  by_cases he : i = j
  · simp only [chainVal, ite_eq_left he]
    exact ⟨fun _ => Or.inl he, fun _ => chain2_multiple h⟩
  · simp only [chainVal, ite_eq_right he]
    by_cases hb : b i
    · simp only [ite_eq_left hb]
      exact ⟨fun _ => Or.inr hb, fun _ => chain1_multiple h⟩
    · simp only [ite_eq_right hb]
      constructor
      · intro hm
        exact False.elim (not_multiple_atom h.s hm)
      · rintro (hi | hi)
        · exact False.elim (he hi)
        · exact False.elim (hb hi)

theorem chainVal_marker {α β : Type} (h : Three α) (b : β → Prop) (j i : β) :
    chainVal h b j i h.r ↔ i = j := by
  classical
  by_cases he : i = j
  · simp only [chainVal, ite_eq_left he]
    exact ⟨fun _ => he, fun _ => Or.inl rfl⟩
  · simp only [chainVal, ite_eq_right he]
    by_cases hb : b i
    · simp only [ite_eq_left hb]
      constructor
      · rintro (hs | ht)
        · exact False.elim (h.rs hs)
        · exact False.elim (h.rt ht)
      · exact fun hi => False.elim (he hi)
    · simp only [ite_eq_right hb]
      constructor
      · exact fun hs => False.elim (h.rs hs)
      · exact fun hi => False.elim (he hi)

theorem Term.chain_marker {α β : Type} (t : Term β) (h : Three α)
    (b : β → Prop) (j : β) :
    t.denote (chainVal h b j) h.r ↔ t.selected b j := by
  let status : β → Prop := fun i => i = j ∨ b i
  have hs : ∀ i, Multiple (chainVal h b j i) ↔ status i :=
    chainVal_status h b j
  have he : ∀ i, i ≠ j → (status i ↔ b i) := by
    intro i hij
    constructor
    · rintro (hi | hi)
      · exact False.elim (hij hi)
      · exact hi
    · exact Or.inr
  rw [t.denote_membership]
  constructor
  · rintro ⟨i, hi, hm⟩
    have hij := (chainVal_marker h b j i).mp hm
    subst i
    exact (t.selected_self_independent status b j he).mp
      ((t.selected_congr _ status hs j).mp hi)
  · intro hj
    have hj' := (t.selected_self_independent status b j he).mpr hj
    exact ⟨j, (t.selected_congr _ status hs j).mpr hj',
      (chainVal_marker h b j j).mpr rfl⟩

def ChainTest {α β : Type} (h : Three α) (v : β → S α) : Prop :=
  ∀ i, v i = chain0 h ∨ v i = chain1 h ∨ v i = chain2 h

theorem chainVal_test {α β : Type} (h : Three α) (b : β → Prop) (j : β) :
    ChainTest h (chainVal h b j) := by
  classical
  intro i
  by_cases he : i = j
  · exact Or.inr (Or.inr (by simp [chainVal, he]))
  · by_cases hb : b i
    · exact Or.inr (Or.inl (by simp [chainVal, he, hb]))
    · exact Or.inl (by simp [chainVal, he, hb])

/-- Equality on this three-element chain proves equality on every valuation. -/
theorem Term.three_chain_complete {α β : Type} (h : Three α) (t u : Term β)
    (he : ∀ v : β → S α, ChainTest h v → t.denote v = u.denote v) :
    ∀ v : β → S α, t.denote v = u.denote v := by
  have hs : ∀ b j, t.selected b j ↔ u.selected b j := by
    intro b j
    have he' := he (chainVal h b j) (chainVal_test h b j)
    have hw : t.denote (chainVal h b j) h.r ↔
        u.denote (chainVal h b j) h.r := by rw [he']
    exact (t.chain_marker h b j).symm.trans (hw.trans (u.chain_marker h b j))
  intro v
  funext w
  apply propext
  rw [t.denote_membership, u.denote_membership]
  exact exists_congr (fun j => and_congr (hs _ j) Iff.rfl)

def suppressTerm {α β : Type} (roles : List α)
    (acc base : MinimalChoice.Term α β) : MinimalChoice.Term α β :=
  match roles with
  | [] => acc
  | r :: rest => .node r (suppressTerm rest acc base) base

theorem denote_suppressTerm {α β : Type} (roles : List α)
    (acc base : MinimalChoice.Term α β) (v : β → S α) :
    MinimalChoice.denote (suppressTerm roles acc base) v =
      resetFold roles (MinimalChoice.denote acc v) (MinimalChoice.denote base v) := by
  induction roles with
  | nil => rfl
  | cons r rest ih => simp only [suppressTerm, MinimalChoice.denote, resetFold, ih]

def Term.compile {α β : Type} (h : Three α) (roles : List α)
    (t : Term β) : MinimalChoice.Term α β :=
  match t with
  | .var j => .var j
  | .step left right =>
    let l := left.compile h roles
    let r := right.compile h roles
    suppressTerm roles (joinTerm h r l) r

/-- The reset syntax expands to actual owned-choice syntax with the same meaning. -/
theorem Term.compile_correct {α β : Type} (h : Three α) (roles : List α)
    (covers : ∀ r, r ∈ roles) (t : Term β) (v : β → S α)
    (hv : ∀ j, NE (v j)) :
    MinimalChoice.denote (t.compile h roles) v = t.denote v := by
  induction t with
  | var j => rfl
  | step left right hl hr =>
    simp only [Term.compile, denote_suppressTerm, denote_joinTerm, hl, hr, Term.denote]
    exact (reset_eq_owned roles covers _ _ (right.denote_ne v hv)).symm

end MinimalChoice.ResetCalculus

#print axioms MinimalChoice.ResetCalculus.reset_eq_owned
#print axioms MinimalChoice.ResetCalculus.basis_idem
#print axioms MinimalChoice.ResetCalculus.basis_absorb
#print axioms MinimalChoice.ResetCalculus.basis_repeat
#print axioms MinimalChoice.ResetCalculus.basis_nested
#print axioms MinimalChoice.ResetCalculus.basis_exchange
#print axioms MinimalChoice.ResetCalculus.basis_left_comm
#print axioms MinimalChoice.ResetCalculus.Term.denote_membership
#print axioms MinimalChoice.ResetCalculus.Term.selected_self_independent
#print axioms MinimalChoice.ResetCalculus.Term.three_chain_complete
#print axioms MinimalChoice.ResetCalculus.Term.compile_correct
