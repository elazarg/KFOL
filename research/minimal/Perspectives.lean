/-
Exact per-player observations and small tests for arbitrary-arity terms.
The observation is membership among possible SPE winners, not forceability.
-/
import Basic

set_option autoImplicit false
namespace MinimalChoice

theorem own_ne {α : Type} (r : α) (A B : S α) (hA : NE A) :
    NE (own r A B) := by
  classical
  unfold own
  split
  · exact atom_ne r
  · rcases hA with ⟨i, hi⟩
    exact ⟨i, Or.inl hi⟩

theorem join_eq_atom_iff {α : Type} (A B : S α) (hA : NE A) (hB : NE B)
    (i : α) : join A B = atom i ↔ A = atom i ∧ B = atom i := by
  constructor
  · intro h
    constructor
    · exact eq_atom_of_ne_sub i A hA (fun x hx => h ▸ Or.inl hx)
    · exact eq_atom_of_ne_sub i B hB (fun x hx => h ▸ Or.inr hx)
  · rintro ⟨rfl, rfl⟩
    funext x
    apply propext
    simp only [join, or_self]

theorem own_eq_owner_iff {α : Type} (r : α) (A B : S α)
    (hA : NE A) (hB : NE B) :
    own r A B = atom r ↔ A = atom r ∨ B = atom r := by
  classical
  by_cases h : A = atom r ∨ B = atom r
  · simp [own, h]
  · have hn : join A B ≠ atom r := by
      intro he
      exact h (Or.inl ((join_eq_atom_iff A B hA hB r).mp he).1)
    simp [own, h, hn]

theorem own_eq_other_iff {α : Type} (r i : α) (hri : r ≠ i)
    (A B : S α) (hA : NE A) (hB : NE B) :
    own r A B = atom i ↔ A = atom i ∧ B = atom i := by
  classical
  by_cases h : A = atom r ∨ B = atom r
  · have hn : ¬ (A = atom i ∧ B = atom i) := by
      rintro ⟨ha, hb⟩
      rcases h with h | h
      · exact hri (atom_inj.mp (h.symm.trans ha))
      · exact hri (atom_inj.mp (h.symm.trans hb))
    simp [own, h, atom_inj, hri, hn]
  · simp only [own, ite_eq_right h]
    exact join_eq_atom_iff A B hA hB i

theorem own_mem_owner {α : Type} (r : α) (A B : S α) :
    own r A B r ↔ A r ∨ B r := by
  classical
  by_cases h : A = atom r ∨ B = atom r
  · have hm : A r ∨ B r := by
      rcases h with h | h
      · exact Or.inl (h.symm ▸ (rfl : atom r r))
      · exact Or.inr (h.symm ▸ (rfl : atom r r))
    simp [own, h, atom, hm]
  · simp only [own, ite_eq_right h, join]

theorem own_mem_other {α : Type} (r k : α) (hrk : r ≠ k) (A B : S α) :
    own r A B k ↔ (A k ∨ B k) ∧ A ≠ atom r ∧ B ≠ atom r := by
  classical
  by_cases h : A = atom r ∨ B = atom r
  · have hn : ¬ (A ≠ atom r ∧ B ≠ atom r) := by
      rintro ⟨ha, hb⟩
      exact h.elim ha hb
    simp only [own, ite_eq_left h, atom, Ne.symm hrk]
    constructor
    · exact False.elim
    · intro hx
      exact hn hx.2
  · have ha : A ≠ atom r := fun e => h (Or.inl e)
    have hb : B ≠ atom r := fun e => h (Or.inr e)
    simp only [own, ite_eq_right h, join]
    exact ⟨fun hm => ⟨hm, ha, hb⟩, fun hm => hm.1⟩

/-- Exactly the information visible to contexts testing whether k is a
    possible winner. A singleton k and any ambiguous set containing k
    intentionally have the same view. -/
def SameView {α : Type} (k : α) (A B : S α) : Prop :=
  (A k ↔ B k) ∧ ∀ i, i ≠ k → (A = atom i ↔ B = atom i)

theorem sameView_own {α : Type} (k r : α) (A B C D : S α)
    (hA : NE A) (hB : NE B) (hC : NE C) (hD : NE D)
    (hAC : SameView k A C) (hBD : SameView k B D) :
    SameView k (own r A B) (own r C D) := by
  classical
  constructor
  · by_cases hr : r = k
    · subst r
      simp only [own_mem_owner]
      exact or_congr hAC.1 hBD.1
    · rw [own_mem_other r k hr, own_mem_other r k hr]
      have ha := hAC.2 r hr
      have hb := hBD.2 r hr
      constructor
      · rintro ⟨hm, hnA, hnB⟩
        refine ⟨hm.elim (fun h => Or.inl (hAC.1.mp h))
          (fun h => Or.inr (hBD.1.mp h)), ?_, ?_⟩
        · exact fun h => hnA (ha.mpr h)
        · exact fun h => hnB (hb.mpr h)
      · rintro ⟨hm, hnC, hnD⟩
        refine ⟨hm.elim (fun h => Or.inl (hAC.1.mpr h))
          (fun h => Or.inr (hBD.1.mpr h)), ?_, ?_⟩
        · exact fun h => hnC (ha.mp h)
        · exact fun h => hnD (hb.mp h)
  · intro i hi
    by_cases hr : r = i
    · subst r
      rw [own_eq_owner_iff i A B hA hB, own_eq_owner_iff i C D hC hD]
      exact or_congr (hAC.2 i hi) (hBD.2 i hi)
    · rw [own_eq_other_iff r i hr A B hA hB,
        own_eq_other_iff r i hr C D hC hD]
      exact and_congr (hAC.2 i hi) (hBD.2 i hi)

inductive Term (α β : Type) where
  | win (i : α)
  | var (j : β)
  | node (r : α) (left right : Term α β)

noncomputable def denote {α β : Type} (t : Term α β) (v : β → S α) : S α :=
  match t with
  | .win i => atom i
  | .var j => v j
  | .node r left right => own r (denote left v) (denote right v)

theorem denote_ne {α β : Type} (t : Term α β) (v : β → S α)
    (hv : ∀ j, NE (v j)) : NE (denote t v) := by
  induction t with
  | win i => exact atom_ne i
  | var j => exact hv j
  | node r left right hl _ => exact own_ne r _ _ hl

theorem denote_sameView {α β : Type} (t : Term α β) (k : α)
    (v w : β → S α) (hv : ∀ j, NE (v j)) (hw : ∀ j, NE (w j))
    (he : ∀ j, SameView k (v j) (w j)) :
    SameView k (denote t v) (denote t w) := by
  induction t with
  | win i => exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
  | var j => exact he j
  | node r left right hl hr =>
    exact sameView_own k r _ _ _ _ (denote_ne left v hv)
      (denote_ne right v hv) (denote_ne left w hw) (denote_ne right w hw) hl hr

def ContextualAt {α : Type} (k : α) (A B : S α) : Prop :=
  ∀ t : Term α Unit,
    denote t (fun _ => A) k ↔ denote t (fun _ => B) k

/-- Full abstraction for one player's possible-winner observation. -/
theorem contextualAt_iff {α : Type} (k : α) (A B : S α)
    (hA : NE A) (hB : NE B) : ContextualAt k A B ↔ SameView k A B := by
  classical
  constructor
  · intro h
    refine ⟨h (.var ()), ?_⟩
    intro i hi
    have hp := h (.node i (.var ()) (.win k))
    have hk : atom k ≠ atom i := fun he => hi (atom_inj.mp he).symm
    change own i A (atom k) k ↔ own i B (atom k) k at hp
    rw [own_mem_other i k hi, own_mem_other i k hi] at hp
    have hneq : A ≠ atom i ↔ B ≠ atom i := by
      exact ⟨fun ha => (hp.mp ⟨Or.inr rfl, ha, hk⟩).2.1,
        fun hb => (hp.mpr ⟨Or.inr rfl, hb, hk⟩).2.1⟩
    constructor <;> intro he <;> apply Classical.byContradiction <;> intro hn
    · exact (hneq.mpr hn) he
    · exact (hneq.mp hn) he
  · intro h t
    exact (denote_sameView t k (fun _ => A) (fun _ => B)
      (fun _ => hA) (fun _ => hB) (fun _ => h)).1

/-- One ambiguous fallback omitting k can be reused for every variable. -/
noncomputable def representative {α : Type} (k : α) (fallback A : S α) : S α := by
  classical
  exact if A k then atom k else
    if ∃ i, A = atom i then A else fallback

theorem representative_ne {α : Type} (k : α) (fallback A : S α)
    (hf : NE fallback) : NE (representative k fallback A) := by
  classical
  unfold representative
  split
  · exact atom_ne k
  · split
    · rename_i h
      rcases h with ⟨i, rfl⟩
      exact atom_ne i
    · exact hf

theorem representative_range {α : Type} (k : α) (fallback A : S α) :
    (∃ i, representative k fallback A = atom i) ∨
      representative k fallback A = fallback := by
  classical
  unfold representative
  split
  · exact Or.inl ⟨k, rfl⟩
  · split
    · rename_i h
      exact Or.inl h
    · exact Or.inr rfl

theorem representative_sameView {α : Type} (k : α) (fallback A : S α)
    (hfk : ¬ fallback k) (hfm : Multiple fallback) :
    SameView k A (representative k fallback A) := by
  classical
  unfold representative
  split
  · rename_i hm
    constructor
    · exact ⟨fun _ => rfl, fun _ => hm⟩
    · intro i hi
      have ha : A ≠ atom i := by
        intro he
        have hki : atom i k := by rw [← he]; exact hm
        exact hi hki.symm
      simp only [ha, atom_inj, Ne.symm hi]
  · rename_i hm
    split
    · exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
    · rename_i hn
      constructor
      · simp only [hm, hfk]
      · intro i _
        have ha : A ≠ atom i := fun he => hn ⟨i, he⟩
        have hp : fallback ≠ atom i := by
          intro he
          apply multiple_not_sub_atom fallback hfm i
          intro x hx
          rw [he] at hx
          exact hx
        simp only [ha, hp]

/-- Any failed equation, at any arity, has a witness using only singleton
    values and ONE prescribed pair omitting the observed player k. -/
theorem small_counterexample {α β : Type} (left right : Term α β)
    (k a b : α) (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b)
    (v : β → S α) (hv : ∀ j, NE (v j))
    (hfail : ¬ (denote left v k ↔ denote right v k)) :
    ∃ w : β → S α,
      (∀ j, NE (w j)) ∧
      (∀ j, (∃ i, w j = atom i) ∨ w j = join (atom a) (atom b)) ∧
      ¬ (denote left w k ↔ denote right w k) := by
  let fallback := join (atom a) (atom b)
  have hfn : NE fallback := ⟨a, Or.inl rfl⟩
  have hfm : Multiple fallback := ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
  have hfk : ¬ fallback k := by simp [fallback, join, atom, Ne.symm hak, Ne.symm hbk]
  let w := fun j => representative k fallback (v j)
  have hw : ∀ j, NE (w j) := fun j => representative_ne k fallback (v j) hfn
  have he : ∀ j, SameView k (v j) (w j) :=
    fun j => representative_sameView k fallback (v j) hfk hfm
  refine ⟨w, hw, (fun j => representative_range k fallback (v j)), ?_⟩
  intro h
  exact hfail (((denote_sameView left k v w hv hw he).1.trans h).trans
    (denote_sameView right k v w hv hw he).1.symm)

def ValidEquation {α β : Type} (left right : Term α β) : Prop :=
  ∀ v : β → S α, (∀ j, NE (v j)) → denote left v = denote right v

/-- A fixed input test domain suffices at EVERY arity if it includes the
    singletons and, for each k, some ambiguous set omitting k. -/
theorem complete_test_domain {α β : Type} (D : S α → Prop)
    (hatoms : ∀ i, D (atom i))
    (hcover : ∀ k, ∃ F, D F ∧ NE F ∧ Multiple F ∧ ¬ F k)
    (left right : Term α β) :
    ValidEquation left right ↔
      ∀ v : β → S α, (∀ j, NE (v j)) → (∀ j, D (v j)) →
        denote left v = denote right v := by
  constructor
  · intro h v hv _
    exact h v hv
  · intro h v hv
    funext k
    apply propext
    rcases hcover k with ⟨F, hDF, hFn, hFm, hFk⟩
    let w := fun j => representative k F (v j)
    have hw : ∀ j, NE (w j) := fun j => representative_ne k F (v j) hFn
    have hDw : ∀ j, D (w j) := by
      intro j
      rcases representative_range k F (v j) with ⟨i, hi⟩ | hi
      · rw [show w j = atom i from hi]
        exact hatoms i
      · rw [show w j = F from hi]
        exact hDF
    have he : ∀ j, SameView k (v j) (w j) :=
      fun j => representative_sameView k F (v j) hFk hFm
    have hl := (denote_sameView left k v w hv hw he).1
    have hr := (denote_sameView right k v w hv hw he).1
    rw [h w hw hDw] at hl
    exact hl.trans hr.symm

/-- No family of player perspectives loses a set-membership distinction. -/
theorem perspectives_separate {α : Type} (A B : S α)
    (h : ∀ k, SameView k A B) : A = B := by
  funext k
  exact propext (h k).1

/-- The key constraint on all algebra congruences: identifying an atom with
    anything else forces it into the class of the full winner set. -/
theorem atom_collapse_to_top {α : Type} (r s : α) (hsr : s ≠ r)
    (R : S α → S α → Prop)
    (hcomp : ∀ i A B C D, NE A → NE B → NE C → NE D →
      R A C → R B D → R (own i A B) (own i C D))
    (htop : R (fun _ => True) (fun _ => True))
    (A : S α) (hAn : NE A) (hA : A ≠ atom r) (h : R (atom r) A) :
    R (atom r) (fun _ => True) := by
  classical
  let top : S α := fun _ => True
  have htr : top ≠ atom r := by
    intro he
    have hm : top s := True.intro
    rw [he] at hm
    exact hsr hm
  have hl : own r (atom r) top = atom r := by simp [own]
  have hr : own r A top = top := by
    have hn : ¬ (A = atom r ∨ top = atom r) := fun e => e.elim hA htr
    simp only [own, ite_eq_right hn]
    funext x
    apply propext
    simp [join, top]
  have htn : NE top := ⟨r, True.intro⟩
  have he := hcomp r (atom r) top A top (atom_ne r) htn hAn htn h htop
  rw [hl, hr] at he
  exact he

#print axioms sameView_own
#print axioms contextualAt_iff
#print axioms small_counterexample
#print axioms complete_test_domain
#print axioms atom_collapse_to_top
end MinimalChoice
