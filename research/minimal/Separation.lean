/-
Disjoint output requirements are witnessed by one common syntactic leaf.
This module includes internal role permutations explicitly. No Mathlib.
-/
import Synthesis

set_option autoImplicit false
namespace MinimalChoice

def DisjointFamily {α γ : Type} (D : γ → S α) : Prop :=
  ∀ i j, i ≠ j → ∀ x, D i x → D j x → False

theorem own_separation {α γ : Type} (r : α) (A B D : γ → S α)
    (hd : DisjointFamily D) (h : ∀ i, Sub (own r (A i) (B i)) (D i)) :
    (∀ i, Sub (A i) (D i)) ∨ (∀ i, Sub (B i) (D i)) := by
  classical
  by_cases ha : ∀ i, Sub (A i) (D i)
  · exact Or.inl ha
  · right
    obtain ⟨i, hi⟩ := Classical.not_forall.mp ha
    have collapse : A i = atom r ∨ B i = atom r := by
      apply Classical.byContradiction
      intro hn
      apply hi
      intro x hx
      apply h i x
      simp only [own, ite_eq_right hn, join]
      exact Or.inl hx
    have hr : D i r := by
      apply h i r
      simp [own, collapse, atom]
    have hb : B i = atom r := by
      rcases collapse with hc | hc
      · exfalso
        apply hi
        intro x hx
        rw [hc] at hx
        change x = r at hx
        exact hx ▸ hr
      · exact hc
    intro j x hx
    by_cases he : j = i
    · subst j
      rw [hb] at hx
      change x = r at hx
      exact hx ▸ hr
    · have hnr : ¬ D j r := fun hj => hd i j (Ne.symm he) r hr hj
      have hn : ¬ (A j = atom r ∨ B j = atom r) := by
        intro hc
        apply hnr
        apply h j r
        simp [own, hc, atom]
      apply h j x
      simp only [own, ite_eq_right hn, join]
      exact Or.inr hx

structure RolePerm (α : Type) where
  apply : α → α
  injective : Function.Injective apply
  surjective : Function.Surjective apply

def RolePerm.identity {α : Type} : RolePerm α :=
  ⟨id, fun _ _ h => h, fun x => ⟨x, rfl⟩⟩

def RolePerm.comp {α : Type} (p q : RolePerm α) : RolePerm α :=
  ⟨fun x => p.apply (q.apply x),
   fun _ _ he => q.injective (p.injective he), by
    intro y
    obtain ⟨z, hz⟩ := p.surjective y
    obtain ⟨x, hx⟩ := q.surjective z
    exact ⟨x, by simp [hx, hz]⟩⟩

def permSet {α : Type} (p : RolePerm α) (A : S α) : S α :=
  fun y => ∃ x, A x ∧ p.apply x = y

inductive FullTerm (α β : Type) where
  | win : α → FullTerm α β
  | var : β → FullTerm α β
  | node : α → FullTerm α β → FullTerm α β → FullTerm α β
  | rename : RolePerm α → FullTerm α β → FullTerm α β

noncomputable def FullTerm.denote {α β : Type} (t : FullTerm α β)
    (v : β → S α) : S α :=
  match t with
  | .win r => atom r
  | .var j => v j
  | .node r p q => own r (p.denote v) (q.denote v)
  | .rename p t => permSet p (t.denote v)

inductive Source (α β : Type) where
  | win : α → Source α β
  | input : β → RolePerm α → Source α β

def Source.rename {α β : Type} (p : RolePerm α) : Source α β → Source α β
  | .win r => .win (p.apply r)
  | .input j q => .input j (p.comp q)

def Source.denote {α β : Type} (s : Source α β) (v : β → S α) : S α :=
  match s with
  | .win r => atom r
  | .input j p => permSet p (v j)

def FullTerm.sources {α β : Type} : FullTerm α β → List (Source α β)
  | .win r => [.win r]
  | .var j => [.input j .identity]
  | .node _ p q => p.sources ++ q.sources
  | .rename p t => t.sources.map (Source.rename p)

theorem Source.rename_sub {α β : Type} (p : RolePerm α) (s : Source α β)
    (v : β → S α) (D : S α)
    (h : Sub (s.denote v) (fun x => D (p.apply x))) :
    Sub ((s.rename p).denote v) D := by
  intro y hy
  cases s with
  | win r =>
    change y = p.apply r at hy
    subst y
    exact h r rfl
  | input j q =>
    obtain ⟨x, hx, he⟩ := hy
    subst y
    exact h (q.apply x) ⟨x, hx, rfl⟩

theorem FullTerm.separation {α β γ : Type} (t : FullTerm α β)
    (v : γ → β → S α) (D : γ → S α) (hd : DisjointFamily D)
    (h : ∀ i, Sub (t.denote (v i)) (D i)) :
    ∃ s ∈ t.sources, ∀ i, Sub (s.denote (v i)) (D i) := by
  induction t generalizing D with
  | win r => exact ⟨.win r, by simp [sources], h⟩
  | var j =>
    refine ⟨.input j .identity, by simp [sources], ?_⟩
    intro i y hy
    obtain ⟨x, hx, he⟩ := hy
    subst y
    exact h i x hx
  | node r p q hp hq =>
    rcases own_separation r (fun i => p.denote (v i))
        (fun i => q.denote (v i)) D hd h with hh | hh
    · obtain ⟨s, hs, he⟩ := hp D hd hh
      exact ⟨s, by simp [sources, hs], he⟩
    · obtain ⟨s, hs, he⟩ := hq D hd hh
      exact ⟨s, by simp [sources, hs], he⟩
  | rename p t ih =>
    let D' : γ → S α := fun i x => D i (p.apply x)
    have hd' : DisjointFamily D' := by
      intro i j hij x hi hj
      exact hd i j hij (p.apply x) hi hj
    have h' : ∀ i, Sub (t.denote (v i)) (D' i) := by
      intro i x hx
      exact h i (p.apply x) ⟨x, hx, rfl⟩
    obtain ⟨s, hs, he⟩ := ih D' hd' h'
    refine ⟨s.rename p, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨s, hs, rfl⟩
    · intro i
      exact s.rename_sub p (v i) (D i) (he i)

/-- Two disjoint output regions exclude a ground winner as the common leaf. -/
theorem FullTerm.input_separation {α β γ : Type} (t : FullTerm α β)
    (v : γ → β → S α) (D : γ → S α) (hd : DisjointFamily D)
    (i j : γ) (hij : i ≠ j) (h : ∀ k, Sub (t.denote (v k)) (D k)) :
    ∃ b p, Source.input b p ∈ t.sources ∧
      ∀ k, Sub (permSet p (v k b)) (D k) := by
  obtain ⟨s, hs, he⟩ := t.separation v D hd h
  cases s with
  | win r => exact False.elim (hd i j hij r (he i r rfl) (he j r rfl))
  | input b p => exact ⟨b, p, hs, he⟩

/-- All distinct singleton outputs are accounted for by one common input leaf. -/
theorem FullTerm.atomic_separation {α β γ : Type} (t : FullTerm α β)
    (v : γ → β → α) (out : γ → α) (ho : Function.Injective out)
    (i j : γ) (hij : i ≠ j)
    (h : ∀ k, t.denote (fun b => atom (v k b)) = atom (out k)) :
    ∃ b p, Source.input b p ∈ t.sources ∧ ∀ k, p.apply (v k b) = out k := by
  have hd : DisjointFamily (fun k => atom (out k)) := by
    intro k l hkl x hk hl
    exact hkl (ho (hk.symm.trans hl))
  have hh : ∀ k, Sub (t.denote (fun b => atom (v k b))) (atom (out k)) := by
    intro k x hx
    rw [h k] at hx
    exact hx
  obtain ⟨b, p, hp, he⟩ := t.input_separation (fun k b => atom (v k b))
    (fun k => atom (out k)) hd i j hij hh
  exact ⟨b, p, hp, fun k => he k (p.apply (v k b)) ⟨v k b, rfl, rfl⟩⟩

noncomputable def resetFold {α : Type} (roles : List α) (A B : S α) : S α :=
  match roles with
  | [] => A
  | r :: rest => own r (resetFold rest A B) B

theorem resetFold_atom {α : Type} (roles : List α) (A : S α) (r : α)
    (hr : r ∈ roles) : resetFold roles A (atom r) = atom r := by
  induction roles with
  | nil => simp at hr
  | cons i rest ih =>
    rcases List.mem_cons.mp hr with he | he
    · subst i
      simp [resetFold, own]
    · simp only [resetFold, ih he]
      exact own_idem i (atom r)

theorem resetFold_multiple {α : Type} (roles : List α) (A B : S α)
    (hb : Multiple B) : resetFold roles (join B A) B = join B A := by
  induction roles with
  | nil => rfl
  | cons r rest ih =>
    simp only [resetFold, ih]
    exact own_extend_multiple r B A hb

noncomputable def relativeReset {α : Type} (roles : List α) (A B : S α) : S α :=
  resetFold roles (join B A) B

theorem relativeReset_atom {α : Type} (roles : List α) (A : S α) (r : α)
    (hr : r ∈ roles) : relativeReset roles A (atom r) = atom r :=
  resetFold_atom roles _ r hr

theorem relativeReset_multiple {α : Type} (roles : List α) (A B : S α)
    (hb : Multiple B) : relativeReset roles A B = join B A :=
  resetFold_multiple roles A B hb

end MinimalChoice

#print axioms MinimalChoice.own_separation
#print axioms MinimalChoice.FullTerm.separation
#print axioms MinimalChoice.FullTerm.input_separation
#print axioms MinimalChoice.FullTerm.atomic_separation
#print axioms MinimalChoice.relativeReset_atom
#print axioms MinimalChoice.relativeReset_multiple
