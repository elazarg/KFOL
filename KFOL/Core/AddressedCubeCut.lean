module

public import KFOL.Core.BichainCubeCuts
public import KFOL.Core.OfferLock

/-! # Transport of a cut to a source sample on addressed inputs

A probe is either permanent or one copy of a logical loss. The two primary
singleton flags at a probe must imply the corresponding encoded endpoint.
Only the auxiliary owner needs a separate local obstruction.
-/

@[expose] public section

namespace KFOL.Core.AddressedCubeCut

open Bichain
attribute [local instance] Equational.coreStructure

variable {Role Rail Label Row Probe : Type*} [DecidableEq Role] [DecidableEq Row]
abbrev Word (Role Rail : Type*) := Equational.Term (Equational.CoreSymbol Role) Rail

structure Encoding (Role Rail Label Row Probe : Type*) (rows : Row → Label → Value) where
  left : Role
  right : Role
  aux : Role
  distinct : left ≠ right
  pos : (Label → Bool) → Rail → Bool
  neg : (Label → Bool) → Rail → Bool
  tag : Probe → Option Row
  values : Probe → Rail → WinnerSet Role
  observe : Probe → Role
  head : ∀ u, ∃ p, tag p = none ∧ observe p ∈ (values p u).val
  owners : ∀ p u r, values p u = WinnerSet.singleton r → r = left ∨ r = right ∨ r = aux ∨ r = observe p
  posRow : ∀ p, left ≠ observe p → (∃ u, values p u = WinnerSet.singleton left) →
    ∃ z, tag p = some z ∧ ∀ u, values p u = WinnerSet.singleton left → pos (cubeLower (rows z)) u = true
  negRow : ∀ p, right ≠ observe p → (∃ u, values p u = WinnerSet.singleton right) →
    ∃ z, tag p = some z ∧ ∀ u, values p u = WinnerSet.singleton right → neg (cubeUpper (rows z)) u = true

namespace Encoding

variable {rows : Row → Label → Value} (E : Encoding Role Rail Label Row Probe rows)

def Active (S : Finset Row) (p : Probe) : Prop := ∀ z, E.tag p = some z → z ∈ S

def Quiet (S : Finset Row) (t : Word Role Rail) : Prop :=
  ∀ p, E.Active S p → E.observe p ∉ (t.realize (E.values p)).val

omit [DecidableEq Role] [DecidableEq Row] in
private theorem active_mono {S T : Finset Row} (sub : S ⊆ T) {p : Probe} (h : E.Active S p) :
    E.Active T p := fun z hz => sub (h z hz)

omit [DecidableEq Role] [DecidableEq Row] in
private theorem quiet_mono {S T : Finset Row} (sub : S ⊆ T) {t : Word Role Rail} (h : E.Quiet T t) :
    E.Quiet S t := fun p hp => h p (E.active_mono sub hp)

def Demands (x y : Label → Bool) (t : Word Role Rail) : Prop :=
  profile E.left (E.pos x) t = true ∧ profile E.right (E.neg y) t = true

omit [DecidableEq Row] in
private theorem child {x y : Label → Bool} {r : Role} {s t : Word Role Rail}
    (h : E.Demands x y (choiceTerm r s t)) : E.Demands x y s ∨ E.Demands x y t := by
  obtain ⟨hl, hr⟩ := h
  by_cases l : r = E.left
  · have n : r ≠ E.right := l ▸ E.distinct
    simp only [profile_choice, ite_eq_left l, Bool.or_eq_true] at hl
    simp only [profile_choice, ite_eq_right n, Bool.and_eq_true] at hr
    exact hl.elim (fun h => Or.inl ⟨h, hr.1⟩) (fun h => Or.inr ⟨h, hr.2⟩)
  · simp only [profile_choice, ite_eq_right l, Bool.and_eq_true] at hl
    by_cases r' : r = E.right
    · simp only [profile_choice, ite_eq_left r', Bool.or_eq_true] at hr
      exact hr.elim (fun h => Or.inl ⟨hl.1, h⟩) (fun h => Or.inr ⟨hl.2, h⟩)
    · simp only [profile_choice, ite_eq_right r', Bool.and_eq_true] at hr
      exact Or.inl ⟨hl.1, hr.1⟩

private theorem input_atom (t : Word Role Rail) (v : Rail → WinnerSet Role) (r : Role)
    (atom : t.realize v = WinnerSet.singleton r) : ∃ u, v u = WinnerSet.singleton r := by
  classical
  by_contra! no
  have pos := (winnerSet_eq_singleton_iff_profile t r v).mp atom
  have e : (fun u => decide (v u = WinnerSet.singleton r)) = fun _ => false :=
    funext fun u => decide_eq_false (no u)
  rw [e, profile_false] at pos
  contradiction

/-- On a covered cell the address calculation need only exclude an auxiliary
atom of a *single* probe. The remaining obstruction is the native cube cut. -/
theorem no_word_of_cut
    (leftOK rightOK : (Label → Bool) → Prop)
    (left_closed : ∀ p z, E.tag p = some z → (∃ u, E.values p u = WinnerSet.singleton E.left) →
      leftOK (cubeLower (rows z)))
    (right_closed : ∀ p z, E.tag p = some z → (∃ u, E.values p u = WinnerSet.singleton E.right) →
      rightOK (cubeUpper (rows z)))
    (lock : ∀ {S x y}, leftOK x → rightOK y →
      (∀ f, x f = true → y f = false → ∃ z ∈ S, rows z f = .possible) →
      ∀ t : Word Role Rail, E.Quiet S t → E.Demands x y t →
        ∀ p, E.Active S p → t.realize (E.values p) ≠ WinnerSet.singleton E.aux)
    {S : Finset Row} {x y : Label → Bool} (cut : CubeCut rows S (.separate x y))
    (hx : leftOK x) (hy : rightOK y) :
    ∀ t : Word Role Rail, E.Quiet S t → ¬ E.Demands x y t := by
  classical
  generalize eq : CubeQuery.separate x y = query at cut
  induction cut generalizing x y with
  | @cover budget selected query sub covered _ _ ihl ihr =>
    cases eq
    intro w quiet h
    have noAtom (t : Word Role Rail) (safe : E.Quiet selected t) (d : E.Demands x y t)
        (p : Probe) (live : E.Active selected p) (r : Role) :
        t.realize (E.values p) ≠ WinnerSet.singleton r := by
      intro atom
      obtain ⟨u, hu⟩ := input_atom t _ r atom
      have unseen : r ≠ E.observe p := by
        rintro rfl
        exact safe p live (by rw [atom]; rfl)
      obtain l | r' | aux | obs := E.owners p u r hu
      · subst r
        obtain ⟨z, tag, inc⟩ := E.posRow p unseen ⟨u, hu⟩
        have zmem := live z tag
        apply ihl z zmem (left_closed p z tag ⟨u, hu⟩) hy rfl t
          (E.quiet_mono (Finset.erase_subset _ _) safe)
        exact ⟨profile_mono _ _ _ (by simpa only [decide_eq_true_eq] using inc) t
          ((winnerSet_eq_singleton_iff_profile t _ _).mp atom), d.2⟩
      · subst r
        obtain ⟨z, tag, inc⟩ := E.negRow p unseen ⟨u, hu⟩
        have zmem := live z tag
        apply ihr z zmem hx (right_closed p z tag ⟨u, hu⟩) rfl t
          (E.quiet_mono (Finset.erase_subset _ _) safe)
        exact ⟨d.1, profile_mono _ _ _ (by simpa only [decide_eq_true_eq] using inc) t
          ((winnerSet_eq_singleton_iff_profile t _ _).mp atom)⟩
      · subst r
        exact lock hx hy (fun f xf yf => covered f ⟨xf, yf⟩) t safe d p live atom
      · exact unseen obs
    have descend : ∀ t : Word Role Rail, E.Quiet selected t → ¬ E.Demands x y t := by
      intro t
      induction t using induction_choice with
      | var u =>
        intro hs _
        obtain ⟨p, tag, mem⟩ := E.head u
        exact hs p (by simp [Active, tag]) mem
      | choice r s t ihs iht =>
        intro safe d
        have unions (p : Probe) (hp : E.Active selected p) :
            E.observe p ∉ (s.realize (E.values p)).val ∧ E.observe p ∉ (t.realize (E.values p)).val := by
          have unabsorbed : ¬(s.realize (E.values p) = WinnerSet.singleton r ∨
              t.realize (E.values p) = WinnerSet.singleton r) :=
            fun hit => noAtom _ safe d p hp r ((WinnerSet.choice_eq_owner_iff _ _ _).mpr hit)
          have hp' := safe p hp
          change E.observe p ∉ (WinnerSet.choice r (s.realize (E.values p)) (t.realize (E.values p))).val at hp'
          simpa only [WinnerSet.choice, ite_eq_right unabsorbed, WinnerSet.union,
            Set.mem_union, not_or] using hp'
        exact (E.child d).elim (ihs (fun p hp => (unions p hp).1)) (iht (fun p hp => (unions p hp).2))
    exact descend w (E.quiet_mono sub quiet) h

end Encoding
end KFOL.Core.AddressedCubeCut
