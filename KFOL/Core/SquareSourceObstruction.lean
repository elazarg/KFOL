module

public import KFOL.Core.FacetPosting
public import KFOL.Core.SingletonProfileAbsorption

/-! # A four-cycle of losses with no common source witness -/

@[expose] public section
namespace KFOL.Core.SquareSourceObstruction

inductive Input | w | p | q | u | v | h
  deriving DecidableEq

inductive Row | positive | loseH | loseU | loseV | loseW
  deriving DecidableEq

instance : Fintype Input := ⟨{.w, .p, .q, .u, .v, .h}, by intro i; cases i <;> simp⟩
instance : Fintype Row := ⟨{.positive, .loseH, .loseU, .loseV, .loseW}, by intro d; cases d <;> simp⟩

inductive Status | hole | head | atom (r : Fin 3)
  deriving DecidableEq

/-- The columns are `w,p,q,u,v,h`. Owners 0, 1, and 2 are respectively
the paper's a, b, and k. -/
def status : Row → Input → Status
  | .positive, .u | .positive, .q => .atom 0
  | .positive, .v | .positive, .p => .atom 1
  | .positive, .h | .loseH, .h | .loseU, .u | .loseV, .v | .loseW, .w => .head
  | .loseH, .u | .loseH, .v => .atom 2
  | .loseU, .w | .loseV, .q | .loseW, .u => .atom 0
  | .loseU, .p | .loseV, .w | .loseW, .v => .atom 1
  | _, _ => .hole

def observer : Row → Fin 3
  | .loseH => 0
  | _ => 2

/-- A marked head carries the full menu and a hole carries every winner
except the observer. -/
noncomputable def values (d : Row) (i : Input) : WinnerSet (Fin 3) :=
  match status d i with
  | .head => ⟨Set.univ, Set.univ_nonempty⟩
  | .hole => Sources.representative (Function.Embedding.refl _) (observer d) .neutral
  | .atom r => WinnerSet.singleton r

private theorem hole_ambiguous (k : Fin 3) :
    (Sources.representative (Function.Embedding.refl _) k .neutral).Ambiguous := by
  intro r he
  by_cases hr : r = k
  · subst r
    have impossible := Sources.representative_omits (Function.Embedding.refl _) k .neutral
    rw [he] at impossible
    exact impossible rfl
  · have h := (Sources.representative_atom_iff _ k .neutral ⟨r, hr⟩).1 he
    cases h

private theorem atom_iff (d : Row) (i : Input) (r : Fin 3) :
    values d i = WinnerSet.singleton r ↔ status d i = .atom r := by
  unfold values
  cases h : status d i with
  | head =>
    have hn : (⟨Set.univ, Set.univ_nonempty⟩ : WinnerSet (Fin 3)) ≠ WinnerSet.singleton r := by
      intro he
      obtain ⟨s, hs⟩ := exists_ne r
      have hm : s ∈ (⟨Set.univ, Set.univ_nonempty⟩ : WinnerSet (Fin 3)).val := Set.mem_univ s
      rw [he] at hm
      exact hs hm
    simp [hn]
  | hole => simp [hole_ambiguous _ r]
  | atom => simp

private theorem observer_mem_iff (d : Row) (i : Input) :
    observer d ∈ (values d i).val ↔ status d i = .head := by
  have hs : ∀ (d : Row) (i : Input), status d i ≠ .atom (observer d) := by decide
  unfold values
  cases h : status d i with
  | head => simp
  | hole => simp
  | atom r =>
    have hr : r ≠ observer d := fun he => hs d i (h.trans (congrArg Status.atom he))
    simp [Ne.symm hr]

private abbrev CoreWord := Equational.Term (Equational.CoreSymbol (Fin 3)) Input
attribute [local instance] Equational.coreStructure

private theorem profile_at (t : CoreWord) (d : Row) (r : Fin 3) :
    t.realize (values d) = WinnerSet.singleton r ↔
      profile r (fun i => decide (status d i = .atom r)) t = true := by
  classical
  rw [winnerSet_eq_singleton_iff_profile]
  simp only [atom_iff]

private theorem atoms_transfer (t : CoreWord) {d e : Row} (r : Fin 3)
    (h : ∀ i, status d i = .atom r → status e i = .atom r) :
    t.realize (values d) = WinnerSet.singleton r →
      t.realize (values e) = WinnerSet.singleton r :=
  fun hd => (profile_at t e r).2 (profile_mono r _ _ (fun i hi =>
    decide_eq_true (h i (of_decide_eq_true hi))) t ((profile_at t d r).1 hd))

private theorem ambiguous_at_losses (t : CoreWord)
    (positive : 2 ∈ (t.realize (values .positive)).val)
    (quiet : ∀ d, d ≠ .positive → observer d ∉ (t.realize (values d)).val) :
    ∀ d, (t.realize (values d)).Ambiguous := by
  have pos : (t.realize (values .positive)).Ambiguous := by
    intro r hr
    have he : (2 : Fin 3) = r := by simpa only [hr, WinnerSet.val_singleton, Set.mem_singleton_iff] using positive
    subst r
    have empty : (fun i => decide (status .positive i = .atom 2)) = (fun _ => false) := by
      funext i; cases i <;> rfl
    have h := (profile_at t .positive 2).1 hr
    rw [empty, profile_false] at h
    cases h
  have w : (t.realize (values .loseW)).Ambiguous := by
    intro r hr
    apply pos r (atoms_transfer t r _ hr)
    exact (by decide : ∀ (s : Fin 3) i, status .loseW i = .atom s →
      status .positive i = .atom s) r
  have tip (d : Row) (r0 : Fin 3)
      (mono : ∀ r : Fin 3, r ≠ r0 → ∀ i, status d i = .atom r → status .positive i = .atom r)
      (onlyW : ∀ i, status d i = .atom r0 ↔ i = .w) : (t.realize (values d)).Ambiguous := by
    intro r hr
    by_cases he : r = r0
    · subst r
      have hp := (profile_at t d r0).1 hr
      simp only [onlyW] at hp
      rcases eq_singleton_or_subset_of_profile_singleton t r0 .w (values .loseW) hp with hs | hsub
      · exact w r0 hs
      · exact quiet .loseW (by decide) (hsub ((observer_mem_iff .loseW .w).2 rfl))
    · exact pos r (atoms_transfer t r (mono r he) hr)
  intro d
  cases d with
  | positive => exact pos
  | loseW => exact w
  | loseU => exact tip .loseU 0 (by decide) (by decide)
  | loseV => exact tip .loseV 1 (by decide) (by decide)
  | loseH =>
    intro r hr
    by_cases he : r = 2
    · subst r
      obtain ⟨i, hi, supplies⟩ := exists_source_of_winning_profile 2 _ t ((profile_at t .loseH 2).1 hr)
      have member : i = .u ∨ i = .v := (by decide : ∀ i : Input,
        status .loseH i = .atom 2 → i = .u ∨ i = .v) i (of_decide_eq_true hi)
      let lossAt (x : Input) : Row := if x = .u then .loseU else .loseV
      have marks : status (lossAt i) i = .head := by rcases member with rfl | rfl <;> decide
      have hk : observer (lossAt i) = 2 := by rcases member with rfl | rfl <;> decide
      apply quiet (lossAt i) (by rcases member with rfl | rfl <;> decide)
      rw [hk]
      apply supplies (values (lossAt i)) (hk ▸ ((observer_mem_iff (lossAt i) i).2 marks))
      intro j hj
      left
      intro s hs
      have noAtom : ∀ (i j : Input), (i = .u ∨ i = .v) → status .loseH j = .atom 2 →
          ∀ s, status (lossAt i) j ≠ .atom s := by decide
      exact noAtom i j member (of_decide_eq_true hj) s ((atom_iff _ _ _).1 hs)
    · exact pos r (atoms_transfer t r ((by decide : ∀ r : Fin 3, r ≠ 2 → ∀ i,
        status .loseH i = .atom r → status .positive i = .atom r) r he) hr)

/-- No core term supplies the positive hub probe and simultaneously omits
the marked winner on each of the four loss probes. -/
theorem no_core_witness (t : Term (Fin 3) Input) (ht : t.IsCore)
    (positive : 2 ∈ (t.eval (values .positive)).val) :
    ∃ d : Row, d ≠ .positive ∧ observer d ∈ (t.eval (values d)).val := by
  classical
  suffices aux : ∀ s : CoreWord, 2 ∈ (s.realize (values .positive)).val →
      ¬(∀ d, d ≠ .positive → observer d ∉ (s.realize (values d)).val) by
    have agrees (d) : (Equational.Core.encode t ht).realize (values d) = t.eval (values d) := by
      rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
    by_contra! hn
    exact aux _ ((agrees .positive).symm ▸ positive) (fun d hd => by rw [agrees d]; exact hn d hd)
  intro s
  induction s using induction_choice with
  | var x =>
    intro hp hn
    have hh : x = .h := (by decide : ∀ i : Input, status .positive i = .head → i = .h) x
      ((observer_mem_iff .positive x).1 hp)
    subst x
    exact hn .loseH (by decide) ((observer_mem_iff .loseH .h).2 rfl)
  | choice r s t hs ht =>
    intro hp hn
    have ha := ambiguous_at_losses (choiceTerm r s t) hp hn
    have vals (d : Row) : (choiceTerm r s t).realize (values d) =
        (s.realize (values d)).union (t.realize (values d)) := by
      rw [realize_choice_winner]
      unfold WinnerSet.choice
      split
      · exact (ha d r (by simp [WinnerSet.choice, *])).elim
      · rfl
    rw [vals] at hp
    rcases hp with h | h
    · exact hs h fun d hd hm => hn d hd ((vals d).symm ▸ Or.inl hm)
    · exact ht h fun d hd hm => hn d hd ((vals d).symm ▸ Or.inr hm)

end KFOL.Core.SquareSourceObstruction
