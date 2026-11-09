module

public import KFOL.Strategic.Adequacy

/-! # Forcing and singleton possible-equilibrium winners -/

@[expose] public section

namespace KFOL.Strategic

universe u

private theorem opponentDeviation_refl {Role : Type u} (i : Role) {g : Tree Role}
    (p : Profile g) : OpponentDeviation i p p := by
  induction p with
  | leaf w => exact .leaf w
  | node _ _ _ _ hl hr => exact .node (fun _ => rfl) hl hr

@[simp] theorem canForce_leaf {Role : Type u} (w i : Role) :
    CanForce (.leaf w) i ↔ w = i := by
  constructor
  · rintro ⟨p, hp⟩
    cases p
    exact hp _ (.leaf w)
  · intro h
    refine ⟨.leaf w, ?_⟩
    intro q _
    cases q
    exact h

/-- The forcing recursion is proved from whole opponent deviations. -/
theorem canForce_node {Role : Type u} [DecidableEq Role] (r i : Role) (g h : Tree Role) :
    CanForce (.node r g h) i ↔
      if r = i then CanForce g i ∨ CanForce h i else CanForce g i ∧ CanForce h i := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | node _ a p q =>
      by_cases hr : r = i
      · rw [ite_eq_left hr]
        cases a with
        | false =>
          refine Or.inl ⟨p, fun s hs => ?_⟩
          exact hp (.node r false s q) (.node (fun _ => rfl) hs (opponentDeviation_refl i q))
        | true =>
          refine Or.inr ⟨q, fun s hs => ?_⟩
          exact hp (.node r true p s) (.node (fun _ => rfl) (opponentDeviation_refl i p) hs)
      · rw [ite_eq_right hr]
        constructor
        · refine ⟨p, fun s hs => ?_⟩
          exact hp (.node r false s q) (.node (fun he => (hr he).elim) hs (opponentDeviation_refl i q))
        · refine ⟨q, fun s hs => ?_⟩
          exact hp (.node r true p s) (.node (fun he => (hr he).elim) (opponentDeviation_refl i p) hs)
  · intro hf
    by_cases hr : r = i
    · rw [ite_eq_left hr] at hf
      rcases hf with ⟨p, hp⟩ | ⟨q, hq⟩
      · obtain ⟨q, _⟩ := exists_spe h
        refine ⟨.node r false p q, ?_⟩
        intro deviation hd
        cases deviation with
        | node _ b p' q' =>
          cases hd with
          | node he hl _ =>
            have hb : false = b := he hr
            subst b
            exact hp p' hl
      · obtain ⟨p, _⟩ := exists_spe g
        refine ⟨.node r true p q, ?_⟩
        intro deviation hd
        cases deviation with
        | node _ b p' q' =>
          cases hd with
          | node he _ hl =>
            have hb : true = b := he hr
            subst b
            exact hq q' hl
    · rw [ite_eq_right hr] at hf
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hf
      refine ⟨.node r false p q, ?_⟩
      intro deviation hd
      cases deviation with
      | node _ b p' q' =>
        cases hd with
        | node _ hl hh =>
          cases b with
          | false => exact hp p' hl
          | true => exact hq q' hh

theorem canForce_iff_value_singleton {Role : Type u} (g : Tree Role) (i : Role) :
    CanForce g i ↔ value g = WinnerSet.singleton i := by
  classical
  induction g with
  | leaf w => simp
  | node r g h hg hh =>
    rw [canForce_node, value_node]
    by_cases hr : r = i
    · subst r
      simp only [hg, hh]
      exact (WinnerSet.choice_eq_owner_iff (value g) (value h) i).symm
    · simp only [ite_eq_right hr, hg, hh]
      exact (WinnerSet.choice_eq_other_iff (value g) (value h) r hr).symm

end KFOL.Strategic
