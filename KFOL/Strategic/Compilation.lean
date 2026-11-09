module

public import KFOL.Strategic.Adequacy

/-! # Strategic interpretation of the full public term syntax -/

@[expose] public section

namespace KFOL.Strategic

universe u v

@[simp] theorem winner_rename {Role : Type u} (p : Equiv.Perm Role)
    {g : Tree Role} (q : Profile g) : winner (q.rename p) = p (winner q) := by
  induction q with
  | leaf i => rfl
  | node r a l h hl hh => cases a <;> simp [Profile.rename, winner, hl, hh]

@[simp] theorem spe_rename_iff {Role : Type u} (p : Equiv.Perm Role)
    {g : Tree Role} (q : Profile g) : IsSubgamePerfect (q.rename p) ↔ IsSubgamePerfect q := by
  induction q with
  | leaf i => exact ⟨fun _ => spe_leaf _, fun _ => spe_leaf _⟩
  | node r a l h hl hh =>
    change IsSubgamePerfect (.node (p r) a (l.rename p) (h.rename p)) ↔
      IsSubgamePerfect (.node r a l h)
    rw [spe_node_iff, spe_node_iff, hl, hh]
    have he (x : Role) : p x = p r ↔ x = r := p.injective.eq_iff
    have hw : winner (Profile.node (p r) a (l.rename p) (h.rename p)) =
        p (winner (Profile.node r a l h)) := by
      exact winner_rename p (.node r a l h)
    simp only [LocallyOptimal, winner_rename, he, hw]

/-- Every strategy in a renamed tree comes from an original full strategy,
including actions at branches the profile never enters. -/
theorem profile_rename_surjective {Role : Type u} (p : Equiv.Perm Role) (g : Tree Role) :
    Function.Surjective (Profile.rename p (g := g)) := by
  induction g with
  | leaf i =>
    intro q
    cases q
    exact ⟨.leaf i, rfl⟩
  | node r l h hl hh =>
    intro q
    cases q with
    | node _ a ql qh =>
      obtain ⟨l', rfl⟩ := hl ql
      obtain ⟨h', rfl⟩ := hh qh
      exact ⟨.node r a l' h', rfl⟩

@[simp] theorem value_rename {Role : Type u} (p : Equiv.Perm Role) (g : Tree Role) :
    value (g.rename p) = WinnerSet.rename p (value g) := by
  apply Subtype.ext
  ext i
  change (∃ q : Profile (g.rename p), IsSubgamePerfect q ∧ winner q = i) ↔
    ∃ j, (∃ q : Profile g, IsSubgamePerfect q ∧ winner q = j) ∧ p j = i
  constructor
  · rintro ⟨q, hq, hw⟩
    obtain ⟨q', rfl⟩ := profile_rename_surjective p g q
    exact ⟨winner q', ⟨q', (spe_rename_iff p q').mp hq, rfl⟩, (winner_rename p q').symm.trans hw⟩
  · rintro ⟨j, ⟨q, hq, hw⟩, hi⟩
    refine ⟨q.rename p, (spe_rename_iff p q).mpr hq, ?_⟩
    rw [winner_rename, hw, hi]

/-- Actual full-profile equilibria interpret every public constructor,
including internal switches and independently solved repeated copies. -/
theorem value_compile {Role : Type u} {Var : Type v} (components : Var → Tree Role)
    (t : Term Role Var) :
    value (compile components t) = t.eval (fun x => value (components x)) := by
  induction t with
  | winner r => exact value_leaf r
  | var x => rfl
  | choice r s t hs ht => simp only [compile, value_node, hs, ht, Term.eval]
  | rename p t ht => simp only [compile, value_rename, ht, Term.eval]

end KFOL.Strategic
