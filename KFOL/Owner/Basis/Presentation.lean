module

public import KFOL.Owner.Four
public import KFOL.Reset.Basis.Laws
public import KFOL.Equational.Completeness
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Card

/-! The thirty-six explicitly expanded native identities, finite soundness and
arbitrary-model algebraic laws. Completeness is separate. -/

@[expose] public section

namespace KFOL.Owner.FiniteBasis

universe u

/-- The reset projection equation is R5 with renamed variables and
its sides exchanged. -/
theorem Laws.reset_back {M : Type u} {f : M → M → M} {h : M → M → M → M}
    (laws : Laws f h) (r a u : M) : f (f u a) r = f (f (f u r) a) r := (laws.R5 u r a).symm

/-- Projection idempotence is reset law R3, with its variables renamed. -/
theorem Laws.project_idem {M : Type u} {f : M → M → M} {h : M → M → M → M}
    (laws : Laws f h) (r u : M) : f (f u r) r = f u r := laws.R3 u r

/-- The action-at-zero equation is exactly reset law R2. -/
theorem Laws.G_zero {M : Type u} {f : M → M → M} {h : M → M → M → M}
    (laws : Laws f h) (r a : M) : f (f r a) r = f a r := laws.R2 r a

/-- The second action-at-zero equation is symmetry of S8. -/
theorem Laws.F_zero {M : Type u} {f : M → M → M} {h : M → M → M → M}
    (laws : Laws f h) (r a b : M) : h r (f r a) b = h r a b := (laws.h_insert r a b).symm

theorem law_R1 (r : Four) :
    (Four.reset r r) = r := by
  cases r <;> rfl

theorem law_R2 (r a : Four) :
    (Four.reset (Four.reset r a) r) = (Four.reset a r) := by
  cases r <;> cases a <;> rfl

theorem law_R3 (r a : Four) :
    (Four.reset (Four.reset r a) a) = (Four.reset r a) := by
  cases r <;> cases a <;> rfl

theorem law_R4 (r a b : Four) :
    (Four.reset r (Four.reset (Four.reset r a) b)) = (Four.reset r (Four.reset a b)) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_R5 (r a b : Four) :
    (Four.reset (Four.reset (Four.reset r a) b) a) = (Four.reset (Four.reset r b) a) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_R6 (r a b : Four) :
    (Four.reset r (Four.reset a b)) = (Four.reset a (Four.reset r b)) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_h_sym (r a b : Four) :
    (Four.guarded r a b) = (Four.guarded r b a) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_h_minor (r a : Four) :
    (Four.guarded r a a) = (Four.reset a r) := by
  cases r <;> cases a <;> rfl

theorem law_h_root (r a b : Four) :
    (Four.reset (Four.guarded r a b) r) = (Four.guarded r a b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_h_expand (r a b u : Four) :
    (Four.guarded (Four.reset u r) a b) = (Four.reset (Four.reset u r) (Four.guarded r a b)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_h_split (r a b u v : Four) :
    (Four.guarded r (Four.reset u a) (Four.reset v b)) = (Four.reset (Four.reset (Four.guarded r (Four.reset u a) b) r) (Four.reset (Four.guarded r a (Four.reset v b)) r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> cases v <;> rfl

theorem law_h_back (r a b u : Four) :
    (Four.guarded r (Four.reset u a) b) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_h_reroot (r a b u : Four) :
    (Four.reset (Four.guarded a u b) r) = (Four.reset (Four.reset (Four.guarded r u b) a) r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_h_insert (r a b : Four) :
    (Four.guarded r a b) = (Four.guarded r (Four.reset r a) b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_project_join (r a u v : Four) :
    (Four.reset (Four.reset (Four.reset u a) (Four.reset v a)) r) = (Four.reset (Four.reset (Four.reset (Four.reset u a) r) r) (Four.reset (Four.reset (Four.reset v a) r) r)) := by
  cases r <;> cases a <;> cases u <;> cases v <;> rfl

theorem law_reset_split (a u v : Four) :
    (Four.reset u (Four.reset v a)) = (Four.reset (Four.reset u a) (Four.reset v a)) := by
  cases a <;> cases u <;> cases v <;> rfl


theorem law_root_preserve (r u v : Four) :
    (Four.reset (Four.reset u (Four.reset v r)) r) = (Four.reset u (Four.reset v r)) := by
  cases r <;> cases u <;> cases v <;> rfl

theorem law_F_closed (r a b u : Four) :
    (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) r) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_join (r a b u v : Four) :
    (Four.guarded r (Four.reset (Four.reset (Four.reset (Four.reset u r) r) (Four.reset (Four.reset v r) r)) a) b) = (Four.reset (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) r) (Four.reset (Four.guarded r (Four.reset (Four.reset v r) a) b) r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> cases v <;> rfl

theorem law_F_contract (r a b u : Four) :
    (Four.reset (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) r) (Four.reset (Four.reset (Four.reset (Four.guarded r (Four.reset r a) b) r) (Four.reset (Four.reset u r) r)) r)) = (Four.reset (Four.reset (Four.guarded r (Four.reset r a) b) r) (Four.reset (Four.reset u r) r)) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_idem (r a b u : Four) :
    (Four.guarded r (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) a) b) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_band (r a b c d u : Four) :
    (Four.guarded r (Four.reset (Four.guarded r (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) c) d) a) b) = (Four.guarded r (Four.reset (Four.guarded r (Four.reset (Four.reset u r) c) d) a) b) := by
  cases r <;> cases a <;> cases b <;> cases c <;> cases d <;> cases u <;> rfl

theorem law_F_Ga (r a b u : Four) :
    (Four.guarded r (Four.reset (Four.reset (Four.reset (Four.reset u r) a) r) a) b) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_Ka (r a b u : Four) :
    (Four.guarded r (Four.reset (Four.guarded r (Four.reset u r) a) a) b) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_Kb (r a b u : Four) :
    (Four.guarded r (Four.reset (Four.guarded r (Four.reset u r) b) a) b) = (Four.guarded r (Four.reset (Four.reset u r) a) b) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_F_ca (r a b : Four) :
    (Four.guarded r (Four.reset (Four.reset a r) a) b) = (Four.guarded r (Four.reset r a) b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_F_cb (r a b : Four) :
    (Four.guarded r (Four.reset (Four.reset b r) a) b) = (Four.guarded r (Four.reset r a) b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_capture (r a b u : Four) :
    (Four.reset (Four.reset (Four.guarded r (Four.guarded r (Four.reset (Four.reset u r) a) b) b) a) r) = (Four.reset (Four.reset (Four.guarded r (Four.reset u r) b) a) r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_weak_gate (r a b u : Four) :
    (Four.reset (Four.reset (Four.guarded r (Four.reset (Four.reset u r) a) b) a) r) = (Four.reset (Four.reset (Four.guarded r (Four.reset u r) b) a) r) := by
  cases r <;> cases a <;> cases b <;> cases u <;> rfl

theorem law_terminal (r a b : Four) :
    (Four.guarded r (Four.guarded r a b) b) = (Four.guarded r (Four.reset a r) b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_terminal_bound (r a b : Four) :
    (Four.reset (Four.reset (Four.guarded r a b) r) (Four.reset (Four.reset (Four.reset (Four.reset a r) r) (Four.reset (Four.reset b r) r)) r)) = (Four.reset (Four.reset (Four.reset a r) r) (Four.reset (Four.reset b r) r)) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_terminal_weak (r a b : Four) :
    (Four.reset (Four.reset (Four.guarded r a b) r) (Four.reset (Four.guarded r (Four.reset a r) b) r)) = (Four.guarded r (Four.reset a r) b) := by
  cases r <;> cases a <;> cases b <;> rfl

theorem law_G_def (r a u : Four) :
    (Four.reset (Four.reset (Four.reset u r) a) r) = (Four.guarded r (Four.reset (Four.reset u r) a) a) := by
  cases r <;> cases a <;> cases u <;> rfl

theorem law_K_def (r a u : Four) :
    (Four.guarded r (Four.reset u r) a) = (Four.guarded r (Four.reset (Four.reset u r) r) a) := by
  cases r <;> cases a <;> cases u <;> rfl



theorem law_G_root (r u : Four) :
    (Four.reset (Four.reset (Four.reset u r) r) r) = (Four.reset u r) := by
  cases r <;> cases u <;> rfl

theorem law_K_root (r u : Four) :
    (Four.guarded r (Four.reset u r) r) = (Four.reset u r) := by
  cases r <;> cases u <;> rfl

theorem four_laws : Laws Four.reset Four.guarded :=
  ⟨law_R1, law_R2, law_R3, law_R4, law_R5, law_R6, law_h_sym, law_h_minor, law_h_root, law_h_expand, law_h_split, law_h_back, law_h_reroot, law_h_insert, law_project_join, law_reset_split, law_root_preserve, law_F_closed, law_F_join, law_F_contract, law_F_idem, law_F_band, law_F_Ga, law_F_Ka, law_F_Kb, law_F_ca, law_F_cb, law_capture, law_weak_gate, law_terminal, law_terminal_bound, law_terminal_weak, law_G_def, law_K_def, law_G_root, law_K_root⟩

theorem basisAxiom_holds (i : Fin 36) :
    letI := fourStructure (Role := Unit); (basisAxiom i).Holds Four := by
  intro v
  change Fin 6 → Four at v
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (Four.reset (v 0) (v 0)) = (v 0)
    exact law_R1 (v 0)
  · change (Four.reset (Four.reset (v 0) (v 1)) (v 0)) = (Four.reset (v 1) (v 0))
    exact law_R2 (v 0) (v 1)
  · change (Four.reset (Four.reset (v 0) (v 1)) (v 1)) = (Four.reset (v 0) (v 1))
    exact law_R3 (v 0) (v 1)
  · change (Four.reset (v 0) (Four.reset (Four.reset (v 0) (v 1)) (v 2))) = (Four.reset (v 0) (Four.reset (v 1) (v 2)))
    exact law_R4 (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.reset (v 0) (v 1)) (v 2)) (v 1)) = (Four.reset (Four.reset (v 0) (v 2)) (v 1))
    exact law_R5 (v 0) (v 1) (v 2)
  · change (Four.reset (v 0) (Four.reset (v 1) (v 2))) = (Four.reset (v 1) (Four.reset (v 0) (v 2)))
    exact law_R6 (v 0) (v 1) (v 2)
  · change (Four.guarded (v 0) (v 1) (v 2)) = (Four.guarded (v 0) (v 2) (v 1))
    exact law_h_sym (v 0) (v 1) (v 2)
  · change (Four.guarded (v 0) (v 1) (v 1)) = (Four.reset (v 1) (v 0))
    exact law_h_minor (v 0) (v 1)
  · change (Four.reset (Four.guarded (v 0) (v 1) (v 2)) (v 0)) = (Four.guarded (v 0) (v 1) (v 2))
    exact law_h_root (v 0) (v 1) (v 2)
  · change (Four.guarded (Four.reset (v 5) (v 0)) (v 1) (v 2)) = (Four.reset (Four.reset (v 5) (v 0)) (Four.guarded (v 0) (v 1) (v 2)))
    exact law_h_expand (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (v 5) (v 1)) (Four.reset (v 4) (v 2))) = (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (v 5) (v 1)) (v 2)) (v 0)) (Four.reset (Four.guarded (v 0) (v 1) (Four.reset (v 4) (v 2))) (v 0)))
    exact law_h_split (v 0) (v 1) (v 2) (v 5) (v 4)
  · change (Four.guarded (v 0) (Four.reset (v 5) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_h_back (v 0) (v 1) (v 2) (v 5)
  · change (Four.reset (Four.guarded (v 1) (v 5) (v 2)) (v 0)) = (Four.reset (Four.reset (Four.guarded (v 0) (v 5) (v 2)) (v 1)) (v 0))
    exact law_h_reroot (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (v 1) (v 2)) = (Four.guarded (v 0) (Four.reset (v 0) (v 1)) (v 2))
    exact law_h_insert (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.reset (v 5) (v 1)) (Four.reset (v 4) (v 1))) (v 0)) = (Four.reset (Four.reset (Four.reset (Four.reset (v 5) (v 1)) (v 0)) (v 0)) (Four.reset (Four.reset (Four.reset (v 4) (v 1)) (v 0)) (v 0)))
    exact law_project_join (v 0) (v 1) (v 5) (v 4)
  · change (Four.reset (v 5) (Four.reset (v 4) (v 1))) = (Four.reset (Four.reset (v 5) (v 1)) (Four.reset (v 4) (v 1)))
    exact law_reset_split (v 1) (v 5) (v 4)
  · change (Four.reset (Four.reset (v 5) (Four.reset (v 4) (v 0))) (v 0)) = (Four.reset (v 5) (Four.reset (v 4) (v 0)))
    exact law_root_preserve (v 0) (v 5) (v 4)
  · change (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 0)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_F_closed (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.reset (Four.reset (Four.reset (v 5) (v 0)) (v 0)) (Four.reset (Four.reset (v 4) (v 0)) (v 0))) (v 1)) (v 2)) = (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 0)) (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 4) (v 0)) (v 1)) (v 2)) (v 0)))
    exact law_F_join (v 0) (v 1) (v 2) (v 5) (v 4)
  · change (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 0)) (Four.reset (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (v 0) (v 1)) (v 2)) (v 0)) (Four.reset (Four.reset (v 5) (v 0)) (v 0))) (v 0))) = (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (v 0) (v 1)) (v 2)) (v 0)) (Four.reset (Four.reset (v 5) (v 0)) (v 0)))
    exact law_F_contract (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_F_idem (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 3)) (v 4)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 3)) (v 4)) (v 1)) (v 2))
    exact law_F_band (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.reset (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 0)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_F_Ga (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 1)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_F_Ka (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 2)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2))
    exact law_F_Kb (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.reset (Four.reset (v 1) (v 0)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (v 0) (v 1)) (v 2))
    exact law_F_ca (v 0) (v 1) (v 2)
  · change (Four.guarded (v 0) (Four.reset (Four.reset (v 2) (v 0)) (v 1)) (v 2)) = (Four.guarded (v 0) (Four.reset (v 0) (v 1)) (v 2))
    exact law_F_cb (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.guarded (v 0) (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 2)) (v 1)) (v 0)) = (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 2)) (v 1)) (v 0))
    exact law_capture (v 0) (v 1) (v 2) (v 5)
  · change (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 2)) (v 1)) (v 0)) = (Four.reset (Four.reset (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 2)) (v 1)) (v 0))
    exact law_weak_gate (v 0) (v 1) (v 2) (v 5)
  · change (Four.guarded (v 0) (Four.guarded (v 0) (v 1) (v 2)) (v 2)) = (Four.guarded (v 0) (Four.reset (v 1) (v 0)) (v 2))
    exact law_terminal (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.guarded (v 0) (v 1) (v 2)) (v 0)) (Four.reset (Four.reset (Four.reset (Four.reset (v 1) (v 0)) (v 0)) (Four.reset (Four.reset (v 2) (v 0)) (v 0))) (v 0))) = (Four.reset (Four.reset (Four.reset (v 1) (v 0)) (v 0)) (Four.reset (Four.reset (v 2) (v 0)) (v 0)))
    exact law_terminal_bound (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.guarded (v 0) (v 1) (v 2)) (v 0)) (Four.reset (Four.guarded (v 0) (Four.reset (v 1) (v 0)) (v 2)) (v 0))) = (Four.guarded (v 0) (Four.reset (v 1) (v 0)) (v 2))
    exact law_terminal_weak (v 0) (v 1) (v 2)
  · change (Four.reset (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 0)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 1)) (v 1))
    exact law_G_def (v 0) (v 1) (v 5)
  · change (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 1)) = (Four.guarded (v 0) (Four.reset (Four.reset (v 5) (v 0)) (v 0)) (v 1))
    exact law_K_def (v 0) (v 1) (v 5)
  · change (Four.reset (Four.reset (Four.reset (v 5) (v 0)) (v 0)) (v 0)) = (Four.reset (v 5) (v 0))
    exact law_G_root (v 0) (v 5)
  · change (Four.guarded (v 0) (Four.reset (v 5) (v 0)) (v 0)) = (Four.reset (v 5) (v 0))
    exact law_K_root (v 0) (v 5)

theorem models_four : letI := fourStructure (Role := Unit); Equational.Models theory Four := by
  rintro e ⟨i, rfl⟩
  exact basisAxiom_holds i

theorem theory_finite : theory.Finite := Set.finite_range basisAxiom

local instance : (n : ℕ) → DecidableEq (Symbol Unit n)
  | _, .reset, .reset => isTrue rfl
  | _, .guarded (), .guarded () => isTrue rfl

/-- The actual displayed family contains thirty-six distinct identities.
This checks the expanded native syntax, not just the number of index slots. -/
theorem basisAxiom_injective : Function.Injective basisAxiom := by
  have hp : Function.Injective (fun i : Fin 36 =>
      ((basisAxiom i).lhs, (basisAxiom i).rhs) :
        Fin 36 → Term Unit (Fin 6) × Term Unit (Fin 6)) := by decide
  intro i j hij
  apply hp
  have hh := Equational.Identity.mk.inj hij
  exact Prod.ext (eq_of_heq hh.2.1) (eq_of_heq hh.2.2)

theorem theory_ncard : theory.ncard = 36 := by
  rw [theory, Set.ncard_range_of_injective basisAxiom_injective, Nat.card_fin]


theorem variable_bound : Equational.HasVariableBound theory 6 := by
  rintro e ⟨i, rfl⟩
  have h := Finset.card_le_card (Finset.subset_univ (basisAxiom i).support)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

@[simp] theorem realize_step {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    {Var : Type*} (s t : Term Unit Var) (v : Var → M) :
    (Term.step s t).realize v = resetOperation M (s.realize v) (t.realize v) := by
  simp only [Term.step, FirstOrder.Language.Term.realize, resetOperation]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

@[simp] theorem realize_guarded {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    {Var : Type*} (s t q : Term Unit Var) (v : Var → M) :
    (Term.guarded () s t q).realize v = guardedOperation M (s.realize v) (t.realize v) (q.realize v) := by
  simp only [Term.guarded, FirstOrder.Language.Term.realize, guardedOperation]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi]
  · by_cases hj : i = 1 <;> simp [hi, hj]

theorem models_theory_iff {M : Type u} [(Equational.language (Symbol Unit)).Structure M] :
    Equational.Models theory M ↔ Laws (resetOperation M) (guardedOperation M) := by
  constructor
  · intro hm
    constructor
    · intro r
      have hh := hm (basisAxiom 0) ⟨0, rfl⟩ ![r, r, r, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a
      have hh := hm (basisAxiom 1) ⟨1, rfl⟩ ![r, a, r, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a
      have hh := hm (basisAxiom 2) ⟨2, rfl⟩ ![r, a, r, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 3) ⟨3, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 4) ⟨4, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 5) ⟨5, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 6) ⟨6, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a
      have hh := hm (basisAxiom 7) ⟨7, rfl⟩ ![r, a, r, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 8) ⟨8, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 9) ⟨9, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u v
      have hh := hm (basisAxiom 10) ⟨10, rfl⟩ ![r, a, b, r, v, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 11) ⟨11, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 12) ⟨12, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 13) ⟨13, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a u v
      have hh := hm (basisAxiom 14) ⟨14, rfl⟩ ![r, a, r, r, v, u]
      simpa [basisAxiom] using hh
    · intro a u v
      have hh := hm (basisAxiom 15) ⟨15, rfl⟩ ![a, a, a, a, v, u]
      simpa [basisAxiom] using hh
    · intro r u v
      have hh := hm (basisAxiom 16) ⟨16, rfl⟩ ![r, r, r, r, v, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 17) ⟨17, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u v
      have hh := hm (basisAxiom 18) ⟨18, rfl⟩ ![r, a, b, r, v, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 19) ⟨19, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 20) ⟨20, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b c d u
      have hh := hm (basisAxiom 21) ⟨21, rfl⟩ ![r, a, b, c, d, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 22) ⟨22, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 23) ⟨23, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 24) ⟨24, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 25) ⟨25, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 26) ⟨26, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 27) ⟨27, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b u
      have hh := hm (basisAxiom 28) ⟨28, rfl⟩ ![r, a, b, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 29) ⟨29, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 30) ⟨30, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a b
      have hh := hm (basisAxiom 31) ⟨31, rfl⟩ ![r, a, b, r, r, r]
      simpa [basisAxiom] using hh
    · intro r a u
      have hh := hm (basisAxiom 32) ⟨32, rfl⟩ ![r, a, r, r, r, u]
      simpa [basisAxiom] using hh
    · intro r a u
      have hh := hm (basisAxiom 33) ⟨33, rfl⟩ ![r, a, r, r, r, u]
      simpa [basisAxiom] using hh
    · intro r u
      have hh := hm (basisAxiom 34) ⟨34, rfl⟩ ![r, r, r, r, r, u]
      simpa [basisAxiom] using hh
    · intro r u
      have hh := hm (basisAxiom 35) ⟨35, rfl⟩ ![r, r, r, r, r, u]
      simpa [basisAxiom] using hh
  · rintro hl e ⟨i, rfl⟩ v
    change Fin 6 → M at v
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [basisAxiom] using hl.R1 (v 0)
    · simpa [basisAxiom] using hl.R2 (v 0) (v 1)
    · simpa [basisAxiom] using hl.R3 (v 0) (v 1)
    · simpa [basisAxiom] using hl.R4 (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.R5 (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.R6 (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.h_sym (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.h_minor (v 0) (v 1)
    · simpa [basisAxiom] using hl.h_root (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.h_expand (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.h_split (v 0) (v 1) (v 2) (v 5) (v 4)
    · simpa [basisAxiom] using hl.h_back (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.h_reroot (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.h_insert (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.project_join (v 0) (v 1) (v 5) (v 4)
    · simpa [basisAxiom] using hl.reset_split (v 1) (v 5) (v 4)
    · simpa [basisAxiom] using hl.root_preserve (v 0) (v 5) (v 4)
    · simpa [basisAxiom] using hl.F_closed (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_join (v 0) (v 1) (v 2) (v 5) (v 4)
    · simpa [basisAxiom] using hl.F_contract (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_idem (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_band (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    · simpa [basisAxiom] using hl.F_Ga (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_Ka (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_Kb (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.F_ca (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.F_cb (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.capture (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.weak_gate (v 0) (v 1) (v 2) (v 5)
    · simpa [basisAxiom] using hl.terminal (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.terminal_bound (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.terminal_weak (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using hl.G_def (v 0) (v 1) (v 5)
    · simpa [basisAxiom] using hl.K_def (v 0) (v 1) (v 5)
    · simpa [basisAxiom] using hl.G_root (v 0) (v 5)
    · simpa [basisAxiom] using hl.K_root (v 0) (v 5)

end KFOL.Owner.FiniteBasis
