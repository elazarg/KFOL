/- Lattice operations on blocking policies and the least-point principle
used by the mixed-policy guard algorithms. Classification and complexity
arguments are written in the selective-reset appendix. -/
import ChainGuards
set_option autoImplicit false
namespace MinimalChoice.ChainGuards
open ResetCalculus OwnerFragments SmallFragments
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem clearPolicy_union {α : Type} (D E : α → Prop) (k : α) (Y : S α) :
    ClearPolicy (fun r => D r ∨ E r) k Y ↔ ClearPolicy D k Y ∧ ClearPolicy E k Y := by
  simp only [ClearPolicy]
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨hd, he⟩ r (hr | hr)
    · exact hd r hr
    · exact he r hr

theorem clearPolicy_inter {α : Type} (D E : α → Prop) (k : α) (Y : S α) (hy : NE Y) :
    ClearPolicy (fun r => D r ∧ E r) k Y ↔ ClearPolicy D k Y ∨ ClearPolicy E k Y := by
  rcases atom_or_multiple Y hy with ⟨r, hr⟩ | hm
  · subst Y
    rw [clearPolicy_atom, clearPolicy_atom, clearPolicy_atom]
    grind
  · have hd := clearPolicy_many D k Y hm
    have he := clearPolicy_many E k Y hm
    have hi := clearPolicy_many (fun r => D r ∧ E r) k Y hm
    simp [hd, he, hi]

theorem policy_union {α : Type} (D E : α → Prop) (X Y Z : S α) :
    policy (fun r => D r ∨ E r) X Y Z = policy D X Y (policy E X Y Z) := by
  funext k
  apply propext
  simp only [policy_membership, clearPolicy_union]
  grind

theorem policy_inter {α : Type} (D E : α → Prop) (X Y Z : S α) (hy : NE Y) :
    policy (fun r => D r ∧ E r) X Y Z = reset (policy D X Y Z) (policy E X Y Z) := by
  funext k
  apply propext
  simp only [policy_membership, clearPolicy_inter D E k Y hy, reset_membership, policy_many]
  grind

theorem clearPolicy_cover {α : Type} (D E : α → Prop) (k : α) (Y : S α)
    (hne : NE Y) (h : ∀ r, D r → E r → k = r) :
    ClearPolicy D k Y ∨ ClearPolicy E k Y := by
  apply (clearPolicy_inter D E k Y hne).mp
  exact fun r hr => Or.inl (h r hr.1 hr.2)

theorem clearPolicy_joint {α : Type} (D E : α → Prop) (k : α) (Y : S α)
    (hne : NE Y) (hall : ∀ r, D r ∨ E r) :
    (ClearPolicy D k Y ∧ ClearPolicy E k Y) ↔ Multiple Y ∨ Y k := by
  constructor
  · rintro ⟨hd, he⟩
    rcases atom_or_multiple Y hne with ⟨r, hr⟩ | hm
    · have hkr : k = r := by
        rcases hall r with hD | hE
        · exact (clearPolicy_atom D k r).mp (hr ▸ hd) hD
        · exact (clearPolicy_atom E k r).mp (hr ▸ he) hE
      exact Or.inr (by rw [hr, hkr]; rfl)
    · exact Or.inl hm
  · rintro (hm | hk)
    · exact ⟨clearPolicy_many D k Y hm, clearPolicy_many E k Y hm⟩
    · exact ⟨clearPolicy_mem D k Y hk, clearPolicy_mem E k Y hk⟩

/-- When the root contribution is present, a collision of the two
covering-policy tests can be replaced by ambiguity. -/
theorem joint_test_absorption {α : Type} (D E : α → Prop) (k : α) (Y : S α)
    (hne : NE Y) (hall : ∀ r, D r ∨ E r) (Q : Prop) :
    (Y k ∨ (Q ∧ ClearPolicy D k Y ∧ ClearPolicy E k Y)) ↔
      (Y k ∨ (Q ∧ Multiple Y)) := by
  have h := clearPolicy_joint D E k Y hne hall
  grind

/-- Outside a baseline, a nonambiguous calibration input realizes exactly
the atomic passing pattern of a role other than the marker. -/
theorem calibration_atom {α : Type} (k : α) (Y : S α) (hne : NE Y)
    (hm : ¬ Multiple Y) (hk : ¬ Y k) :
    ∃ r, Y = atom r ∧ r ≠ k ∧
      ∀ D : α → Prop, (ClearPolicy D k Y ↔ ¬ D r) := by
  rcases atom_or_multiple Y hne with ⟨r, hr⟩ | hmany
  · have hkr : k ≠ r := by intro he; apply hk; rw [hr, he]; rfl
    refine ⟨r, hr, Ne.symm hkr, ?_⟩
    intro D
    rw [hr, clearPolicy_atom]
    simp [hkr]
  · exact False.elim (hm hmany)

theorem policy_marker {α : Type} (D : α → Prop) (X Y Z W : S α) (k : α)
    (hx : Multiple X) (hX : Sub X W) (hY : Sub Y W) (hw : ¬ W k) :
    policy D X Y Z k ↔ ClearPolicy D k Y ∧ Z k := by
  have hxk : ¬ X k := fun h => hw (hX k h)
  have hyk : ¬ Y k := fun h => hw (hY k h)
  simp [policy_membership, hxk, hyk, hx]

noncomputable def policyClause {α β : Type} (D E : α → Prop) (Z : S α)
    (Y : β → S α) (clause : List (Lit β)) (C : S α) : S α :=
  match clause with
  | [] => C
  | l :: rest => policy (if l.2 then D else E) Z (Y l.1)
      (policyClause D E Z Y rest C)

theorem policyClause_marker {α β : Type} (D E : α → Prop) (Z W C : S α)
    (Y : β → S α) (clause : List (Lit β)) (k : α) (hz : Multiple Z)
    (hZW : Sub Z W) (hY : ∀ i, Sub (Y i) W) (hw : ¬ W k) :
    policyClause D E Z Y clause C k ↔ C k ∧
      ∀ l ∈ clause, ClearPolicy (if l.2 then D else E) k (Y l.1) := by
  induction clause with
  | nil => simp [policyClause]
  | cons l rest ih =>
    rw [policyClause, policy_marker _ Z _ _ W k hz hZW (hY l.1) hw, ih]
    simp only [List.mem_cons]
    grind

theorem unsat_policy_clause {α β : Type} (D E : α → Prop) (k : α)
    (F : List (List (Lit β))) (Y : β → S α)
    (hc : ∀ i, ClearPolicy D k (Y i) ∨ ClearPolicy E k (Y i))
    (hu : ∀ v, ¬ Sat F v) :
    ∃ clause ∈ F, ∀ l ∈ clause, ClearPolicy (if l.2 then D else E) k (Y l.1) := by
  have hf : ∃ clause ∈ F, ∀ l ∈ clause,
      ¬ Holds (fun i => ¬ ClearPolicy D k (Y i)) l := by
    simpa [Sat] using hu (fun i => ¬ ClearPolicy D k (Y i))
  rcases hf with ⟨clause, hcf, hf⟩
  refine ⟨clause, hcf, ?_⟩
  intro l hl
  have h := hf l hl
  cases hb : l.2
  · have hn : ¬ ClearPolicy D k (Y l.1) := by simpa [Holds, hb] using h
    simpa [hb] using (hc l.1).resolve_left hn
  · simpa [Holds, hb] using h

/-- The UNSAT direction at a fixed observer. Shared blockers may consist
of that observer; disjointness is stronger than needed here. -/
theorem policy_unsat_observation {α β : Type} (D E : α → Prop) (k : α)
    (F : List (List (Lit β))) (Y : β → S α) (Z W C : S α)
    (hz : Multiple Z) (hZW : Sub Z W) (hY : ∀ i, Sub (Y i) W)
    (hne : ∀ i, NE (Y i)) (hi : ∀ r, D r → E r → k = r)
    (hu : ∀ v, ¬ Sat F v) :
    let R := rightResets (F.map (fun clause => policyClause D E Z Y clause C)) W
    reset C R k ↔ R k := by
  let R := rightResets (F.map (fun clause => policyClause D E Z Y clause C)) W
  have hmW := multiple_mono hZW hz
  have hmR : Multiple R := (rightResets_multiple _ W).mpr hmW
  have hCR : C k → R k := by
    intro hc
    apply (rightResets_mem _ W hmW k).mpr
    by_cases hw : W k
    · exact Or.inl hw
    · rcases unsat_policy_clause D E k F Y
        (fun i => clearPolicy_cover D E k (Y i) (hne i) hi) hu with ⟨clause, hcf, hf⟩
      refine Or.inr ⟨policyClause D E Z Y clause C,
        List.mem_map.mpr ⟨clause, hcf, rfl⟩, ?_⟩
      exact (policyClause_marker D E Z W C Y clause k hz hZW hY hw).mpr ⟨hc, hf⟩
  change reset C R k ↔ R k
  simp only [reset_membership, hmR, true_and]
  exact ⟨fun h => h.elim id hCR, Or.inl⟩

theorem policy_sat_separation {α β : Type} (D E : α → Prop) (k : α)
    (F : List (List (Lit β))) (Y : β → S α) (Z W C : S α)
    (hz : Multiple Z) (hZW : Sub Z W) (hY : ∀ i, Sub (Y i) W)
    (hw : ¬ W k) (hc : C k)
    (hs : ∀ clause ∈ F, ∃ l ∈ clause,
      ¬ ClearPolicy (if l.2 then D else E) k (Y l.1)) :
    let R := rightResets (F.map (fun clause => policyClause D E Z Y clause C)) W
    reset C R k ∧ ¬ R k := by
  let R := rightResets (F.map (fun clause => policyClause D E Z Y clause C)) W
  have hmW := multiple_mono hZW hz
  have hn : ¬ R k := by
    dsimp only [R]
    rw [rightResets_mem _ W hmW]
    rintro (h | ⟨branch, hb, hbk⟩)
    · exact hw h
    · rcases List.mem_map.mp hb with ⟨clause, hcf, he⟩
      subst branch
      have hall := ((policyClause_marker D E Z W C Y clause k hz hZW hY hw).mp hbk).2
      rcases hs clause hcf with ⟨l, hl, hn⟩
      exact hn (hall l hl)
  change reset C R k ∧ ¬ R k
  exact ⟨(reset_membership C R k).mpr
    (Or.inr ⟨(rightResets_multiple _ W).mpr hmW, hc⟩), hn⟩

/-- A monotone disjunction holds above a least satisfying point exactly
when one of its disjuncts holds at that point. No finiteness is needed. -/
theorem least_point_coverage {σ γ : Type} (rel : σ → σ → Prop)
    (holds : γ → σ → Prop) (point : γ → σ)
    (realizes : ∀ g, holds g (point g))
    (least : ∀ g v, holds g v → rel (point g) v)
    (monotone : ∀ h u v, rel u v → holds h u → holds h v)
    (left right : List γ) :
    (∀ v, (∃ g ∈ left, holds g v) → ∃ h ∈ right, holds h v) ↔
      ∀ g ∈ left, ∃ h ∈ right, holds h (point g) := by
  constructor
  · intro h g hg
    exact h (point g) ⟨g, hg, realizes g⟩
  · intro h v ⟨g, hg, hv⟩
    obtain ⟨q, hq, hp⟩ := h g hg
    exact ⟨q, hq, monotone q (point g) v (least g v hv) hp⟩

end MinimalChoice.ChainGuards
#print axioms MinimalChoice.ChainGuards.policy_inter
#print axioms MinimalChoice.ChainGuards.policy_union
#print axioms MinimalChoice.ChainGuards.policy_unsat_observation
#print axioms MinimalChoice.ChainGuards.policy_sat_separation
#print axioms MinimalChoice.ChainGuards.joint_test_absorption
