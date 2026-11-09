module

public import KFOL.Owner.Basis.WinnerSet
public import KFOL.Owner.GuardEncoding

/-! Literal two-new-source guard coverage implies equational absorption. -/

@[expose] public section

namespace KFOL.Owner

universe u v

private theorem eval_atomGuard {Var : Type v} (j : Var) (M N V : Var → Prop) :
    Eval [⟨j, [], []⟩] M N V ↔ V j := by simp [Eval, Guard.Holds]

private theorem twoSourceGuards_cons {Var : Type v} (r a b w z : Var) (P : List (Var × Var)) :
    Term.twoSourceGuards r a b ((w, z) :: P) =
      (((Term.twoSourceGuards r a b P).map (Guard.addMany w)).map (Guard.addOutside w)).map
        (fun g => (g.addOutside z).addMany r) := by
  simp only [Term.twoSourceGuards, Guard.pathLift, List.map_map, Function.comp_def]

private theorem eval_twoSourceGuards_cons {Var : Type v} (r a b w z : Var) (P : List (Var × Var))
    (M N V : Var → Prop) :
    Eval (Term.twoSourceGuards r a b ((w, z) :: P)) M N V ↔
      M r ∧ N z ∧ N w ∧ M w ∧ Eval (Term.twoSourceGuards r a b P) M N V := by
  rw [twoSourceGuards_cons]
  have he : (((Term.twoSourceGuards r a b P).map (Guard.addMany w)).map
      (Guard.addOutside w)).map (fun g => (g.addOutside z).addMany r) =
      ((((Term.twoSourceGuards r a b P).map (Guard.addMany w)).map
        (Guard.addOutside w)).map (Guard.addOutside z)).map (Guard.addMany r) := by
    simp only [List.map_map, Function.comp_def]
  rw [he, eval_many, eval_outside, eval_outside, eval_many]

/-- Independent Boolean guard decomposition of the actual original path
term. No winner-set semantic or completeness hypothesis enters this lemma. -/
theorem Term.eval_guards_two_sources {Var : Type v} (r a b : Var) (P : List (Var × Var))
    (M N V : Var → Prop) :
    Eval ((pathBody false r P (guarded false (.var r) (.var a) (.var b))).guards true) M N V ↔
      Eval ((pathBody false r P (.var r)).guards true) M N V ∨
        Eval (twoSourceGuards r a b P) M N V := by
  induction P with
  | nil =>
    simp only [pathBody, guards_guarded, guards_var, Bool.false_eq_true, ite_false,
      root_var, twoSourceGuards, Guard.pathLift]
    simp [Guard.addMany, Guard.addOutside, Eval, Guard.Holds]
  | cons p P ih =>
    obtain ⟨w, z⟩ := p
    rw [eval_twoSourceGuards_cons]
    simp only [pathBody, guards_guarded, guards_step, guards_var, Bool.false_eq_true, ite_false,
      root_var, root_step, eval_append, eval_many, eval_outside, eval_atomGuard]
    rw [ih]
    tauto

@[simp] theorem Term.withOwner_pathBody {Role : Type u} {Var : Type v} (owner : Role)
    (r : Var) (P : List (Var × Var)) (fill : Term Unit Var) :
    (pathBody () r P fill).withOwner owner = pathBody owner r P (fill.withOwner owner) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨w, z⟩ := p
    simp only [pathBody, withOwner_guarded, withOwner_step, withOwner_var, ih]

end KFOL.Owner

namespace KFOL.Owner.FiniteBasis

universe v

/-- Literal two-source absorption: an already derived prefix constant and
coverage of precisely the two added source guards suffice. The upper term
may be any native term; in particular it may be the report's word-value join. -/
theorem two_source_guard_absorption {Var : Type v} (r a b : Var) (P : List (Var × Var))
    (W : Term Unit Var)
    (hzero : Equational.Derives theory
      (Term.step (Term.pathBody () r P (.var r)) W) W)
    (hcover : Covers (Term.twoSourceGuards r a b P) ((W.withOwner false).guards true)) :
    Equational.Derives theory
      (Term.step (Term.pathBody () r P (Term.guarded () (.var r) (.var a) (.var b))) W) W := by
  classical
  let zero := Term.pathBody () r P (.var r)
  let added := Term.pathBody () r P (Term.guarded () (.var r) (.var a) (.var b))
  let left := Term.step added W
  let _ := oneOwnerStructure (2 : Fin 3)
  have hmodels := (isBasis_winnerSet (Function.Embedding.refl (Fin 3)) (2 : Fin 3) 0 (by decide)).models
  have hguard (t : Term Unit Var) (v : Var → WinnerSet (Fin 3)) :
      0 ∈ ((t.withOwner (2 : Fin 3)).eval v).val ↔
        Eval ((t.withOwner false).guards true)
          (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton 2)
          (fun j => 0 ∈ (v j).val) := by
    rw [(t.withOwner (2 : Fin 3)).guard_semantics 0 2
      ((t.withOwner (2 : Fin 3)).owners_mono _ _ (Term.ownersIn_withOwner 2 t)
        (fun _ h => Or.inr h)), Term.guards_withOwner_outsider t 2 0 (by decide)]
  have hobs (v : Var → WinnerSet (Fin 3)) :
      (0 ∈ ((left.withOwner (2 : Fin 3)).eval v).val ↔
        0 ∈ ((W.withOwner (2 : Fin 3)).eval v).val) := by
    have hshape := Term.eval_guards_two_sources r a b P
      (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton 2) (fun j => 0 ∈ (v j).val)
    have hshape' : Eval ((added.withOwner false).guards true)
        (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton 2) (fun j => 0 ∈ (v j).val) ↔
      Eval ((zero.withOwner false).guards true)
        (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton 2) (fun j => 0 ∈ (v j).val) ∨
      Eval (Term.twoSourceGuards r a b P)
        (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton 2) (fun j => 0 ∈ (v j).val) := by
      simpa only [added, zero, Term.withOwner_pathBody, Term.withOwner_guarded, Term.withOwner_var] using hshape
    have hzeroEval : ((Term.step zero W).withOwner (2 : Fin 3)).eval v =
        (W.withOwner (2 : Fin 3)).eval v := by
      rw [Term.eval_withOwner, Term.eval_withOwner]
      exact hzero.sound (WinnerSet (Fin 3)) hmodels v
    change 0 ∈ ((Term.step added W).withOwner (2 : Fin 3) |>.eval v).val ↔ _
    rw [Term.withOwner_step, Term.eval_step, WinnerSet.mem_reset]
    constructor
    · rintro (hW | ⟨hAmb, hAdd⟩)
      · exact hW
      · rcases hshape'.mp ((hguard added v).mp hAdd) with hOld | hNew
        · have hz := (hguard zero v).mpr hOld
          have hmem : 0 ∈ (((Term.step zero W).withOwner (2 : Fin 3)).eval v).val := by
            rw [Term.withOwner_step, Term.eval_step, WinnerSet.mem_reset]
            exact Or.inr ⟨hAmb, hz⟩
          exact hzeroEval ▸ hmem
        · apply (hguard W v).mpr
          exact (covers_iff (0 : Fin 3) 2 1 (by decide) (by decide) (by decide)
            _ _).mp hcover v hNew
    · exact Or.inl
  have hl := Term.ownersIn_withOwner (2 : Fin 3) left
  have hr := Term.ownersIn_withOwner (2 : Fin 3) W
  have hc := ((left.withOwner (2 : Fin 3)).observation_equation_iff (W.withOwner 2) 0 2 1
    (by decide) (by decide) (by decide)
    ((left.withOwner (2 : Fin 3)).owners_mono _ _ hl (fun _ h => Or.inr h))
    ((W.withOwner (2 : Fin 3)).owners_mono _ _ hr (fun _ h => Or.inr h))).mpr hobs
  have hvalid := ((left.withOwner (2 : Fin 3)).single_table_equation_iff
    (Function.Embedding.refl _) (W.withOwner 2) 2 0 (by decide) hl hr).mpr hc
  have hfour := ((left.withOwner (2 : Fin 3)).four_element_complete
    (Function.Embedding.refl _) (W.withOwner 2) 2 0 (by decide) hl hr).mp hvalid
  have hfour' : ∀ w : Var → Four, left.evalFour w = W.evalFour w := by
    intro w
    simpa only [Term.evalFour_withOwner] using hfour w
  apply Equational.derives_of_valid_in_models theory left W
  intro M str _ hm v
  exact (models_theory_iff.mp hm).equal_of_four left W hfour' v

end KFOL.Owner.FiniteBasis
