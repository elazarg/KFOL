module

public import KFOL.Complexity.OwnerSynthesisMachine

/-! # Exact correspondence between native and independently defined owner synthesis -/

@[expose] public section

namespace KFOL.Complexity.OwnerRuntime

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

variable {Role : Type}

private theorem relabel_step {Var : Type} (f : Var → ℕ) (s t : Owner.Term Role Var) :
    (Owner.Term.step s t).relabel f = Owner.Term.step (s.relabel f) (t.relabel f) := by
  unfold Owner.Term.step
  simp only [FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  split <;> rfl

private theorem relabel_guarded {Var : Type} (f : Var → ℕ) (owner : Role)
    (x y z : Owner.Term Role Var) :
    (Owner.Term.guarded owner x y z).relabel f =
      Owner.Term.guarded owner (x.relabel f) (y.relabel f) (z.relabel f) := by
  unfold Owner.Term.guarded
  simp only [FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  split
  · rfl
  · split <;> rfl

private theorem relabel_pathBody {n : ℕ} (owner : Role) (root : Fin n)
    (frames : List (Fin n × Fin n)) (fill : Owner.Term Role (Fin n)) :
    (Owner.Term.pathBody owner root frames fill).relabel Fin.val =
      Owner.Term.pathBody owner root.val (frames.map (fun p => (p.1.val, p.2.val)))
        (fill.relabel Fin.val) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    simp only [Owner.Term.pathBody, List.map_cons, relabel_guarded, relabel_step,
      FirstOrder.Language.Term.relabel, ih]

private theorem relabel_pathTerm {n : ℕ} (owner : Role) (root : Fin n)
    (frames : List (Fin n × Fin n)) (fill : Owner.Term Role (Fin n)) :
    (Owner.Term.pathTerm owner root frames fill).relabel Fin.val =
      Owner.Term.pathTerm owner root.val (frames.map (fun p => (p.1.val, p.2.val)))
        (fill.relabel Fin.val) := by
  simp only [Owner.Term.pathTerm, relabel_step, relabel_pathBody, FirstOrder.Language.Term.relabel]

private theorem relabel_joinPaths {n : ℕ} (root : Fin n) (terms : List (Owner.Term Role (Fin n))) :
    (Owner.Term.joinPaths root terms).relabel Fin.val =
      Owner.Term.joinPaths root.val (terms.map (FirstOrder.Language.Term.relabel Fin.val)) := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp only [Owner.Term.joinPaths, List.map_cons, relabel_step, ih]

theorem finishTerm_view {n : ℕ} (owner : Role) (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) :
    finishTerm owner (tableView T, entryView (j, g)) (stateView S) =
      (T.finishTerm owner (List.finRange n) j g S).map
        (FirstOrder.Language.Term.relabel Fin.val) := by
  unfold finishTerm Owner.GuardTable.finishTerm
  rw [show permitted (tableView T, entryView (j, g)).1
      (tableView T, entryView (j, g)).2.1 (stateView S) =
      decide (T.Permitted j S.many S.outside) from permitted_view T j S.many S.outside]
  simp only [decide_eq_true_eq]
  by_cases hp : T.Permitted j S.many S.outside
  · simp only [hp, ite_true, Option.map_some, relabel_step, FirstOrder.Language.Term.relabel]
    rfl
  · simp only [hp, ite_false]
    rw [finishWitness_view]
    simp only [Option.map_map, Function.comp_def, relabel_guarded, FirstOrder.Language.Term.relabel]
    rfl

theorem guardPath_view {n : ℕ} (owner : Role) (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) :
    guardPath owner (tableView T, entryView (j, g)) =
      (T.guardPath owner (List.finRange n) j g).map
        (FirstOrder.Language.Term.relabel Fin.val) := by
  unfold guardPath Owner.GuardTable.guardPath
  change (if j.val = T.root.val then some (.var T.root.val : Owner.Term Role ℕ) else _) = _
  simp only [Fin.val_inj]
  by_cases hp : j = T.root
  · simp only [hp, ite_true, Option.map_some, FirstOrder.Language.Term.relabel]
  · simp only [hp, ite_false]
    rw [run_view]
    change (finishTerm owner (tableView T, entryView (j, g))
      (stateView (T.run (List.finRange n) j g (2 * n)).1)).map _ = _
    rw [finishTerm_view]
    simp only [Option.map_map, Function.comp_def, List.length_finRange, runView]
    congr 1
    funext fill
    exact (relabel_pathTerm owner T.root _ fill).symm

private theorem mapM_map {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx]
    | some y => simp [List.mapM_cons, hx, ih]; cases xs.mapM f <;> rfl

/-- The complete generated term, including every copied frame and join, is the
renaming of the actual independent source synthesis output. -/
theorem synthesize_view {n : ℕ} (owner : Role) (T : Owner.GuardTable (Fin n)) :
    synthesize owner (n, tableView T) =
      (T.synthesize owner (List.finRange n)).map
        (FirstOrder.Language.Term.relabel Fin.val) := by
  unfold synthesize Owner.GuardTable.synthesize
  rw [check_view]
  cases hc : T.check (List.finRange n) with
  | false => rfl
  | true =>
    simp only [ite_true, tableView, List.mapM_map]
    have hpath : (fun p : Fin n × Owner.GuardPair (Fin n) =>
        guardPath owner (tableView T, entryView p)) =
        (fun p => (T.guardPath owner (List.finRange n) p.1 p.2).map
          (FirstOrder.Language.Term.relabel Fin.val)) := by
      funext p
      exact guardPath_view owner T p.1 p.2
    change (T.entries.mapM (fun p => guardPath owner (tableView T, entryView p))).map
      (Owner.Term.joinPaths T.root.val) = _
    rw [hpath, mapM_map]
    simp only [Option.map_map, Function.comp_def]
    congr 1
    funext terms
    exact (relabel_joinPaths T.root terms).symm

abbrev Output (Role : Type) := (n : ℕ) × Owner.Term Role (Fin n)

private theorem relabel_fin_injective (n : ℕ) : Function.Injective
    (FirstOrder.Language.Term.relabel (L := Equational.language (Owner.Symbol Role))
      (Fin.val : Fin n → ℕ)) := by
  cases n with
  | zero =>
    intro term
    exact Fin.elim0 (Owner.Term.root term)
  | succ n =>
    let back : ℕ → Fin (n + 1) := fun j => ⟨j % (n + 1), Nat.mod_lt _ (by omega)⟩
    have hb : back ∘ Fin.val = id := by
      funext i
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    intro t u h
    have he := congrArg (FirstOrder.Language.Term.relabel back) h
    simpa only [FirstOrder.Language.Term.relabel_relabel, hb,
      FirstOrder.Language.Term.relabel_id] using he

variable [Fintype Role]

/-- Expanded syntax output carries its unary position dimension. Renaming the
finite positions to natural binary labels is injective on every dimension. -/
noncomputable def outputEncoding : Output Role ↪ List Bool :=
  ⟨fun output => encPair encUnary termEncoding
      (output.1, output.2.relabel Fin.val), by
    rintro ⟨n, t⟩ ⟨m, u⟩ h
    have hp := (encPair encUnary (termEncoding (Role := Role))).injective h
    have hn : n = m := congrArg Prod.fst hp
    cases hn
    have ht := relabel_fin_injective n (congrArg Prod.snd hp)
    cases ht
    rfl⟩

/-- The exact independent synthesis program, including failed checks, complete
finite saturation, both finishing branches, all paths and the expanded final
join, has a native polynomial-time certificate. -/
theorem source_synthesize_polyTime (owner : Role) : ComputableInPolyTime
    (fun input : Input => (input.2.synthesize owner (List.finRange input.1)).map
      (fun term => (⟨input.1, term⟩ : Output Role)))
    inputEncoding (encOption outputEncoding) := by
  have hraw := (synthesize_polyTime owner).comp view_polyTime
  have hwidth := (fst encUnary tableEncoding).comp view_polyTime
  have hn := hwidth.comp (fst inputEncoding (termEncoding (Role := Role)))
  have ht := snd inputEncoding (termEncoding (Role := Role))
  have htagged := hraw.optionMapWithInput
    (f := fun (input : Input) (term : Owner.Term Role ℕ) => (input.1, term)) (hn.prod ht)
  apply htagged.of_enc_eq
  intro input
  rcases input with ⟨n, T⟩
  change (encOption outputEncoding)
    ((T.synthesize owner (List.finRange n)).map (fun term => (⟨n, term⟩ : Output Role))) =
    (encOption (encPair encUnary termEncoding))
      ((synthesize owner (n, tableView T)).map (fun term => (n, term)))
  rw [synthesize_view]
  cases T.synthesize owner (List.finRange n) <;> rfl

end KFOL.Complexity.OwnerRuntime
