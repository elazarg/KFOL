module

public import KFOL.Owner.Saturation
public import KFOL.Owner.Completeness

/-! Constructing permitted native paths from recorded saturation updates. -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

@[simp] theorem size_var (i : Var) : size (.var i : Term Role Var) = 1 := rfl
@[simp] theorem size_step (s t : Term Role Var) : (step s t).size = 1 + s.size + t.size := rfl
@[simp] theorem size_guarded (a : Role) (x y z : Term Role Var) :
    (guarded a x y z).size = 1 + x.size + y.size + z.size := rfl

theorem size_pathBody (a : Role) (r : Var) (frames : List (Var × Var)) (fill : Term Role Var) :
    (pathBody a r frames fill).size = fill.size + 5 * frames.length := by
  induction frames with
  | nil => simp [pathBody]
  | cons p frames ih =>
    simp only [pathBody, size_guarded, size_step, size_var, ih, List.length_cons]
    omega

theorem size_pathTerm (a : Role) (r : Var) (frames : List (Var × Var)) (fill : Term Role Var) :
    (pathTerm a r frames fill).size = fill.size + 5 * frames.length + 2 := by
  simp only [pathTerm, size_step, size_var, size_pathBody]
  omega

@[simp] theorem root_pathTerm (a : Role) (r : Var) (frames : List (Var × Var)) (fill : Term Role Var) :
    (pathTerm a r frames fill).root = r := rfl

theorem owners_pathBody (a : Role) (r : Var) (frames : List (Var × Var)) (fill : Term Role Var)
    (hfill : fill.OwnersIn (fun x => x = a)) :
    (pathBody a r frames fill).OwnersIn (fun x => x = a) := by
  induction frames with
  | nil => exact hfill
  | cons p frames ih => exact ⟨rfl, trivial, ⟨ih, trivial⟩, trivial⟩

theorem owners_pathTerm (a : Role) (r : Var) (frames : List (Var × Var)) (fill : Term Role Var)
    (hfill : fill.OwnersIn (fun x => x = a)) :
    (pathTerm a r frames fill).OwnersIn (fun x => x = a) :=
  ⟨owners_pathBody a r frames fill hfill, trivial⟩

end Term

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

private def Safe {Role : Type u} (T : GuardTable Var) (a k : Role)
    (S : SaturationState Var) (t : Term Role Var) : Prop :=
  ∀ v : Var → WinnerSet Role,
    (∀ i ∈ S.many, (v i).Ambiguous) →
    (∀ i ∈ S.outside, v i ≠ WinnerSet.singleton a) →
    k ∈ (t.eval v).val →
    T.Enabled {i | (v i).Ambiguous} {i | v i ≠ WinnerSet.singleton a} {i | k ∈ (v i).val}

private theorem permitted_sound {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (j : Var) (C D : Finset Var) (hp : T.Permitted j C D) (v : Var → WinnerSet Role)
    (hm : ∀ i ∈ C, (v i).Ambiguous) (hn : ∀ i ∈ D, v i ≠ WinnerSet.singleton a)
    (hj : k ∈ (v j).val) :
    T.Enabled {i | (v i).Ambiguous} {i | v i ≠ WinnerSet.singleton a} {i | k ∈ (v i).val} := by
  obtain ⟨g, hg, hC, hD⟩ := hp
  refine ⟨j, g, hg, ?_, ?_, hj⟩
  · exact fun i hi => hm i (hC hi)
  · intro i hi
    rcases Finset.mem_union.mp (hD hi) with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact hm i hi a
      · exact hn i hi
    · have he : i = j := Finset.mem_singleton.mp hi
      subst i
      intro hv
      rw [hv] at hj
      exact hka hj

private theorem root_sound {Role : Type u} (T : GuardTable Var) (a k : Role)
    (hr : T.guards T.root = {⟨∅, ∅⟩}) (v : Var → WinnerSet Role) (hk : k ∈ (v T.root).val) :
    T.Enabled {i | (v i).Ambiguous} {i | v i ≠ WinnerSet.singleton a} {i | k ∈ (v i).val} := by
  refine ⟨T.root, ⟨∅, ∅⟩, ?_, ?_, ?_, hk⟩
  · rw [hr]
    exact Finset.mem_singleton_self _
  · intro i hi; exact False.elim (Finset.notMem_empty i hi)
  · intro i hi; exact False.elim (Finset.notMem_empty i hi)

omit [DecidableEq Var] in
/-- Appending recorded frames is composition of actual one-hole syntax. -/
theorem pathBody_append {Role : Type u} (a : Role) (r : Var)
    (first second : List (Var × Var)) (fill : Term Role Var) :
    Term.pathBody a r (first ++ second) fill = Term.pathBody a r first (Term.pathBody a r second fill) := by
  induction first with
  | nil => rfl
  | cons p first ih => simp only [List.cons_append, Term.pathBody, ih]

private theorem frame_safe {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (hr : T.guards T.root = {⟨∅, ∅⟩}) (S : SaturationState Var) (w z : Var)
    (hw : T.Permitted w S.many (S.outside ∪ {w, z}))
    (hz : T.Permitted z S.many (S.outside ∪ {w, z})) (fill : Term Role Var)
    (hfill : Safe T a k (S.update w z) fill) :
    Safe T a k S (Term.guarded a (.var T.root) (Term.step fill (.var w)) (.var z)) := by
  intro v hM hN hseen
  simp only [Term.eval_guarded, WinnerSet.guardedChoice, WinnerSet.mem_reset,
    WinnerSet.mem_choice_other a k hka.symm, Term.eval_var] at hseen
  rcases hseen with hroot | ⟨_, hchild, hnotw, hnotz⟩
  · exact root_sound T a k hr v hroot
  · have hNw : v w ≠ WinnerSet.singleton a := by
      intro he
      exact hnotw ((Term.step fill (.var w)).eq_singleton_iff v a |>.mpr he)
    have hNext : ∀ i ∈ S.outside ∪ {w, z}, v i ≠ WinnerSet.singleton a := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hN i hi
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hNw
        · exact hnotz
    rcases hchild with hleft | hzseen
    · simp only [Term.eval_step, Term.eval_var, WinnerSet.mem_reset] at hleft
      rcases hleft with hwseen | ⟨hMw, hinner⟩
      · exact permitted_sound T a k hka w _ _ hw v hM hNext hwseen
      · apply hfill v ?_ ?_ hinner
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hMw
          · exact hM i hi
        · intro i hi
          exact hNext i (Finset.mem_sdiff.mp hi).1
    · exact permitted_sound T a k hka z _ _ hz v hM hNext hzseen

/-- A safe final filling remains safe through every frame the executable
saturation actually recorded. -/
private theorem run_safe {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (hr : T.guards T.root = {⟨∅, ∅⟩}) (positions : List Var) (j : Var) (g : GuardPair Var)
    (n : ℕ) (fill : Term Role Var) (hfill : Safe T a k (T.run positions j g n).1 fill) :
    Safe T a k (SaturationState.initial T.root)
      (Term.pathBody a T.root (T.run positions j g n).2 fill) := by
  induction n generalizing fill with
  | zero => exact hfill
  | succ n ih =>
    cases hn : T.next positions j g (T.run positions j g n).1 with
    | none =>
      simp only [run, hn] at hfill ⊢
      exact ih fill hfill
    | some p =>
      simp only [run, hn] at hfill ⊢
      rw [pathBody_append]
      exact ih _ (frame_safe T a k hka hr _ _ _
        (T.next_spec positions j g _ hn).2.2.1 (T.next_spec positions j g _ hn).2.2.2.1 fill hfill)

private theorem target_nonowner {Role : Type u} (a k : Role) (hka : k ≠ a)
    (j : Var) (g : GuardPair Var) (v : Var → WinnerSet Role)
    (hm : ∀ i ∈ g.many, (v i).Ambiguous) (hn : ∀ i ∈ g.outside, v i ≠ WinnerSet.singleton a)
    (hj : k ∈ (v j).val) : ∀ i ∈ target j g, v i ≠ WinnerSet.singleton a := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact hm i hi a
    · exact hn i hi
  · have he := Finset.mem_singleton.mp hi
    subst i
    intro hv
    rw [hv] at hj
    exact hka hj

omit [DecidableEq Var] in
private theorem frame_seen {Role : Type u} (a k : Role) (hka : k ≠ a) (r w z : Var)
    (fill : Term Role Var) (v : Var → WinnerSet Role) (hr : (v r).Ambiguous)
    (hw : (v w).Ambiguous) (hz : v z ≠ WinnerSet.singleton a) (hf : k ∈ (fill.eval v).val) :
    k ∈ ((Term.guarded a (.var r) (Term.step fill (.var w)) (.var z)).eval v).val := by
  simp only [Term.eval_guarded, WinnerSet.guardedChoice, Term.eval_var, WinnerSet.mem_reset,
    WinnerSet.mem_choice_other a k hka.symm, Term.eval_step]
  exact Or.inr ⟨hr, Or.inl (Or.inr ⟨hw, hf⟩), fun he => hw a ((WinnerSet.reset_eq_singleton _ _ a).mp he), hz⟩

private theorem pathBody_seen {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (j : Var) (g : GuardPair Var) (hr : T.root ∈ g.many) (frames : List (Var × Var))
    (hframes : ∀ p ∈ frames, p.1 ∈ g.many ∧ p.2 ∈ target j g) (fill : Term Role Var)
    (v : Var → WinnerSet Role) (hm : ∀ i ∈ g.many, (v i).Ambiguous)
    (hn : ∀ i ∈ g.outside, v i ≠ WinnerSet.singleton a) (hj : k ∈ (v j).val)
    (hfill : k ∈ (fill.eval v).val) :
    k ∈ (Term.pathBody a T.root frames fill |>.eval v).val := by
  induction frames with
  | nil => exact hfill
  | cons p frames ih =>
    have hp := hframes p List.mem_cons_self
    exact frame_seen a k hka T.root p.1 p.2 _ v (hm _ hr) (hm _ hp.1)
      (target_nonowner a k hka j g v hm hn hj _ hp.2)
      (ih (fun q hq => hframes q (List.mem_cons_of_mem p hq)))

private theorem finishTerm_cases {Role : Type u} (T : GuardTable Var) (a : Role)
    (positions : List Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var)
    {fill : Term Role Var} (h : T.finishTerm a positions j g S = some fill) :
    (T.Permitted j S.many S.outside ∧ fill = Term.step (.var j) (.var T.root)) ∨
    ∃ z ∈ target j g, T.Permitted j S.many (S.outside ∪ {j, z}) ∧
      T.Permitted z S.many (S.outside ∪ {j, z}) ∧
      fill = Term.guarded a (.var T.root) (.var j) (.var z) := by
  unfold finishTerm at h
  split at h
  next hp => exact Or.inl ⟨hp, (Option.some.inj h).symm⟩
  next =>
    obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
    have hp : z ∈ target j g ∧ T.Permitted j S.many (S.outside ∪ {j, z}) ∧
        T.Permitted z S.many (S.outside ∪ {j, z}) := of_decide_eq_true
      (List.find?_some (p := fun z => decide (z ∈ target j g ∧
        T.Permitted j S.many (S.outside ∪ {j, z}) ∧ T.Permitted z S.many (S.outside ∪ {j, z})))
        (a := z) hz)
    exact Or.inr ⟨z, hp.1, hp.2.1, hp.2.2, he.symm⟩

private theorem finishTerm_safe {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (hr : T.guards T.root = {⟨∅, ∅⟩}) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) {fill : Term Role Var} (h : T.finishTerm a positions j g S = some fill) :
    Safe T a k S fill := by
  rcases finishTerm_cases T a positions j g S h with ⟨hp, rfl⟩ | ⟨z, _, hpj, hpz, rfl⟩
  · intro v hm hn hseen
    simp only [Term.eval_step, Term.eval_var, WinnerSet.mem_reset] at hseen
    rcases hseen with hroot | ⟨_, hj⟩
    · exact root_sound T a k hr v hroot
    · exact permitted_sound T a k hka j _ _ hp v hm hn hj
  · intro v hm hn hseen
    simp only [Term.eval_guarded, WinnerSet.guardedChoice, Term.eval_var, WinnerSet.mem_reset,
      WinnerSet.mem_choice_other a k hka.symm] at hseen
    rcases hseen with hroot | ⟨_, hjz, hNj, hNz⟩
    · exact root_sound T a k hr v hroot
    · have hNext : ∀ i ∈ S.outside ∪ {j, z}, v i ≠ WinnerSet.singleton a := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hn i hi
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hNj
          · exact hNz
      rcases hjz with hj | hz
      · exact permitted_sound T a k hka j _ _ hpj v hm hNext hj
      · exact permitted_sound T a k hka z _ _ hpz v hm hNext hz

private theorem finishTerm_seen {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (positions : List Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var)
    (hr : T.root ∈ g.many) {fill : Term Role Var} (h : T.finishTerm a positions j g S = some fill)
    (v : Var → WinnerSet Role) (hm : ∀ i ∈ g.many, (v i).Ambiguous)
    (hn : ∀ i ∈ g.outside, v i ≠ WinnerSet.singleton a) (hj : k ∈ (v j).val) :
    k ∈ (fill.eval v).val := by
  rcases finishTerm_cases T a positions j g S h with ⟨_, rfl⟩ | ⟨z, hz, _, _, rfl⟩
  · simp only [Term.eval_step, Term.eval_var, WinnerSet.mem_reset]
    exact Or.inr ⟨hm _ hr, hj⟩
  · simp only [Term.eval_guarded, WinnerSet.guardedChoice, Term.eval_var, WinnerSet.mem_reset,
      WinnerSet.mem_choice_other a k hka.symm]
    have hNz := target_nonowner a k hka j g v hm hn hj
    exact Or.inr ⟨hm _ hr, Or.inl hj, hNz j (Finset.mem_union_right _ (Finset.mem_singleton_self _)), hNz z hz⟩

theorem finishWitness_isSome (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (hcover : target j g ⊆ positions.toFinset) :
    (T.finishWitness positions j g S).isSome = true ↔
      ∃ z ∈ target j g, T.Permitted j S.many (S.outside ∪ {j, z}) ∧
        T.Permitted z S.many (S.outside ∪ {j, z}) := by
  rw [finishWitness, List.find?_isSome]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨z, _, hz, hpj, hpz⟩
    exact ⟨z, hz, hpj, hpz⟩
  · rintro ⟨z, hz, hpj, hpz⟩
    exact ⟨z, List.mem_toFinset.mp (hcover hz), hz, hpj, hpz⟩

theorem finishTerm_isSome {Role : Type u} (T : GuardTable Var) (a : Role)
    (positions : List Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var)
    (hcover : target j g ⊆ positions.toFinset) :
    (T.finishTerm a positions j g S).isSome = true ↔ T.Finish j g S := by
  unfold finishTerm Finish
  split
  next hp => simp [hp]
  next hp =>
    simp only [Option.isSome_map, hp, false_or]
    exact finishWitness_isSome T positions j g S hcover

/-- The exact native path program succeeds precisely when the saturation
accepts this target guard. No external witness is supplied to the program. -/
theorem guardPath_isSome {Role : Type u} (T : GuardTable Var) (a : Role)
    (positions : List Var) (j : Var) (g : GuardPair Var) (hcover : target j g ⊆ positions.toFinset) :
    (T.guardPath a positions j g).isSome = true ↔ T.accepts positions j g = true := by
  unfold guardPath accepts
  split
  next hj => simp [hj]
  next hj =>
    simp only [Option.isSome_map, decide_eq_true_eq, hj, false_or]
    exact finishTerm_isSome T a positions j g _ hcover

/-- Every successful actual path has the prescribed root, only the chosen
owner, linear expanded syntax size, no forbidden contribution, and covers the
requested guard. Necessity of acceptance for every realizable table is separate. -/
theorem guardPath_spec {Role : Type u} (T : GuardTable Var) (a k : Role) (hka : k ≠ a)
    (hr : T.guards T.root = {⟨∅, ∅⟩}) (positions : List Var) (j : Var) (g : GuardPair Var)
    (hshape : j ≠ T.root → T.root ∈ g.many) (hcover : target j g ⊆ positions.toFinset)
    {t : Term Role Var} (ht : T.guardPath a positions j g = some t) :
    t.root = T.root ∧ t.OwnersIn (fun x => x = a) ∧ t.size ≤ 10 * positions.length + 6 ∧
    (∀ v : Var → WinnerSet Role, k ∈ (t.eval v).val →
      T.Enabled {i | (v i).Ambiguous} {i | v i ≠ WinnerSet.singleton a} {i | k ∈ (v i).val}) ∧
    (∀ v : Var → WinnerSet Role, (∀ i ∈ g.many, (v i).Ambiguous) →
      (∀ i ∈ g.outside, v i ≠ WinnerSet.singleton a) → k ∈ (v j).val → k ∈ (t.eval v).val) := by
  unfold guardPath at ht
  split at ht
  next hj =>
    have he := Option.some.inj ht
    subst t
    refine ⟨rfl, trivial, ?_, ?_, ?_⟩
    · simp only [Term.size_var]
      omega
    · intro v hv
      exact root_sound T a k hr v hv
    · intro v _ _ hv
      simpa only [Term.eval_var, hj] using hv
  next hj =>
    obtain ⟨fill, hfill, he⟩ := Option.map_eq_some_iff.mp ht
    subst t
    have hroot := hshape hj
    have hflen := T.run_frames_length_le positions j g hroot hcover (2 * positions.length)
    have howners : fill.OwnersIn (fun x => x = a) := by
      rcases finishTerm_cases T a positions j g _ hfill with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩
      · exact ⟨trivial, trivial⟩
      · exact ⟨rfl, trivial, trivial, trivial⟩
    have hsize : fill.size ≤ 4 := by
      rcases finishTerm_cases T a positions j g _ hfill with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
        simp only [Term.size_step, Term.size_guarded, Term.size_var] <;> omega
    refine ⟨rfl, Term.owners_pathTerm a T.root _ fill howners, ?_, ?_, ?_⟩
    · rw [Term.size_pathTerm]
      omega
    · intro v hv
      simp only [Term.pathTerm, Term.eval_step, Term.eval_var, WinnerSet.mem_reset] at hv
      rcases hv with hv | ⟨hMroot, hbody⟩
      · exact root_sound T a k hr v hv
      · apply run_safe T a k hka hr positions j g _ fill
          (finishTerm_safe T a k hka hr positions j g _ hfill) v ?_ ?_ hbody
        · intro i hi
          exact (Finset.mem_singleton.mp hi) ▸ hMroot
        · intro i hi
          exact False.elim (Finset.notMem_empty i hi)
    · intro v hm hn hv
      simp only [Term.pathTerm, Term.eval_step, Term.eval_var, WinnerSet.mem_reset]
      exact Or.inr ⟨hm _ hroot, pathBody_seen T a k hka j g hroot _
        (T.run_frames positions j g _) fill v hm hn hv
        (finishTerm_seen T a k hka positions j g _ hroot hfill v hm hn hv)⟩

end GuardTable
end KFOL.Owner
