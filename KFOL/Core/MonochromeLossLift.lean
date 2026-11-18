module

public import KFOL.Core.SourceNormalForm

/-! # Splitting a source loss by the colors that block its leaf occurrences -/

@[expose] public section
namespace KFOL.Core.MonochromeLossLift

universe u v
variable {Role : Type u} {Var : Type v}

/-- A particular occurrence of the variable `j` in the owned-choice tree. -/
inductive Occurrence (j : Var) : Term Role Var → Type (max u v) where
  | leaf : Occurrence j (.var j)
  | left {r s t} : Occurrence j s → Occurrence j (.choice r s t)
  | right {r s t} : Occurrence j t → Occurrence j (.choice r s t)

/-- No foreign owner can take its singleton from a sibling on this leaf's path. -/
def Occurrence.Survives {j : Var} {t : Term Role Var} (o : Occurrence j t)
    (k : Role) (v : Var → WinnerSet Role) : Prop :=
  match o with
  | .leaf => True
  | @Occurrence.left _ _ _ r _ t l => l.Survives k v ∧ (r ≠ k → t.eval v ≠ WinnerSet.singleton r)
  | @Occurrence.right _ _ _ r s _ l => l.Survives k v ∧ (r ≠ k → s.eval v ≠ WinnerSet.singleton r)

private theorem mem_choice_iff_paths (k r : Role) (A B : WinnerSet Role) :
    k ∈ (WinnerSet.choice r A B).val ↔
      (k ∈ A.val ∧ (r ≠ k → B ≠ WinnerSet.singleton r)) ∨
      (k ∈ B.val ∧ (r ≠ k → A ≠ WinnerSet.singleton r)) := by
  by_cases rk : r = k
  · subst r
    simp [WinnerSet.mem_choice_owner]
  · rw [WinnerSet.mem_choice_other _ _ rk]
    have notAtom (C : WinnerSet Role) (h : k ∈ C.val) : C ≠ WinnerSet.singleton r :=
      fun e => rk ((e ▸ h : k ∈ (WinnerSet.singleton r).val).symm)
    grind

variable {Name : Type*}

/-- Label each actual leaf independently, keeping all the original gates. -/
def relabel (t : Term Role Var) (ht : t.IsCore)
    (name : ∀ i, Occurrence i t → Name) : Term Role Name :=
  match t with
  | .var i => .var (name i .leaf)
  | .choice r s t => .choice r (relabel s ht.1 (fun i o => name i (.left o)))
      (relabel t ht.2 (fun i o => name i (.right o)))
  | .winner _ | .rename _ _ => False.elim ht

theorem relabel_isCore (t : Term Role Var) (ht : t.IsCore)
    (name : ∀ i, Occurrence i t → Name) : (relabel t ht name).IsCore := by
  induction t with
  | winner | rename => contradiction
  | var => trivial
  | choice _ _ _ hs ht' => exact ⟨hs ht.1 _, ht' ht.2 _⟩

private theorem collapse_relabel (t : Term Role Var) (ht : t.IsCore)
    (name : ∀ i, Occurrence i t → Name) (forget : Name → Var)
    (hl : ∀ i o, forget (name i o) = i) :
    (relabel t ht name).subst (fun x => .var (forget x)) = t := by
  induction t with
  | winner | rename => contradiction
  | var i => exact congrArg Term.var (hl i .leaf)
  | choice q s t hs ht' =>
    exact congrArg₂ (Term.choice q)
      (hs ht.1 _ (fun i o => hl i (.left o))) (ht' ht.2 _ (fun i o => hl i (.right o)))

private theorem relabel_atom (t : Term Role Var) (ht : t.IsCore)
    (name : ∀ i, Occurrence i t → Name) (v : Var → WinnerSet Role) (w : Name → WinnerSet Role)
    (r : Role) (same : ∀ i o, w (name i o) = WinnerSet.singleton r ↔ v i = WinnerSet.singleton r) :
    (relabel t ht name).eval w = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r := by
  induction t with
  | winner | rename => contradiction
  | var i => exact same i .leaf
  | choice q s t hs ht' =>
    have l := hs ht.1 (fun i o => name i (.left o)) (fun i o => same i (.left o))
    have h := ht' ht.2 (fun i o => name i (.right o)) (fun i o => same i (.right o))
    simp only [relabel, Term.eval]
    by_cases qr : q = r
    · subst q
      simpa only [WinnerSet.choice_eq_owner_iff] using or_congr l h
    · simpa only [WinnerSet.choice_eq_other_iff _ _ _ qr] using and_congr l h

/-- Reassigning the input names and their menus can select independent copies
of a repeated input. Matching foreign singleton tests preserves their paths. -/
theorem mem_relabel_iff (t : Term Role Var) (ht : t.IsCore)
    (name : ∀ i, Occurrence i t → Name) (k : Role) (v : Var → WinnerSet Role)
    (w : Name → WinnerSet Role) (same : ∀ r, r ≠ k → ∀ i o,
      w (name i o) = WinnerSet.singleton r ↔ v i = WinnerSet.singleton r) :
    k ∈ ((relabel t ht name).eval w).val ↔
      ∃ (i : Var) (o : Occurrence i t), k ∈ (w (name i o)).val ∧ o.Survives k v := by
  induction t with
  | winner | rename => contradiction
  | var i =>
    constructor
    · exact fun h => ⟨i, .leaf, h, trivial⟩
    · rintro ⟨j, o, h, _⟩
      cases o
      exact h
  | choice r s t hs ht' =>
    let l i (o : Occurrence i s) := name i (.left o)
    let h i (o : Occurrence i t) := name i (.right o)
    have sl q ne i (o : Occurrence i s) := same q ne i (.left o)
    have sr q ne i (o : Occurrence i t) := same q ne i (.right o)
    change k ∈ (WinnerSet.choice r ((relabel s ht.1 l).eval w) ((relabel t ht.2 h).eval w)).val ↔ _
    rw [mem_choice_iff_paths, hs ht.1 l sl, ht' ht.2 h sr]
    have sa (ne : r ≠ k) := (relabel_atom s ht.1 l v w r (sl r ne)).not
    have ta (ne : r ≠ k) := (relabel_atom t ht.2 h v w r (sr r ne)).not
    constructor
    · rintro (⟨⟨i, o, hi, ho⟩, clear⟩ | ⟨⟨i, o, hi, ho⟩, clear⟩)
      · exact ⟨i, .left o, hi, ho, fun ne => (ta ne).mp (clear ne)⟩
      · exact ⟨i, .right o, hi, ho, fun ne => (sa ne).mp (clear ne)⟩
    · rintro ⟨i, o, hi, ho⟩
      cases o with
      | left o => exact Or.inl ⟨⟨i, o, hi, ho.1⟩, fun ne => (ta ne).mpr (ho.2 ne)⟩
      | right o => exact Or.inr ⟨⟨i, o, hi, ho.1⟩, fun ne => (sa ne).mpr (ho.2 ne)⟩

/-- Evaluation selects exactly the input winners with some surviving occurrence.
The input valuation is arbitrary, so several variables may carry the winner. -/
theorem mem_iff_occurrence (t : Term Role Var) (ht : t.IsCore) (k : Role)
    (v : Var → WinnerSet Role) :
    k ∈ (t.eval v).val ↔ ∃ (j : Var) (o : Occurrence j t), k ∈ (v j).val ∧ o.Survives k v := by
  have identity (s : Term Role Var) (hs : s.IsCore) : (relabel s hs (fun i _ => i)) = s := by
    induction s with
    | winner | rename => contradiction
    | var => rfl
    | choice r _ _ hl hr => exact congrArg₂ (Term.choice r) (hl hs.1) (hr hs.2)
  simpa only [identity] using
    mem_relabel_iff t ht (fun i _ => i) k v v (fun _ _ _ _ => Iff.rfl)

/-- Retain precisely the postings at one foreign owner. -/
noncomputable def component {k : Role} {j : Var} (r : {r : Role // r ≠ k})
    (p : Sources.Pattern k j) : Sources.Pattern k j := by
  classical
  exact fun i => if p i = .atom r then .atom r else .neutral

private theorem atom_iff_component (three : Fin 3 ↪ Role) {k : Role} {j : Var}
    (p : Sources.Pattern k j) (r : {r : Role // r ≠ k}) (t : Term Role Var) (ht : t.IsCore) :
    t.eval (Sources.probe three k j p) = WinnerSet.singleton r.val ↔
      t.eval (Sources.probe three k j (component r p)) = WinnerSet.singleton r.val := by
  classical
  apply ht.isPublic.eval_singleton_iff_of_tests
  intro i
  by_cases ij : i = j
  · subst i
    simp
  · rw [Sources.probe_other _ _ _ _ _ ij, Sources.probe_other _ _ _ _ _ ij,
      Sources.representative_atom_iff _ _ _ r, Sources.representative_atom_iff _ _ _ r]
    by_cases h : p ⟨i, ij⟩ = .atom r <;> simp [component, h]

private theorem Occurrence.survives_mono {j : Var} {t : Term Role Var} (o : Occurrence j t)
    (k : Role) {v w : Var → WinnerSet Role} (sub : ∀ i, (v i).val ⊆ (w i).val) :
    o.Survives k v → o.Survives k w := by
  have lift (s : Term Role Var) (r : Role) (h : s.eval v ≠ WinnerSet.singleton r) :
      s.eval w ≠ WinnerSet.singleton r := by
    intro he
    exact h (WinnerSet.eq_singleton_of_subset _ r (by simpa [he] using s.eval_mono sub))
  induction o with
  | leaf => exact id
  | left _ ih | right _ ih => exact fun h => ⟨ih h.1, fun ne => lift _ _ (h.2 ne)⟩

/-- One particular occurrence survives the mixed row exactly when this same
occurrence survives every single-color component. -/
theorem Occurrence.survives_iff_components (three : Fin 3 ↪ Role) {k : Role} {j : Var}
    (p : Sources.Pattern k j) {t : Term Role Var} (o : Occurrence j t) (ht : t.IsCore) :
    o.Survives k (Sources.probe three k j p) ↔
      ∀ r, o.Survives k (Sources.probe three k j (component r p)) := by
  constructor
  · intro h r
    apply o.survives_mono k (Sources.probe_mono three k j ?_) h
    intro i
    classical
    by_cases e : p i = .atom r
    · exact Or.inr (by simp [component, e])
    · exact Or.inl (by simp [component, e])
  · induction o with
    | leaf => exact fun _ => trivial
    | @left r s t o ih =>
      intro h
      refine ⟨ih ht.1 (fun q => (h q).1), ?_⟩
      intro rk blocked
      exact (h ⟨r, rk⟩).2 rk ((atom_iff_component three p ⟨r, rk⟩ t ht.2).mp blocked)
    | @right r s t o ih =>
      intro h
      refine ⟨ih ht.2 (fun q => (h q).1), ?_⟩
      intro rk blocked
      exact (h ⟨r, rk⟩).2 rk ((atom_iff_component three p ⟨r, rk⟩ s ht.1).mp blocked)

/-- A mixed loss has a coloring of the occurrences of its head. On each
single-color component all occurrences tagged with that color are blocked. -/
theorem omits_iff_color_blocked (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (k : Role) (j : Var) (p : Sources.Pattern k j) :
    k ∉ (t.eval (Sources.probe three k j p)).val ↔
      ∃ tag : Occurrence j t → {r : Role // r ≠ k},
        ∀ o : Occurrence j t, ¬ o.Survives k (Sources.probe three k j (component (tag o) p)) := by
  classical
  have mixed : k ∈ (t.eval (Sources.probe three k j p)).val ↔
      ∃ o : Occurrence j t, o.Survives k (Sources.probe three k j p) := by
    rw [mem_iff_occurrence t ht]
    constructor
    · rintro ⟨i, o, hi, ho⟩
      obtain rfl := (Sources.mem_probe_iff three k j p i).mp hi
      exact ⟨o, ho⟩
    · rintro ⟨o, ho⟩
      exact ⟨j, o, (Sources.mem_probe_iff three k j p j).mpr rfl, ho⟩
  rw [mixed, not_exists]
  constructor
  · intro h
    have blocks (o : Occurrence j t) : ∃ r, ¬ o.Survives k (Sources.probe three k j (component r p)) :=
      not_forall.mp (fun all => h o ((o.survives_iff_components three p ht).mpr all))
    exact ⟨fun o => (blocks o).choose, fun o => (blocks o).choose_spec⟩
  · rintro ⟨tag, blocks⟩ o h
    exact blocks o ((o.survives_iff_components three p ht).mp h (tag o))

/-- A tagged copy of the head becomes a new source input bearing its color.
All other leaves keep their original variable names. -/
noncomputable def taggedName {t : Term Role Var} {j : Var} {k : Role}
    (tag : Occurrence j t → {r : Role // r ≠ k}) (i : Var) (o : Occurrence i t) :
    Var ⊕ {r : Role // r ≠ k} := by
  classical
  exact if e : i = j then .inr (tag (e ▸ o)) else .inl i

/-- Identifying the tagged copies with the original head recovers the original syntax. -/
theorem collapse_tagged {t : Term Role Var} (ht : t.IsCore) {j : Var} {k : Role}
    (tag : Occurrence j t → {r : Role // r ≠ k}) :
    (relabel t ht (taggedName tag)).subst (fun x => .var (x.elim id (fun _ => j))) = t := by
  apply collapse_relabel
  intro i o
  by_cases eq : i = j
  · subst i
    simp [taggedName]
  · simp [taggedName, eq]

/-- On a pure lifted row only the source tagged `r` carries the observer.
The original non-head inputs retain just the postings of color `r`. -/
noncomputable def taggedPattern {j : Var} {k : Role} (p : Sources.Pattern k j)
    (r : {r : Role // r ≠ k}) : Sources.Pattern k (Sum.inr r : Var ⊕ {s : Role // s ≠ k}) := by
  classical
  exact fun a => match a.val with
    | .inr _ => .neutral
    | .inl i => if e : i = j then .neutral else component r p ⟨i, e⟩

theorem mem_tagged_probe_iff (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    {k : Role} {j : Var} (p : Sources.Pattern k j) (tag : Occurrence j t → {r : Role // r ≠ k})
    (r : {r : Role // r ≠ k}) :
    k ∈ ((relabel t ht (taggedName tag)).eval
      (Sources.probe three k (.inr r) (taggedPattern p r))).val ↔
        ∃ o : Occurrence j t, tag o = r ∧ o.Survives k (Sources.probe three k j (component r p)) := by
  classical
  rw [mem_relabel_iff _ _ _ _ (Sources.probe three k j (component r p))]
  · simp only [Sources.mem_probe_iff]
    constructor
    · rintro ⟨i, o, eq, ho⟩
      by_cases ij : i = j
      · subst i
        exact ⟨o, by simpa [taggedName] using eq, ho⟩
      · simp [taggedName, ij] at eq
    · rintro ⟨o, eq, ho⟩
      exact ⟨j, o, by simp [taggedName, eq], ho⟩
  · intro s sk i o
    by_cases ij : i = j
    · subst i
      simp only [taggedName, Sources.probe_source]
      by_cases eq : tag o = r
      · simp [eq]
      · rw [Sources.probe_other _ _ _ _ _ (by simpa using eq)]
        rw [Sources.representative_atom_iff _ _ _ ⟨s, sk⟩]
        simp [taggedPattern, Ne.symm sk]
    · simp only [taggedName, dite_eq_right ij]
      rw [Sources.probe_other _ _ _ _ _ (by simp), Sources.probe_other _ _ _ _ _ ij]
      simp [taggedPattern, ij]

/-- The mixed source omission is equivalent to ordinary semantic omissions
on all pure rows of a single relabeling of the given syntax tree. -/
theorem omits_iff_tagged_pure_probes (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (k : Role) (j : Var) (p : Sources.Pattern k j) :
    k ∉ (t.eval (Sources.probe three k j p)).val ↔
      ∃ tag : Occurrence j t → {r : Role // r ≠ k}, ∀ r,
        k ∉ ((relabel t ht (taggedName tag)).eval
          (Sources.probe three k (.inr r) (taggedPattern p r))).val := by
  rw [omits_iff_color_blocked three t ht k j p]
  apply exists_congr
  intro tag
  simp only [mem_tagged_probe_iff, not_exists, not_and]
  exact ⟨fun all _ o e => e ▸ all o, fun all o => all (tag o) o rfl⟩

end KFOL.Core.MonochromeLossLift
