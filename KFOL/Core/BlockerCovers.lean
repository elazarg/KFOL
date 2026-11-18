module

public import KFOL.Core.MonochromeLossLift

/-! # Universal color dictionaries for mixed losses at one head -/

@[expose] public section
namespace KFOL.Core.BlockerCovers

open MonochromeLossLift

variable {Role Var Row : Type*} {h : Var}

/-- The observer may differ from row to row. All rows mark the same input. -/
structure Sample (Role Var Row : Type*) (h : Var) where
  observer : Row → Role
  pattern : (i : Row) → Sources.Pattern (observer i) h

variable (S : Sample Role Var Row h)

/-- The variables actually posted at a given color in the row. -/
def postings (i : Row) (r : Role) : Set Var :=
  {x | ∃ (ne : x ≠ h) (rk : r ≠ S.observer i), S.pattern i ⟨x, ne⟩ = .atom ⟨r, rk⟩}

noncomputable abbrev values (three : Fin 3 ↪ Role) (i : Row) :=
  Sources.probe three (S.observer i) h (S.pattern i)

private theorem mem_postings (three : Fin 3 ↪ Role) (i : Row) {r : Role}
    (rk : r ≠ S.observer i) (x : Var) :
    x ∈ postings S i r ↔ values S three i x = WinnerSet.singleton r := by
  classical
  by_cases xh : x = h
  · subst x
    simp [postings, values, Ne.symm rk]
  · rw [values, Sources.probe_other _ _ _ _ _ xh, Sources.representative_atom_iff _ _ _ ⟨r, rk⟩]
    exact ⟨fun ⟨_, _, e⟩ => e, fun e => ⟨xh, rk, e⟩⟩

/-- A cover chooses an upset of nonempty posting coalitions for each color,
and at least one chosen foreign color in every row. -/
structure IsCover (U : Set (Row × Role)) : Prop where
  valid : ∀ {i r}, (i, r) ∈ U → r ≠ S.observer i ∧ (postings S i r).Nonempty
  upward : ∀ {i l r}, (i, r) ∈ U → r ≠ S.observer l →
    postings S i r ⊆ postings S l r → (l, r) ∈ U
  covers : ∀ i, ∃ r, (i, r) ∈ U

/-- A sibling at an r-gate can supply the r-singleton. -/
def Blocks {t : Term Role Var} (o : Occurrence h t) (r : Role)
    (v : Var → WinnerSet Role) : Prop :=
  match o with
  | .leaf => False
  | @Occurrence.left _ _ _ s _ y p => Blocks p r v ∨ (s = r ∧ y.eval v = WinnerSet.singleton r)
  | @Occurrence.right _ _ _ s x _ p => Blocks p r v ∨ (s = r ∧ x.eval v = WinnerSet.singleton r)

private theorem singleton_mono (t : Term Role Var) (ht : t.IsCore) (r : Role)
    {v w : Var → WinnerSet Role} (sub : ∀ x, v x = WinnerSet.singleton r → w x = WinnerSet.singleton r) :
    t.eval v = WinnerSet.singleton r → t.eval w = WinnerSet.singleton r := by
  induction t with
  | winner | rename => contradiction
  | var i => exact sub i
  | choice s _ _ hs ht' =>
    by_cases sr : s = r
    · subst s
      simp only [Term.eval, WinnerSet.choice_eq_owner_iff]
      exact Or.imp (hs ht.1) (ht' ht.2)
    · simp only [Term.eval, WinnerSet.choice_eq_other_iff _ _ _ sr]
      exact And.imp (hs ht.1) (ht' ht.2)

private theorem singleton_input (t : Term Role Var) (ht : t.IsCore) (r : Role)
    (v : Var → WinnerSet Role) :
    t.eval v = WinnerSet.singleton r → ∃ x, v x = WinnerSet.singleton r := by
  induction t with
  | winner | rename => contradiction
  | var i => exact fun e => ⟨i, e⟩
  | choice s _ _ hs ht' =>
    by_cases sr : s = r
    · subst s
      exact fun e => ((WinnerSet.choice_eq_owner_iff _ _ _).mp e).elim (hs ht.1) (ht' ht.2)
    · exact fun e => hs ht.1 ((WinnerSet.choice_eq_other_iff _ _ _ sr).mp e).1

private theorem block_mono {t : Term Role Var} (o : Occurrence h t) (ht : t.IsCore)
    (r : Role) {v w : Var → WinnerSet Role}
    (sub : ∀ x, v x = WinnerSet.singleton r → w x = WinnerSet.singleton r) :
    Blocks o r v → Blocks o r w := by
  induction o with
  | leaf => exact id
  | left _ ih => exact Or.imp (ih ht.1) (fun e => ⟨e.1, singleton_mono _ ht.2 r sub e.2⟩)
  | right _ ih => exact Or.imp (ih ht.2) (fun e => ⟨e.1, singleton_mono _ ht.1 r sub e.2⟩)

private theorem block_input {t : Term Role Var} (o : Occurrence h t) (ht : t.IsCore)
    (r : Role) (v : Var → WinnerSet Role) :
    Blocks o r v → ∃ x, v x = WinnerSet.singleton r := by
  induction o with
  | leaf => exact False.elim
  | left _ ih => exact fun e => e.elim (ih ht.1) (fun h => singleton_input _ ht.2 r v h.2)
  | right _ ih => exact fun e => e.elim (ih ht.2) (fun h => singleton_input _ ht.1 r v h.2)

theorem not_survives_iff {t : Term Role Var} (o : Occurrence h t) (k : Role)
    (v : Var → WinnerSet Role) : ¬ o.Survives k v ↔ ∃ r, r ≠ k ∧ Blocks o r v := by
  classical
  induction o with
  | leaf => simp [Occurrence.Survives, Blocks]
  | left _ ih | right _ ih =>
    simp only [Occurrence.Survives, not_and_or, not_forall, not_not, ih, Blocks]
    grind

/-- The actual eligible color choices of one occurrence. -/
def blockedSet (three : Fin 3 ↪ Role) {t : Term Role Var} (o : Occurrence h t) : Set (Row × Role) :=
  {p | p.2 ≠ S.observer p.1 ∧ Blocks o p.2 (values S three p.1)}

/-- Every omitted occurrence gives an upset cover, even with row-specific observers. -/
theorem occurrence_cover (three : Fin 3 ↪ Role) {t : Term Role Var} (ht : t.IsCore)
    (o : Occurrence h t) (loss : ∀ i, ¬ o.Survives (S.observer i) (values S three i)) :
    IsCover S (blockedSet S three o) where
  valid := by
    rintro i r ⟨rk, b⟩
    obtain ⟨x, hx⟩ := block_input o ht r _ b
    exact ⟨rk, x, (mem_postings S three i rk x).mpr hx⟩
  upward := by
    rintro i l r ⟨ri, b⟩ rl sub
    exact ⟨rl, block_mono o ht r (fun x hx =>
      (mem_postings S three l rl x).mp (sub ((mem_postings S three i ri x).mpr hx))) b⟩
  covers i := (not_survives_iff o _ _).mp (loss i)

/-- All row-color pairs forced upwards by a choice of one color per row. -/
def generated (tag : Row → Role) : Set (Row × Role) :=
  {p | p.2 ≠ S.observer p.1 ∧ ∃ i, tag i = p.2 ∧ postings S i p.2 ⊆ postings S p.1 p.2}

def Legal (tag : Row → Role) : Prop :=
  ∀ i, tag i ≠ S.observer i ∧ (postings S i (tag i)).Nonempty

theorem generated_isCover (tag : Row → Role) (ok : Legal S tag) : IsCover S (generated S tag) where
  valid := by
    rintro l r ⟨rl, i, rfl, sub⟩
    exact ⟨rl, (ok i).2.mono sub⟩
  upward := by
    rintro l j r ⟨_, i, hr, sub⟩ rj sub'
    exact ⟨rj, i, hr, sub.trans sub'⟩
  covers i := ⟨tag i, (ok i).1, i, rfl, Set.Subset.rfl⟩

theorem generated_le (tag : Row → Role) {U : Set (Row × Role)} (u : IsCover S U)
    (hit : ∀ i, (i, tag i) ∈ U) : generated S tag ⊆ U := by
  rintro ⟨l, r⟩ ⟨rl, i, eq, sub⟩
  change tag i = r at eq
  subst r
  exact u.upward (hit i) rl sub

private theorem exists_clause (q r : Role) (qr : q ≠ r) (a : Var) (ha : a ≠ h)
    (xs : List Var) (away : ∀ x ∈ xs, x ≠ h) :
    ∃ t : Term Role Var, t.IsCore ∧ IsEmpty (Occurrence h t) ∧
      ∀ v : Var → WinnerSet Role, t.eval v = WinnerSet.singleton r ↔
        v a = WinnerSet.singleton r ∧ ∀ x ∈ xs, v x = WinnerSet.singleton r := by
  induction xs with
  | nil =>
    refine ⟨.var a, trivial, ⟨fun o => ?_⟩, fun _ => by simp [Term.eval]⟩
    cases o
    exact ha rfl
  | cons x xs ih =>
    obtain ⟨t, ht, hon, atom⟩ := ih (fun y hy => away y (List.mem_cons_of_mem _ hy))
    refine ⟨.choice q (.var x) t, ⟨trivial, ht⟩, ⟨fun o => ?_⟩, fun v => ?_⟩
    · cases o with
      | left o => cases o; exact away h List.mem_cons_self rfl
      | right o => exact hon.false o
    · simp only [Term.eval, WinnerSet.choice_eq_other_iff _ _ _ qr, atom,
        List.forall_mem_cons]
      tauto

private theorem helper [Finite Var] (three : Fin 3 ↪ Role) (i : Row) (r : Role)
    (hne : (postings S i r).Nonempty) :
    ∃ t : Term Role Var, t.IsCore ∧ IsEmpty (Occurrence h t) ∧
      ∀ l, r ≠ S.observer l → (t.eval (values S three l) = WinnerSet.singleton r ↔
        postings S i r ⊆ postings S l r) := by
  classical
  let : Nontrivial Role := three.injective.nontrivial
  obtain ⟨q, hq⟩ := exists_ne r
  obtain ⟨a, ha⟩ := hne
  let xs := (postings S i r).toFinite.toFinset.toList
  have mem (x : Var) : x ∈ xs ↔ x ∈ postings S i r := by simp [xs]
  obtain ⟨t, ht, hon, atom⟩ := exists_clause q r hq a ha.choose xs
    (fun x hx => ((mem x).mp hx).choose)
  refine ⟨t, ht, hon, fun l rl => ?_⟩
  rw [atom]
  constructor
  · exact fun cond x hx => (mem_postings S three l rl x).mpr (cond.2 x ((mem x).mpr hx))
  · exact fun sub => ⟨(mem_postings S three l rl a).mp (sub ha),
      fun x hx => (mem_postings S three l rl x).mp (sub ((mem x).mp hx))⟩

private theorem spine [Finite Var] (three : Fin 3 ↪ Role) (entries : List (Row × Role))
    (valid : ∀ e ∈ entries, (postings S e.1 e.2).Nonempty) :
    ∃ (t : Term Role Var) (o : Occurrence h t), t.IsCore ∧ (∀ o', o' = o) ∧
      ∀ l r, r ≠ S.observer l → (Blocks o r (values S three l) ↔
        ∃ e ∈ entries, e.2 = r ∧ postings S e.1 r ⊆ postings S l r) := by
  induction entries with
  | nil =>
    exact ⟨.var h, .leaf, trivial, fun o' => by cases o'; rfl,
      fun _ _ _ => by simp [Blocks]⟩
  | cons e xs ih =>
    obtain ⟨t, o, ht, unique, blocked⟩ := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    obtain ⟨g, hg, empty, atg⟩ := helper S three e.1 e.2 (valid e List.mem_cons_self)
    refine ⟨.choice e.2 t g, .left o, ⟨ht, hg⟩, ?_, ?_⟩
    · intro o'
      cases o' with
      | left a => exact congrArg Occurrence.left (unique a)
      | right a => exact (empty.false a).elim
    · intro l r rl
      rw [show Blocks (.left (r := e.2) (t := g) o) r (values S three l) ↔
        Blocks o r (values S three l) ∨ (e.2 = r ∧ g.eval (values S three l) = WinnerSet.singleton r)
        from Iff.rfl, blocked l r rl]
      simp only [List.mem_cons, exists_eq_or_imp]
      by_cases eq : e.2 = r
      · subst r
        rw [atg l rl]
        exact or_comm
      · simp [eq]

/-- Every cover occurs exactly as the blockers of the unique head occurrence
in an actual core word omitting the sample. The other leaves are passive. -/
theorem exists_spine [Finite Role] [Finite Var] [Finite Row] (three : Fin 3 ↪ Role)
    {U : Set (Row × Role)} (u : IsCover S U) :
    ∃ (t : Term Role Var) (o : Occurrence h t), t.IsCore ∧ (∀ o', o' = o) ∧
      blockedSet S three o = U ∧
      ∀ i, S.observer i ∉ (t.eval (values S three i)).val := by
  classical
  let entries := U.toFinite.toFinset.toList
  have mem (x : Row × Role) : x ∈ entries ↔ x ∈ U := by simp [entries]
  obtain ⟨t, o, ht, unique, blocks⟩ := spine S three entries
    (fun e he => (u.valid ((mem e).mp he)).2)
  have eq : blockedSet S three o = U := by
    ext ⟨l, r⟩
    constructor
    · rintro ⟨rl, b⟩
      obtain ⟨⟨i, s⟩, he, eq, sub⟩ := (blocks l r rl).mp b
      change s = r at eq
      subst s
      exact u.upward ((mem _).mp he) rl sub
    · intro he
      have rl := (u.valid he).1
      exact ⟨rl, (blocks l r rl).mpr ⟨(l, r), (mem _).mpr he, rfl, Set.Subset.rfl⟩⟩
  refine ⟨t, o, ht, unique, eq, ?_⟩
  intro i hit
  obtain ⟨x, o', hx, survives⟩ := (mem_iff_occurrence t ht _ _).mp hit
  obtain rfl := (Sources.mem_probe_iff three _ h _ x).mp hx
  obtain ⟨r, hr⟩ := u.covers i
  rw [← eq] at hr
  exact (not_survives_iff o _ _).mpr ⟨r, hr⟩ (unique o' ▸ survives)

/-- A dictionary works for every tree that omits the sample if each actual
occurrence can use one of its color assignments on all the rows at once. -/
def Universal (three : Fin 3 ↪ Role) (dictionary : Set (Row → Role)) : Prop :=
  ∀ (t : Term Role Var), t.IsCore → (∀ i, S.observer i ∉ (t.eval (values S three i)).val) →
    ∀ o : Occurrence h t, ∃ tag ∈ dictionary, ∀ i, (i, tag i) ∈ blockedSet S three o

/-- Exactly the minimal upset covers must be represented by the dictionary.
Each legal tag vector generates just one cover. -/
theorem universal_iff_minimal_covers [Finite Role] [Finite Var] [Finite Row] (three : Fin 3 ↪ Role)
    (dictionary : Set (Row → Role)) :
    Universal S three dictionary ↔ ∀ U, Minimal (IsCover S) U →
      ∃ tag ∈ dictionary, Legal S tag ∧ generated S tag = U := by
  classical
  constructor
  · intro all U m
    obtain ⟨t, o, ht, _, eq, loss⟩ := exists_spine S three m.prop
    obtain ⟨tag, hd, hit⟩ := all t ht loss o
    rw [eq] at hit
    have ok : Legal S tag := fun i => m.prop.valid (hit i)
    exact ⟨tag, hd, ok, m.eq_of_le (generated_isCover S tag ok) (generated_le S tag m.prop hit)⟩
  · intro all t ht loss o
    have cov := occurrence_cover S three ht o (fun i survives => loss i
      ((mem_iff_occurrence t ht _ _).mpr ⟨h, o, (Sources.mem_probe_iff three _ h _ h).mpr rfl, survives⟩))
    obtain ⟨U, sub, least⟩ := exists_minimal_le_of_wellFoundedLT (IsCover S) _ cov
    obtain ⟨tag, hd, ok, rfl⟩ := all U least
    exact ⟨tag, hd, fun i => sub ⟨(ok i).1, i, rfl, Set.Subset.rfl⟩⟩

private theorem pure_atom (three : Fin 3 ↪ Role) (i : Row)
    (r : {r : Role // r ≠ S.observer i}) (q : Role) (qk : q ≠ S.observer i) (x : Var) :
    Sources.probe three (S.observer i) h (component r (S.pattern i)) x = WinnerSet.singleton q ↔
      q = r.val ∧ values S three i x = WinnerSet.singleton q := by
  classical
  by_cases xh : x = h
  · subst x
    simp [values, Ne.symm qk]
  · rw [Sources.probe_other _ _ _ _ _ xh, values, Sources.probe_other _ _ _ _ _ xh,
      Sources.representative_atom_iff _ _ _ ⟨q, qk⟩, Sources.representative_atom_iff _ _ _ ⟨q, qk⟩]
    by_cases e : S.pattern i ⟨x, xh⟩ = .atom r
    · simp [component, e, Subtype.ext_iff, eq_comm]
    · by_cases qr : q = r.val
      · subst q
        simp [component, e]
      · simp [component, e, qr]

/-- Membership in an occurrence cover is the semantic failure of that
occurrence on the indicated pure probe, as in the mixed-loss lift. -/
theorem mem_blockedSet_iff_pure (three : Fin 3 ↪ Role) {t : Term Role Var} (ht : t.IsCore)
    (o : Occurrence h t) (i : Row) (r : {r : Role // r ≠ S.observer i}) :
    (i, r.val) ∈ blockedSet S three o ↔
      ¬ o.Survives (S.observer i) (Sources.probe three (S.observer i) h (component r (S.pattern i))) := by
  rw [not_survives_iff]
  constructor
  · rintro ⟨_, b⟩
    exact ⟨r.val, r.property, block_mono o ht r.val
      (fun x a => (pure_atom S three i r r.val r.property x).mpr ⟨rfl, a⟩) b⟩
  · rintro ⟨q, qk, b⟩
    obtain ⟨x, hx⟩ := block_input o ht q _ b
    obtain rfl := ((pure_atom S three i r q qk x).mp hx).1
    exact ⟨qk, block_mono o ht _ (fun y hy => ((pure_atom S three i r _ qk y).mp hy).2) b⟩

abbrev MinimalCover := {U : Set (Row × Role) // Minimal (IsCover S) U}

private theorem exists_tag (U : MinimalCover S) :
    ∃ tag, Legal S tag ∧ generated S tag = U.val := by
  classical
  choose tag hit using U.property.prop.covers
  have legal : Legal S tag := fun i => U.property.prop.valid (hit i)
  exact ⟨tag, legal, U.property.eq_of_le (generated_isCover S tag legal)
    (generated_le S tag U.property.prop hit)⟩

/-- One representative per minimal cover suffices, and every universal
dictionary has at least that many names. -/
theorem optimal_dictionary [Finite Role] [Finite Var] [Finite Row] (three : Fin 3 ↪ Role) :
    (∃ D : Set (Row → Role), Universal S three D ∧ Nonempty (MinimalCover S ≃ D)) ∧
    ∀ D : Set (Row → Role), Universal S three D → Nonempty (MinimalCover S ↪ D) := by
  classical
  choose pick legal gen using exists_tag S
  have inj : Function.Injective pick := by
    intro U W same
    apply Subtype.ext
    exact (gen U).symm.trans ((congrArg (generated S) same).trans (gen W))
  constructor
  · refine ⟨Set.range pick, (universal_iff_minimal_covers S three _).mpr ?_,
      ⟨Equiv.ofInjective pick inj⟩⟩
    intro U m
    exact ⟨pick ⟨U, m⟩, Set.mem_range_self _, legal _, gen _⟩
  · intro D all
    have repr (U : MinimalCover S) := (universal_iff_minimal_covers S three D).mp all U.val U.property
    choose f inside _ fg using repr
    refine ⟨⟨fun U => ⟨f U, inside U⟩, ?_⟩⟩
    intro U W eq
    apply Subtype.ext
    exact (fg U).symm.trans ((congrArg (generated S) (congrArg Subtype.val eq)).trans (fg W))

end KFOL.Core.BlockerCovers
