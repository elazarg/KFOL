module

public import KFOL.Algebra.PairTests
public import KFOL.Definitions.TestDomains
public import Mathlib.Data.Fintype.List
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Sharp fixed input domains

Each singleton and each pair is isolated by a unary equation in the actual
full signature. Together with pair countervaluations this characterizes all
complete fixed test domains. Union and reset below are derived terms, not
extra primitive operations or arbitrary set constants.
-/

@[expose] public section

namespace KFOL

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

/-- A derived union term using three distinct owners. -/
def unionTerm (three : Fin 3 ↪ Role) (s t : Term Role Var) : Term Role Var :=
  .choice (three 2) (.choice (three 0) s t) (.choice (three 1) s t)

@[simp] theorem eval_unionTerm (three : Fin 3 ↪ Role) (s t : Term Role Var)
    (v : Var → WinnerSet Role) :
    (unionTerm three s t).eval v = WinnerSet.union (s.eval v) (t.eval v) := by
  exact WinnerSet.three_owner_union _ _ _ _ _
    (three.injective.ne (by decide)) (three.injective.ne (by decide))
    (three.injective.ne (by decide))

private noncomputable def collect (three : Fin 3 ↪ Role) (roles : List Role)
    (enabled : Role → Prop) (piece : Role → Term Role Var) (base : Term Role Var) :
    Term Role Var := by
  classical
  exact match roles with
  | [] => base
  | i :: rest => if enabled i then unionTerm three (piece i)
      (collect three rest enabled piece base) else collect three rest enabled piece base

private theorem mem_eval_collect (three : Fin 3 ↪ Role) (roles : List Role)
    (enabled : Role → Prop) (piece : Role → Term Role Var) (base : Term Role Var)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ ((collect three roles enabled piece base).eval v).val ↔
      k ∈ (base.eval v).val ∨ ∃ i ∈ roles, enabled i ∧ k ∈ ((piece i).eval v).val := by
  classical
  induction roles with
  | nil => simp [collect]
  | cons i rest ih =>
    by_cases hi : enabled i
    · simp only [collect, ite_eq_left hi, eval_unionTerm, WinnerSet.val_union,
        Set.mem_union, ih]
      constructor
      · rintro (hp | hb | ⟨j, hj, he, hp⟩)
        · exact Or.inr ⟨i, by simp, hi, hp⟩
        · exact Or.inl hb
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, he, hp⟩
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inr (Or.inl hb)
        · rcases List.mem_cons.mp hj with hj | hj
          · subst j; exact Or.inl hp
          · exact Or.inr (Or.inr ⟨j, hj, he, hp⟩)
    · simp only [collect, ite_eq_right hi, ih]
      constructor
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inl hb
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, he, hp⟩
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inl hb
        · rcases List.mem_cons.mp hj with hj | hj
          · subst j; exact False.elim (hi he)
          · exact Or.inr ⟨j, hj, he, hp⟩

/-- Every nonempty set of finitely many roles is denoted by a genuine constant
term, with no dependence on the valuation. -/
theorem exists_constant [Fintype Role] (three : Fin 3 ↪ Role) (A : WinnerSet Role) :
    ∃ t : Term Role Var, ∀ v, t.eval v = A := by
  classical
  obtain ⟨a, ha⟩ := A.property
  refine ⟨collect three (Finset.univ.toList) (fun i => i ∈ A.val) .winner (.winner a), ?_⟩
  intro v
  apply Subtype.ext
  apply Set.ext
  intro k
  rw [mem_eval_collect]
  simp only [eval, WinnerSet.val_singleton, Set.mem_singleton_iff,
    Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim (fun h => h ▸ ha) (fun ⟨i, hi, hk⟩ => hk ▸ hi),
    fun hk => Or.inr ⟨k, hk, rfl⟩⟩

private def suppress (roles : List Role) (acc base : Term Role Var) : Term Role Var :=
  match roles with
  | [] => acc
  | r :: rest => .choice r (suppress rest acc base) base

private theorem eval_suppress_atom (roles : List Role) (acc base : Term Role Var)
    (v : Var → WinnerSet Role) (a : Role) (ha : a ∈ roles)
    (hbase : base.eval v = WinnerSet.singleton a) :
    (suppress roles acc base).eval v = WinnerSet.singleton a := by
  classical
  induction roles with
  | nil => simp at ha
  | cons r rest ih =>
    rcases List.mem_cons.mp ha with hr | hr
    · subst r
      simp [suppress, eval, hbase, WinnerSet.choice]
    · simp only [suppress, eval, ih hr, hbase, WinnerSet.choice_self]

private theorem eval_suppress_ambiguous (roles : List Role) (acc base : Term Role Var)
    (v : Var → WinnerSet Role) (hbase : ∀ r, base.eval v ≠ WinnerSet.singleton r)
    (hsub : (base.eval v).val ⊆ (acc.eval v).val) :
    (suppress roles acc base).eval v = acc.eval v := by
  classical
  have hacc : ∀ r, acc.eval v ≠ WinnerSet.singleton r := by
    intro r he
    exact hbase r (WinnerSet.eq_singleton_of_subset _ r (by simpa [he] using hsub))
  induction roles with
  | nil => rfl
  | cons r rest ih =>
    simp only [suppress, eval, ih, WinnerSet.choice, hbase r, hacc r,
      or_self]
    apply Subtype.ext
    exact Set.union_eq_left.mpr hsub

/-- A unary full-language equation isolates each atomic input. -/
theorem exists_singleton_separator (three : Fin 3 ↪ Role) (a k : Role) (hak : a ≠ k) :
    ∃ s t : Term Role (Fin 1),
      (∀ A : WinnerSet Role, A ≠ WinnerSet.singleton a →
        s.eval (fun _ => A) = t.eval (fun _ => A)) ∧
      s.eval (fun _ => WinnerSet.singleton a) ≠ t.eval (fun _ => WinnerSet.singleton a) := by
  classical
  refine ⟨.choice a (.var 0) (.winner k), unionTerm three (.var 0) (.winner k), ?_, ?_⟩
  · intro A hA
    simp [eval, WinnerSet.choice, hA, Ne.symm hak]
  · intro he
    have hmem : k ∈ (WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton k)).val :=
      Or.inr rfl
    have hp : WinnerSet.singleton a = WinnerSet.union (WinnerSet.singleton a)
        (WinnerSet.singleton k) := by simpa [eval, WinnerSet.choice] using he
    rw [← hp] at hmem
    exact hak (Set.mem_singleton_iff.mp hmem).symm

private theorem exists_pair_expander [Fintype Role] (three : Fin 3 ↪ Role)
    (a b k : Role) (hak : a ≠ k) (hbk : b ≠ k) :
    ∃ t : Term Role (Fin 1),
      (∀ A, A.val ⊆ (t.eval (fun _ => A)).val) ∧
      (∀ A, k ∈ (t.eval (fun _ => A)).val ↔ ¬ A.val ⊆ {a, b}) ∧
      (∀ A i, i ≠ k → i ∈ (t.eval (fun _ => A)).val) := by
  classical
  let C : WinnerSet Role := ⟨{i | i ≠ k}, a, hak⟩
  obtain ⟨ground, hg⟩ := exists_constant (Var := Fin 1) three C
  let enabled := fun i => i ≠ a ∧ i ≠ b ∧ i ≠ k
  let piece : Role → Term Role (Fin 1) := fun i => .rename (Equiv.swap i k) (.var 0)
  let base := unionTerm three (.var 0) ground
  let t := collect three Finset.univ.toList enabled piece base
  have formula : ∀ A i, i ∈ (t.eval (fun _ => A)).val ↔
      (i ∈ A.val ∨ i ≠ k) ∨ ∃ j, enabled j ∧ i ∈ (WinnerSet.rename (Equiv.swap j k) A).val := by
    intro A i
    simpa [t, base, piece, eval, hg, C] using
      mem_eval_collect three Finset.univ.toList enabled piece base (fun _ => A) i
  have at_k : ∀ A, k ∈ (t.eval (fun _ => A)).val ↔
      k ∈ A.val ∨ ∃ j, enabled j ∧ j ∈ A.val := by
    intro A
    have hs : ∀ j, k ∈ (WinnerSet.rename (Equiv.swap j k) A).val ↔ j ∈ A.val := by
      intro j
      change k ∈ (Equiv.swap j k) '' A.val ↔ j ∈ A.val
      constructor
      · rintro ⟨x, hx, he⟩
        have hxj : x = j := (Equiv.swap j k).injective
          (he.trans (Equiv.swap_apply_left j k).symm)
        exact hxj ▸ hx
      · intro hj
        exact ⟨j, hj, Equiv.swap_apply_left j k⟩
    simp only [formula, ne_eq, not_true_eq_false, or_false, hs]
  refine ⟨t, fun A i hi => (formula A i).mpr (Or.inl (Or.inl hi)), ?_,
    fun A i hi => (formula A i).mpr (Or.inl (Or.inr hi))⟩
  intro A
  rw [at_k]
  constructor
  · rintro (hk | ⟨j, hj, hmem⟩) hsub
    · rcases Set.mem_insert_iff.mp (hsub hk) with h | h
      · exact hak h.symm
      · exact hbk (Set.mem_singleton_iff.mp h).symm
    · rcases Set.mem_insert_iff.mp (hsub hmem) with h | h
      · exact hj.1 h
      · exact hj.2.1 (Set.mem_singleton_iff.mp h)
  · intro hn
    apply Classical.byContradiction
    intro hm
    apply hn
    intro i hi
    by_cases ha : i = a
    · exact Or.inl ha
    by_cases hb : i = b
    · exact Or.inr hb
    by_cases hk : i = k
    · exact False.elim (hm (Or.inl (hk ▸ hi)))
    · exact False.elim (hm (Or.inr ⟨i, ⟨ha, hb, hk⟩, hi⟩))

private theorem eq_pair_of_ambiguous_subset (A : WinnerSet Role) (a b : Role)
    (hA : ∀ r, A ≠ WinnerSet.singleton r) (hsub : A.val ⊆ {a, b}) : A.val = {a, b} := by
  have ha : a ∈ A.val := by
    apply Classical.byContradiction
    intro ha
    apply hA b
    apply WinnerSet.eq_singleton_of_subset
    intro x hx
    rcases Set.mem_insert_iff.mp (hsub hx) with h | h
    · exact False.elim (ha (h ▸ hx))
    · exact h
  have hb : b ∈ A.val := by
    apply Classical.byContradiction
    intro hb
    apply hA a
    apply WinnerSet.eq_singleton_of_subset
    intro x hx
    rcases Set.mem_insert_iff.mp (hsub hx) with h | h
    · exact h
    · exact False.elim (hb (Set.mem_singleton_iff.mp h ▸ hx))
  exact Set.Subset.antisymm hsub (Set.pair_subset_iff.mpr ⟨ha, hb⟩)

/-- A unary full-language equation isolates each particular two-element input.
Both terms are assembled from the existing primitive constructors. -/
theorem exists_pair_separator [Fintype Role] (three : Fin 3 ↪ Role)
    (a b : Role) (hab : a ≠ b) :
    ∃ s t : Term Role (Fin 1),
      (∀ A : WinnerSet Role, A.val ≠ {a, b} →
        s.eval (fun _ => A) = t.eval (fun _ => A)) ∧
      s.eval (fun _ => WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)) ≠
        t.eval (fun _ => WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)) := by
  classical
  obtain ⟨k, hka, hkb⟩ := exists_role_outside_pair three a b
  obtain ⟨f, hfsub, hfk, hfother⟩ := exists_pair_expander three a b k hka.symm hkb.symm
  let top : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  obtain ⟨ground, hg⟩ := exists_constant (Var := Fin 1) three top
  let roles : List Role := Finset.univ.toList
  let p := suppress roles (unionTerm three (.var 0) f) (.var 0)
  let q := suppress roles (unionTerm three (.var 0) ground) (.var 0)
  have hp_atom : ∀ r, p.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r := by
    intro r
    exact eval_suppress_atom roles _ _ _ r (by simp [roles]) rfl
  have hq_atom : ∀ r, q.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r := by
    intro r
    exact eval_suppress_atom roles _ _ _ r (by simp [roles]) rfl
  have hp_amb : ∀ A : WinnerSet Role, (∀ r, A ≠ WinnerSet.singleton r) →
      p.eval (fun _ => A) = f.eval (fun _ => A) := by
    intro A hA
    have hs := eval_suppress_ambiguous roles (unionTerm three (.var 0) f) (.var 0)
      (fun _ => A) hA (by simp only [eval_unionTerm, eval]; exact Set.subset_union_left)
    change p.eval (fun _ => A) = _ at hs
    rw [hs, eval_unionTerm]
    apply Subtype.ext
    exact Set.union_eq_right.mpr (hfsub A)
  have hq_amb : ∀ A : WinnerSet Role, (∀ r, A ≠ WinnerSet.singleton r) →
      q.eval (fun _ => A) = top := by
    intro A hA
    have hs := eval_suppress_ambiguous roles (unionTerm three (.var 0) ground) (.var 0)
      (fun _ => A) hA (by simp only [eval_unionTerm, eval]; exact Set.subset_union_left)
    change q.eval (fun _ => A) = _ at hs
    rw [hs, eval_unionTerm, hg]
    apply Subtype.ext
    exact Set.union_univ _
  refine ⟨p, q, ?_, ?_⟩
  · intro A hne
    by_cases h : ∃ r, A = WinnerSet.singleton r
    · obtain ⟨r, rfl⟩ := h
      rw [hp_atom, hq_atom]
    · have hA : ∀ r, A ≠ WinnerSet.singleton r := fun r he => h ⟨r, he⟩
      have hnsub : ¬ A.val ⊆ {a, b} := fun hs => hne (eq_pair_of_ambiguous_subset A a b hA hs)
      rw [hp_amb A hA, hq_amb A hA]
      apply Subtype.ext
      apply Set.eq_univ_of_forall
      intro i
      by_cases hi : i = k
      · subst i; exact (hfk A).mpr hnsub
      · exact hfother A i hi
  · let A := WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)
    have hA : ∀ r, A ≠ WinnerSet.singleton r := by
      intro r he
      have hs : A.val = {r} := congrArg Subtype.val he
      have ha : a ∈ A.val := Or.inl rfl
      have hb : b ∈ A.val := Or.inr rfl
      have har : a = r := by simpa [hs] using ha
      have hbr : b = r := by simpa [hs] using hb
      exact hab (har.trans hbr.symm)
    intro he
    have hk : k ∈ (p.eval (fun _ => A)).val := by rw [he, hq_amb A hA]; trivial
    rw [hp_amb A hA] at hk
    exact (hfk A).mp hk (by intro i hi; exact hi)

end Term

variable {Role : Type u}

theorem completeTestDomain_iff [Fintype Role] (three : Fin 3 ↪ Role)
    (D : Set (WinnerSet Role)) :
    CompleteTestDomain D ↔ ∀ a b,
      WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b) ∈ D := by
  classical
  constructor
  · intro hc
    have unary (s t : Term Role (Fin 1))
        (he : ∀ A, A ∈ D → s.eval (fun _ => A) = t.eval (fun _ => A)) :
        ∀ A, s.eval (fun _ => A) = t.eval (fun _ => A) := by
      intro A
      apply hc 1 s t ?_ (fun _ => A)
      intro v hv
      have hconst : v = fun _ : Fin 1 => v 0 := by funext x; exact congrArg v (Subsingleton.elim _ _)
      rw [hconst]
      exact he (v 0) (hv 0)
    have atoms : ∀ a, WinnerSet.singleton a ∈ D := by
      intro a
      obtain ⟨k, hka, _⟩ := exists_role_outside_pair three a a
      obtain ⟨s, t, he, hne⟩ := Term.exists_singleton_separator three a k hka.symm
      apply Classical.byContradiction
      intro hn
      exact hne (unary s t (fun A hD => he A (fun heq => hn (heq ▸ hD))) _)
    intro a b
    by_cases hab : a = b
    · subst b; simpa using atoms a
    · obtain ⟨s, t, he, hne⟩ := Term.exists_pair_separator three a b hab
      apply Classical.byContradiction
      intro hn
      apply hne
      apply unary s t
      intro A hD
      apply he A
      intro heq
      have hA : A = WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b) :=
        Subtype.ext heq
      exact hn (hA ▸ hD)
  · intro hd n s t he v
    apply Classical.byContradiction
    intro hne
    obtain ⟨w, hw, hwne⟩ := s.exists_pair_countervaluation t ⟨v, hne⟩
    apply hwne
    apply he w
    intro x
    obtain ⟨a, b, hab⟩ := hw x
    have hval : w x = WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b) :=
      Subtype.ext hab
    rw [hval]
    exact hd a b

/-- Singleton-or-pair values form the least complete fixed input domain. -/
theorem isLeast_completeTestDomain [Fintype Role] (three : Fin 3 ↪ Role) :
    IsLeast {D : Set (WinnerSet Role) | CompleteTestDomain D}
      {A | ∃ a b, A.val = {a, b}} := by
  constructor
  · apply (completeTestDomain_iff three _).mpr
    intro a b
    exact ⟨a, b, rfl⟩
  · intro D hD A hA
    obtain ⟨a, b, hab⟩ := hA
    have heq : A = WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b) :=
      Subtype.ext hab
    rw [heq]
    exact (completeTestDomain_iff three D).mp hD a b

end KFOL
