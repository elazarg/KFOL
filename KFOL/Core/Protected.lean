module

public import KFOL.Core.ModelLaws
public import KFOL.Core.Profiles

/-! # Protected upper markers selected by Boolean profiles -/

@[expose] public section

namespace KFOL.Core

universe u v

variable {Role : Type u} [DecidableEq Role] {Var : Type v}

attribute [local instance] Native.structureOf

theorem profile_false (i : Role) (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i (fun _ => false) t = false := by
  induction t using induction_choice with
  | var => rfl
  | choice r s t hs ht => simp only [profile_choice, hs, ht]; split <;> rfl

theorem no_atom_of_valuation (i : Role) (v : Var → Native Role)
    (hv : ∀ x, v x ≠ Native.atom i) (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    t.realize v ≠ Native.atom i := by
  intro he
  have hp := (realize_eq_atom_iff_profile t i v).mp he
  have heq : (fun x => decide (v x = Native.atom i)) = fun _ => false := by
    funext x
    exact decide_eq_false (hv x)
  rw [heq, profile_false] at hp
  cases hp

theorem profile_common_source_two (a b : Role) (hab : a ≠ b) (E F : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (ha : profile a E t = true) (hb : profile b F t = true) :
    ∃ x, E x = true ∧ F x = true := by
  let owners : Bool → Role := fun i => bif i then a else b
  let values : Bool → Var → Bool := fun i => bif i then E else F
  have hi : Function.Injective owners := by
    intro i j he
    cases i <;> cases j <;> simp_all [owners]
  have hp : ∀ i, profile (owners i) (values i) t = true := by
    intro i
    cases i
    · exact hb
    · exact ha
  obtain ⟨x, hx⟩ := profile_common_source owners hi values t hp
  exact ⟨x, hx true, hx false⟩

theorem profile_common_source_three (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (E F G : Var → Bool) (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (ha : profile a E t = true) (hb : profile b F t = true) (hc : profile c G t = true) :
    ∃ x, E x = true ∧ F x = true ∧ G x = true := by
  let owners : Fin 3 → Role := ![a, b, c]
  let values : Fin 3 → Var → Bool := ![E, F, G]
  have hi : Function.Injective owners := by
    intro i j he
    have hic : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hic with rfl | rfl | rfl <;> rcases hjc with rfl | rfl | rfl
    all_goals simp_all [owners]
  have hp : ∀ i, profile (owners i) (values i) t = true := by
    intro i
    have hic : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hic with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  obtain ⟨x, hx⟩ := profile_common_source owners hi values t hp
  exact ⟨x, hx 0, hx 1, hx 2⟩

/-- A positive profile prevents a different owner's atom whenever that
owner's atomic inputs avoid all positive input positions. -/
theorem no_atom_of_positive_profile (a b : Role) (hab : a ≠ b) (E : Var → Bool)
    (v : Var → Native Role) (avoid : ∀ x, E x = true → v x ≠ Native.atom b)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (ht : profile a E t = true) :
    t.realize v ≠ Native.atom b := by
  intro he
  have hb := (realize_eq_atom_iff_profile t b v).mp he
  obtain ⟨x, hx, hv⟩ := profile_common_source_two a b hab E _ t ht hb
  exact avoid x hx (of_decide_eq_true hv)

/-- The single-profile protected-path argument. A marker is placed at each
candidate leaf in its associated row; other atoms avoid the positive set,
and the tracked owner atom is absent from that row altogether. -/
theorem marker_of_positive_profile (a : Role) (E : Var → Bool)
    (v : Var → Var → Native Role)
    (marker : ∀ x, E x = true → v x x = Native.upper)
    (absent : ∀ x, E x = true → ∀ z, v x z ≠ Native.atom a)
    (avoid : ∀ x, E x = true → ∀ z, E z = true → ∀ b, v x z ≠ Native.atom b)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (ht : profile a E t = true) :
    ∃ x, E x = true ∧ t.realize (v x) = Native.upper := by
  induction t using induction_choice with
  | var x => exact ⟨x, ht, marker x ht⟩
  | choice r s t hs ht' =>
    by_cases hra : r = a
    · subst r
      have h : profile a E s = true ∨ profile a E t = true := by
        simpa only [profile_choice, ite_true, Bool.or_eq_true] using ht
      rcases h with h | h
      · obtain ⟨x, hx, hp⟩ := hs h
        refine ⟨x, hx, ?_⟩
        change Native.choice a (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
          no_atom_of_valuation a (v x) (absent x hx) t⟩
      · obtain ⟨x, hx, hp⟩ := ht' h
        refine ⟨x, hx, ?_⟩
        change Native.choice a (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inr hp,
          no_atom_of_valuation a (v x) (absent x hx) s, by rw [hp]; simp⟩
    · have h : profile a E s = true ∧ profile a E t = true := by
        simpa only [profile_choice, ite_eq_right hra, Bool.and_eq_true] using ht
      obtain ⟨x, hx, hp⟩ := hs h.1
      refine ⟨x, hx, ?_⟩
      change Native.choice r (s.realize (v x)) (t.realize (v x)) = Native.upper
      exact (Native.choice_eq_upper r _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
        no_atom_of_positive_profile a r (Ne.symm hra) E (v x) (fun z hz => avoid x hx z hz r) t h.2⟩

/-- A row separating two profiles of one role protects a marker: the
tracked role's atomic inputs are exactly F, and all other atoms avoid E. -/
theorem marker_of_profile_difference (a : Role) (E F : Var → Bool)
    (v : Var → Var → Native Role)
    (marker : ∀ x, E x = true → v x x = Native.upper)
    (atomic : ∀ x, E x = true → ∀ z, v x z = Native.atom a ↔ F z = true)
    (avoid : ∀ x, E x = true → ∀ b, b ≠ a → ∀ z, E z = true → v x z ≠ Native.atom b)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hE : profile a E t = true) (hF : profile a F t = false) :
    ∃ x, E x = true ∧ t.realize (v x) = Native.upper := by
  have noAtom (x : Var) (hx : E x = true)
      (t : Equational.Term (Equational.CoreSymbol Role) Var) (ht : profile a F t = false) :
      t.realize (v x) ≠ Native.atom a := by
    intro he
    have hp := (realize_eq_atom_iff_profile t a (v x)).mp he
    have heq : (fun z => decide (v x z = Native.atom a)) = F := by
      funext z
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using atomic x hx z
    rw [heq, ht] at hp
    cases hp
  induction t using induction_choice with
  | var x => exact ⟨x, hE, marker x hE⟩
  | choice r s t hs ht =>
    by_cases hra : r = a
    · subst r
      have he : profile a E s = true ∨ profile a E t = true := by
        simpa only [profile_choice, ite_true, Bool.or_eq_true] using hE
      have hf : profile a F s = false ∧ profile a F t = false := by
        simpa only [profile_choice, ite_true, Bool.or_eq_false_iff] using hF
      rcases he with he | he
      · obtain ⟨x, hx, hp⟩ := hs he hf.1
        refine ⟨x, hx, ?_⟩
        change Native.choice a (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inl hp, by rw [hp]; simp, noAtom x hx t hf.2⟩
      · obtain ⟨x, hx, hp⟩ := ht he hf.2
        refine ⟨x, hx, ?_⟩
        change Native.choice a (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inr hp, noAtom x hx s hf.1, by rw [hp]; simp⟩
    · have he : profile a E s = true ∧ profile a E t = true := by
        simpa only [profile_choice, ite_eq_right hra, Bool.and_eq_true] using hE
      have hf : profile a F s = false ∨ profile a F t = false := by
        simpa only [profile_choice, ite_eq_right hra, Bool.and_eq_false_iff] using hF
      rcases hf with hf | hf
      · obtain ⟨x, hx, hp⟩ := hs he.1 hf
        refine ⟨x, hx, ?_⟩
        change Native.choice r (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper r _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
          no_atom_of_positive_profile a r (Ne.symm hra) E (v x)
            (fun z hz => avoid x hx r hra z hz) t he.2⟩
      · obtain ⟨x, hx, hp⟩ := ht he.2 hf
        refine ⟨x, hx, ?_⟩
        change Native.choice r (s.realize (v x)) (t.realize (v x)) = Native.upper
        exact (Native.choice_eq_upper r _ _).mpr ⟨Or.inr hp,
          no_atom_of_positive_profile a r (Ne.symm hra) E (v x)
            (fun z hz => avoid x hx r hra z hz) s he.1, by rw [hp]; simp⟩

/-- Two positive profiles exclude a third atom when its atomic input
positions avoid their intersection. -/
theorem no_atom_of_two_positive_profiles (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (E F : Var → Bool)
    (v : Var → Native Role) (avoid : ∀ x, E x = true → F x = true → v x ≠ Native.atom c)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hE : profile a E t = true) (hF : profile b F t = true) :
    t.realize v ≠ Native.atom c := by
  intro he
  have hc := (realize_eq_atom_iff_profile t c v).mp he
  obtain ⟨x, hx, hy, hz⟩ := profile_common_source_three a b c hab hac hbc E F _ t hE hF hc
  exact avoid x hx hy (of_decide_eq_true hz)

/-- The annotation-row protected-path argument. The only common positive
inputs carry the upper marker; neither tracked role atom occurs in the row,
and other atoms avoid that intersection. -/
theorem marker_of_two_profiles (a b : Role) (hab : a ≠ b) (E F : Var → Bool)
    (v : Var → Native Role)
    (marker : ∀ x, E x = true → F x = true → v x = Native.upper)
    (absentA : ∀ x, v x ≠ Native.atom a) (absentB : ∀ x, v x ≠ Native.atom b)
    (avoid : ∀ c, c ≠ a → c ≠ b → ∀ x, E x = true → F x = true → v x ≠ Native.atom c)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hE : profile a E t = true) (hF : profile b F t = true) :
    t.realize v = Native.upper := by
  induction t using induction_choice with
  | var x => exact marker x hE hF
  | choice r s t hs ht =>
    change Native.choice r (s.realize v) (t.realize v) = Native.upper
    by_cases hra : r = a
    · subst r
      have he : profile a E s = true ∨ profile a E t = true := by
        simpa only [profile_choice, ite_true, Bool.or_eq_true] using hE
      have hf : profile b F s = true ∧ profile b F t = true := by
        simpa only [profile_choice, ite_eq_right hab, Bool.and_eq_true] using hF
      rcases he with he | he
      · have hp := hs he hf.1
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
          no_atom_of_valuation a v absentA t⟩
      · have hp := ht he hf.2
        exact (Native.choice_eq_upper a _ _).mpr ⟨Or.inr hp,
          no_atom_of_valuation a v absentA s, by rw [hp]; simp⟩
    · by_cases hrb : r = b
      · subst r
        have he : profile a E s = true ∧ profile a E t = true := by
          simpa only [profile_choice, ite_eq_right hra, Bool.and_eq_true] using hE
        have hf : profile b F s = true ∨ profile b F t = true := by
          simpa only [profile_choice, ite_true, Bool.or_eq_true] using hF
        rcases hf with hf | hf
        · have hp := hs he.1 hf
          exact (Native.choice_eq_upper b _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
            no_atom_of_valuation b v absentB t⟩
        · have hp := ht he.2 hf
          exact (Native.choice_eq_upper b _ _).mpr ⟨Or.inr hp,
            no_atom_of_valuation b v absentB s, by rw [hp]; simp⟩
      · have he : profile a E s = true ∧ profile a E t = true := by
          simpa only [profile_choice, ite_eq_right hra, Bool.and_eq_true] using hE
        have hf : profile b F s = true ∧ profile b F t = true := by
          simpa only [profile_choice, ite_eq_right hrb, Bool.and_eq_true] using hF
        have hp := hs he.1 hf.1
        exact (Native.choice_eq_upper r _ _).mpr ⟨Or.inl hp, by rw [hp]; simp,
          no_atom_of_two_positive_profiles a b r hab (Ne.symm hra) (Ne.symm hrb)
            E F v (avoid r hra hrb) t he.2 hf.2⟩

end KFOL.Core
