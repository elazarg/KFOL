module

public import KFOL.Core.SourceProbes
public import KFOL.Algebra.TestDomains
public import Mathlib.Order.Antichain
public import Mathlib.Data.Fintype.BigOperators

/-! # Canonical prime source-guard normal forms

Each coefficient is an upward-closed predicate on passive statuses. Its
canonical representation consists of all minimal sufficient exclusion guards.
Sourcewise linearity then reconstructs the whole winner-set operation.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

private theorem representative_mono (three : Fin 3 ↪ Role) (k : Role)
    {p q : Passive k} (h : p ≤ q) :
    (representative three k p).val ⊆ (representative three k q).val := by
  rcases h with hq | he
  · subst q
    cases p with
    | neutral => exact Set.Subset.rfl
    | atom r => exact Set.singleton_subset_iff.mpr r.property
  · rw [he]

/-- Erasing singleton tests enlarges a probe coordinatewise. -/
theorem probe_mono (three : Fin 3 ↪ Role) (k : Role) (j : Var)
    {p q : Pattern k j} (h : p ≤ q) :
    ∀ i, (probe three k j p i).val ⊆ (probe three k j q i).val := by
  classical
  intro i
  by_cases hi : i = j
  · subst i; simp
  · rw [probe_other three k j p i hi, probe_other three k j q i hi]
    exact representative_mono three k (h ⟨i, hi⟩)

/-- The isolated-source predicate is upward closed on the passive status poset. -/
theorem coefficient_mono (three : Fin 3 ↪ Role) (t : Term Role Var) (k : Role) (j : Var) :
    Monotone (fun p : Pattern k j => k ∈ (t.eval (probe three k j p)).val) :=
  fun _ _ h hp => t.eval_mono (probe_mono three k j h) hp

private noncomputable def pointGuard [Fintype Role] [Fintype Var]
    {k : Role} {j : Var} (p : Pattern k j) : Guard k j := by
  classical
  exact Finset.univ.filter (fun a => p a.1 ≠ .atom a.2)

private theorem pointGuard_enabled [Fintype Role] [Fintype Var]
    {k : Role} {j : Var} (p q : Pattern k j) : Enabled (pointGuard p) q ↔ p ≤ q := by
  classical
  constructor
  · intro h i
    change q i = .neutral ∨ p i = q i
    cases hqi : q i with
    | neutral => exact Or.inl rfl
    | atom r =>
      right
      by_contra hp
      exact h (i, r) (by simp [pointGuard, hp]) hqi
  · intro h a ha
    have hp : p a.1 ≠ .atom a.2 := (Finset.mem_filter.mp ha).2
    rcases h a.1 with hq | he
    · simp [hq]
    · exact he ▸ hp

/-- Prime exclusion boxes cover every upward-closed passive predicate. -/
theorem iff_enabled_prime [Fintype Role] [Fintype Var] {k : Role} {j : Var}
    (F : Pattern k j → Prop) (hF : Monotone F) (p : Pattern k j) :
    F p ↔ ∃ g : Guard k j, Prime F g ∧ Enabled g p := by
  classical
  constructor
  · intro hp
    have hs : Sound F (pointGuard p) :=
      fun q hq => hF ((pointGuard_enabled p q).mp hq) hp
    obtain ⟨g, hgp, hg⟩ := exists_minimal_le_of_wellFoundedLT (Sound F) (pointGuard p) hs
    refine ⟨g, hg, ?_⟩
    intro a ha
    exact (pointGuard_enabled p p).mpr le_rfl a (hgp ha)
  · rintro ⟨g, hg, hp⟩
    exact hg.prop p hp

@[simp] theorem mem_normalForm [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (k : Role) (j : Var) (g : Guard k j) :
    g ∈ normalForm three f k j ↔ Prime (fun p => k ∈ (f (probe three k j p)).val) g := by
  classical
  simp [normalForm]

/-- The canonical guards at each source form an antichain under inclusion. -/
theorem normalForm_antichain [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (k : Role) (j : Var) :
    IsAntichain (· ≤ ·) (normalForm three f k j : Set (Guard k j)) := by
  intro g hg h hh hne hgh
  have pg := (mem_normalForm three f k j g).mp hg
  have ph := (mem_normalForm three f k j h).mp hh
  exact hne (le_antisymm hgh (ph.2 pg.prop hgh))

/-- The prime guards describe exactly the isolated-source membership. -/
theorem coefficient_iff_guard [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (k : Role) (j : Var) (p : Pattern k j) :
    k ∈ (t.eval (probe three k j p)).val ↔
      ∃ g ∈ normalForm three (fun v => t.eval v) k j, Enabled g p := by
  rw [iff_enabled_prime _ (coefficient_mono three t k j)]
  simp only [mem_normalForm]

/-- The canonical source-guard family reconstructs the whole operation. -/
theorem normalForm_correct [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ht : t.IsCore) (v : Var → WinnerSet Role) :
    meaning (normalForm three (fun w => t.eval w)) v = (t.eval v).val := by
  ext k
  rw [membership_iff_source three t ht v k]
  change (∃ j, k ∈ (v j).val ∧ ∃ g ∈ normalForm three (fun w => t.eval w) k j,
    Enabled g (pattern k j v)) ↔ _
  exact exists_congr (fun j => and_congr_right (fun _ =>
    (coefficient_iff_guard three t k j (pattern k j v)).symm))

/-- Canonical prime source guards are a complete equality invariant. -/
theorem normalForm_eq_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (s t : Term Role Var) (hs : s.IsCore) (ht : t.IsCore) :
    normalForm three (fun v => s.eval v) = normalForm three (fun v => t.eval v) ↔
      ∀ v, s.eval v = t.eval v := by
  constructor
  · intro h v
    apply Subtype.ext
    rw [← normalForm_correct three s hs v, ← normalForm_correct three t ht v, h]
  · intro h
    exact congrArg (normalForm three) (funext h)

/-- Every individual exclusion box is the coefficient of a core term.
The construction is an owned-choice spine, with its source at the base. -/
theorem exists_guard_term (three : Fin 3 ↪ Role) {k : Role} {j : Var}
    (g : Guard k j) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ p : Pattern k j,
      (k ∈ (t.eval (probe three k j p)).val ↔ Enabled g p) := by
  classical
  induction g using Finset.induction_on with
  | empty => exact ⟨.var j, trivial, fun p => by simp [Term.eval, Enabled]⟩
  | @insert a g ha ih =>
    obtain ⟨t, ht, he⟩ := ih
    refine ⟨.choice a.2.val t (.var a.1.val), ⟨ht, trivial⟩, ?_⟩
    intro p
    rw [Term.eval, Term.eval, WinnerSet.mem_choice_other _ _ a.2.property]
    have hn : k ∉ (probe three k j p a.1.val).val := by
      simp [a.1.property]
    have hatom : probe three k j p a.1.val = WinnerSet.singleton a.2.val ↔
        p a.1 = .atom a.2 := by
      rw [probe_other three k j p a.1.val a.1.property]
      exact representative_atom_iff three k (p a.1) a.2
    constructor
    · rintro ⟨hm | hm, _, hnr⟩
      · have hg := (he p).mp hm
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact fun hb => hnr (hatom.mpr hb)
        · exact hg b hb
      · exact (hn hm).elim
    · intro hg
      have hm := (he p).mpr (fun b hb => hg b (Finset.mem_insert_of_mem hb))
      exact ⟨Or.inl hm,
        fun h => a.2.property (by
          have hk : k = a.2.val := by simpa only [h, WinnerSet.val_singleton,
            Set.mem_singleton_iff] using hm
          exact hk.symm),
        fun h => hg a (Finset.mem_insert_self _ _) (hatom.mp h)⟩

/-- Every nonempty guard family is realizable at one distinguished source.
This is a local synthesis theorem, with no prescription of the other coefficients. -/
theorem exists_guard_family_term (three : Fin 3 ↪ Role) {k : Role} {j : Var}
    (G : Finset (Guard k j)) (hG : G.Nonempty) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ p : Pattern k j,
      (k ∈ (t.eval (probe three k j p)).val ↔ ∃ g ∈ G, Enabled g p) := by
  classical
  induction hG using Finset.Nonempty.cons_induction with
  | singleton g =>
    obtain ⟨t, ht, he⟩ := exists_guard_term three g
    exact ⟨t, ht, fun p => by simpa using he p⟩
  | cons g G _ _ ih =>
    obtain ⟨s, hs, es⟩ := exists_guard_term three g
    obtain ⟨t, ht, et⟩ := ih
    refine ⟨Term.unionTerm three s t, ⟨⟨hs, ht⟩, ⟨hs, ht⟩⟩, ?_⟩
    intro p
    simp only [Term.eval_unionTerm, WinnerSet.val_union, Set.mem_union, es, et,
      Finset.mem_cons, exists_eq_or_imp]

/-- There are exactly K passive statuses: K−1 other atoms and neutral. -/
@[simp] theorem card_passive [Fintype Role] (k : Role) :
    Fintype.card (Passive k) = Fintype.card Role := by
  classical
  rw [Fintype.card_congr (Passive.equivOption k), Fintype.card_option,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have := Fintype.card_pos_iff.mpr (⟨k⟩ : Nonempty Role)
  omega

/-- The complete isolated-source test uses n Kⁿ Boolean observations. -/
theorem card_probeIndex [Fintype Role] [Fintype Var] [DecidableEq Var] :
    Fintype.card (ProbeIndex Role Var) =
      Fintype.card Var * Fintype.card Role ^ Fintype.card Var := by
  classical
  simp only [ProbeIndex, Pattern, Fintype.card_sigma, Fintype.card_fun,
    card_passive, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  by_cases hn : Fintype.card Var = 0
  · simp [hn]
  · have he : Fintype.card Var - 1 + 1 = Fintype.card Var := by omega
    conv_rhs => rw [← he, pow_succ]
    simp only [he]
    ac_rfl

/-- Constant true coefficients have exactly the empty prime guard. -/
theorem prime_true_iff {k : Role} {j : Var} (g : Guard k j) :
    Prime (fun _ : Pattern k j => True) g ↔ g = ∅ := by
  constructor
  · intro h
    exact Finset.eq_empty_iff_forall_notMem.mpr (fun _ ha =>
      Finset.notMem_empty _ (h.2 (fun _ _ => trivial) (Finset.empty_subset _) ha))
  · rintro rfl
    exact ⟨fun _ _ => trivial, fun _ _ _ => Finset.empty_subset _⟩

/-- A false coefficient has no sound guard, since neutral enables every guard. -/
theorem not_prime_false {k : Role} {j : Var} (g : Guard k j) :
    ¬Prime (fun _ : Pattern k j => False) g := by
  intro h
  exact h.prop (fun _ => .neutral) (fun _ _ => by simp)

/-- A projection has one empty guard at its own source and none elsewhere. -/
theorem normalForm_var [Fintype Role] [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (x : Var) (k : Role) (j : Var) :
    normalForm three (fun v => (Term.var x : Term Role Var).eval v) k j =
      if j = x then {∅} else ∅ := by
  classical
  ext g
  simp only [mem_normalForm, Term.eval, mem_probe_iff]
  by_cases h : j = x
  · subst j
    simp [prime_true_iff]
  · have hx : x ≠ j := Ne.symm h
    simp [hx, h, not_prime_false]

end KFOL.Core.Sources
