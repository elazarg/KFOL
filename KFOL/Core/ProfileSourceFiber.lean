module

public import KFOL.Core.SourceNormalForm
public import KFOL.Algebra.SemilatticeTrace
public import KFOL.Core.ProfileBounds
public import KFOL.Equational.Native
public import KFOL.Reset.Public

/-! # A single source in a fixed singleton-profile class

Substitution at the distinguished input intersects its two source
coefficients. When both words have the same singleton profiles, substitution
preserves those profiles. -/

@[expose] public section

namespace KFOL.Core.ProfileSourceFiber

open Sources
open scoped Classical

universe u v
variable {Role : Type u} {Var : Type v}

/-- All singleton outputs agree, on every valuation and for every owner. -/
def SameProfiles (s t : Term Role Var) : Prop :=
  ∀ v r, s.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r

/-- Replace every occurrence of the chosen input of the outer word by the inner word. -/
noncomputable def substituteAt (s : Term Role Var) (j : Var) (t : Term Role Var) : Term Role Var :=
  s.subst (fun i => if i = j then t else .var i)

theorem substituteAt_isCore {s t : Term Role Var} (hs : s.IsCore) (ht : t.IsCore) (j : Var) :
    (substituteAt s j t).IsCore :=
  hs.subst _ (fun i _ => by split <;> first | exact ht | trivial)

private theorem eval_substituteAt (s t : Term Role Var) (j : Var) (v : Var → WinnerSet Role) :
    (substituteAt s j t).eval v = s.eval (Function.update v j (t.eval v)) := by
  rw [substituteAt, Term.eval_subst]
  congr 1
  funext i
  by_cases hi : i = j <;> simp [hi, Term.eval, Function.update]

/-- At the substituted input a canonical source probe survives precisely when
both words transmit it. The remaining source coefficients are unrestricted. -/
theorem substituteAt_probe (three : Fin 3 ↪ Role) {s : Term Role Var}
    (hs : s.IsCore) (t : Term Role Var) (k : Role) (j : Var) (p : Pattern k j) :
    k ∈ ((substituteAt s j t).eval (probe three k j p)).val ↔
      k ∈ (s.eval (probe three k j p)).val ∧ k ∈ (t.eval (probe three k j p)).val := by
  let v := probe three k j p
  let w := Function.update v j (t.eval v)
  rw [eval_substituteAt]
  change k ∈ (s.eval w).val ↔ _
  have pat : pattern k j w = p := by
    rw [← pattern_probe three k j p]
    funext i
    change passive k (w i.val) = passive k (v i.val)
    rw [show w i.val = v i.val from Function.update_of_ne i.property ..]
  rw [membership_iff_source three s hs w k]
  constructor
  · rintro ⟨i, hi, hsup⟩
    by_cases hij : i = j
    · subst i
      exact ⟨pat ▸ hsup, by simpa [w] using hi⟩
    · have hk : k ∈ (v i).val := by simpa [w, hij] using hi
      exact (hij ((mem_probe_iff three k j p i).mp hk)).elim
  · rintro ⟨hsup, hmem⟩
    exact ⟨j, by simpa [w] using hmem, by simpa only [pat] using hsup⟩

/-- Substituting one member of a singleton-profile class into another at one
input stays in that class. -/
theorem substituteAt_sameProfiles {s t : Term Role Var} (hs : s.IsCore)
    (same : SameProfiles s t) (j : Var) : SameProfiles (substituteAt s j t) s := by
  intro v r
  rw [eval_substituteAt]
  let active (i : Var) := decide (i = j)
  have fix (x : WinnerSet Role) :
      (fun i => if active i then x else v i) = Function.update v j x := by
    funext i
    by_cases hi : i = j <;> simp [active, Function.update, hi]
  rcases hs.isPublic.unary_constant_or_extensive active v with ⟨C, hC⟩ | extensive
  · have h := hC (v j)
    rw [fix, Function.update_eq_self] at h
    rw [← fix, hC, h]
  · constructor
    · intro ha
      have sub := extensive (t.eval v)
      rw [fix, ha] at sub
      exact (same v r).mpr (WinnerSet.eq_singleton_of_subset _ r sub)
    · intro ha
      have sub := extensive (v j)
      rw [fix, Function.update_eq_self, ha] at sub
      have eq := (same v r).mp ha
      rw [← WinnerSet.eq_singleton_of_subset _ r sub] at eq
      rwa [eq, Function.update_eq_self]

/-- An observer and an arbitrary coloring away from the chosen input. -/
abbrev Observation (Role : Type u) {Var : Type v} (j : Var) := Σ k : Role, Pattern k j

/-- The chosen source transmits the observer on this canonical probe. -/
def Supplies (three : Fin 3 ↪ Role) (t : Term Role Var) (j : Var) (q : Observation Role j) : Prop :=
  q.1 ∈ (t.eval (probe three q.1 j q.2)).val

/-- A full profile tuple is read from the singleton flags of each valuation. -/
def HasProfiles (Φ : Role → (Var → Bool) → Bool) (t : Term Role Var) : Prop :=
  ∀ v r, t.eval v = WinnerSet.singleton r ↔ Φ r (ProfileBounds.atomicBits r v) = true

private theorem hasProfiles_decode_iff [DecidableEq Role] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (e : Equational.Term (Equational.CoreSymbol Role) Var) :
    HasProfiles Φ (Equational.Core.decode e) ↔ ∀ r A, profile r A e = Φ r A := by
  let _ := Equational.coreStructure Role
  have readProfile (v : Var → WinnerSet Role) (r : Role) :
      (Equational.Core.decode e).eval v = WinnerSet.singleton r ↔
        profile r (ProfileBounds.atomicBits r v) e = true := by
    rw [Equational.Core.eval_decode]
    exact winnerSet_eq_singleton_iff_profile e r v
  constructor
  · intro h r A
    obtain ⟨s, hsr, _⟩ := exists_role_outside_pair three r r
    let v (i : Var) := WinnerSet.singleton (if A i then r else s)
    have bits : ProfileBounds.atomicBits r v = A := by
      funext i
      cases hA : A i <;> simp [ProfileBounds.atomicBits, v, hA, hsr]
    apply Bool.eq_iff_iff.mpr
    simpa only [bits] using (readProfile v r).symm.trans (h v r)
  · intro h v r
    simpa only [← h] using readProfile v r

/-- Failure of the one-bound test means the observer cannot be omitted. -/
def Forced [Fintype Role] (three : Fin 3 ↪ Role) (Φ : Role → (Var → Bool) → Bool)
    (j : Var) (q : Observation Role j) : Prop :=
  ¬ProfileBounds.ProfileCondition Φ (probe three q.1 j q.2) {r | r ≠ q.1}

/-- The profile does not force a competing singleton at the probe. -/
def Permitted (three : Fin 3 ↪ Role) (Φ : Role → (Var → Bool) → Bool)
    (j : Var) (q : Observation Role j) : Prop :=
  ∀ r, r ≠ q.1 → Φ r (ProfileBounds.atomicBits r (probe three q.1 j q.2)) = false

/-- In the coloring itself the head is unposted. Thus checking the competing
singleton profiles is equivalent to checking every owner's coalition there. -/
theorem permitted_iff_unposted_head (three : Fin 3 ↪ Role) (Φ : Role → (Var → Bool) → Bool)
    (admissible : AdmissibleProfiles Φ) (j : Var) (q : Observation Role j) :
    Permitted three Φ j q ↔ ∀ r,
      Φ r (Function.update (ProfileBounds.atomicBits r (probe three q.1 j q.2)) j false) = false := by
  classical
  let bits (r : Role) := ProfileBounds.atomicBits r (probe three q.1 j q.2)
  have foreign (r : Role) (hr : r ≠ q.1) : Function.update (bits r) j false = bits r := by
    have hj : bits r j = false := by simp [bits, ProfileBounds.atomicBits, Ne.symm hr]
    rw [← hj, Function.update_eq_self]
  have observer : Function.update (bits q.1) j false = fun _ => false := by
    funext i
    by_cases hi : i = j
    · simp [hi]
    · have ne : probe three q.1 j q.2 i ≠ WinnerSet.singleton q.1 := by
        intro he
        exact hi ((mem_probe_iff three q.1 j q.2 i).mp (he ▸ (Set.mem_singleton q.1)))
      rw [Function.update_of_ne hi]
      exact decide_eq_false ne
  constructor
  · intro h r
    change Φ r (Function.update (bits r) j false) = false
    by_cases hr : r = q.1
    · subst r
      rw [observer]
      cases hx : Φ q.1 (fun _ => false) with
      | false => rfl
      | true =>
        let A (r : Role) (_ : Var) := decide (r ≠ q.1)
        obtain ⟨i, hi⟩ := admissible.common_source A fun r => by
          by_cases he : r = q.1
          · simpa [A, he] using hx
          · simpa [A, he] using admissible.top r
        simpa [A] using hi q.1
    · rw [foreign r hr]
      exact h r hr
  · intro h r hr
    have hv : Φ r (Function.update (bits r) j false) = false := h r
    rwa [foreign r hr] at hv

theorem not_forced_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (j : Var) (q : Observation Role j) :
    ¬Forced three Φ j q ↔ ∃ t : Term Role Var, t.IsCore ∧ HasProfiles Φ t ∧ ¬Supplies three t j q := by
  classical
  let _ := Equational.coreStructure Role
  rw [Forced, not_not, ProfileBounds.profileCondition_iff three]
  constructor
  · rintro ⟨e, hφ, hb⟩
    refine ⟨Equational.Core.decode e, Equational.Core.isCore_decode e,
      (hasProfiles_decode_iff three Φ e).mpr hφ, ?_⟩
    intro hk
    rw [Supplies, Equational.Core.eval_decode] at hk
    exact hb hk rfl
  · rintro ⟨t, ht, hφ, miss⟩
    let e := Equational.Core.encode t ht
    have he : Equational.Core.decode e = t := Equational.Core.decode_encode t ht
    refine ⟨e, (hasProfiles_decode_iff three Φ e).mp (he ▸ hφ), ?_⟩
    rw [← Equational.Core.eval_decode, he]
    rintro k hk rfl
    exact miss hk

private theorem meet_omissions (three : Fin 3 ↪ Role) (Φ : Role → (Var → Bool) → Bool)
    (base : Term Role Var) (hc : base.IsCore) (hΦ : HasProfiles Φ base)
    (j : Var) (Z : Finset (Observation Role j))
    (individual : ∀ q ∈ Z, ∃ t : Term Role Var, t.IsCore ∧ HasProfiles Φ t ∧ ¬Supplies three t j q) :
    ∃ t : Term Role Var, t.IsCore ∧ HasProfiles Φ t ∧ ∀ q ∈ Z, ¬Supplies three t j q := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨base, hc, hΦ, by simp⟩
  | insert q Z _ ih =>
    obtain ⟨s, hs, hsp, old⟩ := ih (fun p hp => individual p (Finset.mem_insert_of_mem hp))
    obtain ⟨t, ht, htp, new⟩ := individual q (Finset.mem_insert_self ..)
    have same : SameProfiles s t := fun v r => (hsp v r).trans (htp v r).symm
    refine ⟨substituteAt s j t, substituteAt_isCore hs ht j,
      fun v r => (substituteAt_sameProfiles hs same j v r).trans (hsp v r), ?_⟩
    rintro ⟨k,p⟩ hmem hit
    have hh := (substituteAt_probe three hs t k j p).mp hit
    rcases Finset.mem_insert.mp hmem with rfl | hold
    · exact new hh.2
    · exact old _ hold hh.1

/-- One actual term with the prescribed entire profile tuple misses every mark
at this input that can be omitted separately. Its coefficient is computed by
the one-bound tests. -/
theorem exists_least [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (admissible : AdmissibleProfiles Φ) (j : Var) :
    ∃ t : Term Role Var, t.IsCore ∧ HasProfiles Φ t ∧
      ∀ q, Supplies three t j q ↔ Forced three Φ j q := by
  classical
  obtain ⟨e, he⟩ := (exists_term_iff_admissibleProfiles three Φ).mpr admissible
  let Z := Finset.univ.filter fun q : Observation Role j => ¬Forced three Φ j q
  have memZ (q : Observation Role j) : q ∈ Z ↔ ¬Forced three Φ j q := by simp [Z]
  obtain ⟨t, ht, hφ, misses⟩ := meet_omissions three Φ (Equational.Core.decode e)
    (Equational.Core.isCore_decode e) ((hasProfiles_decode_iff three Φ e).mpr he) j Z
    (fun q hq => (not_forced_iff three Φ j q).mp ((memZ q).mp hq))
  refine ⟨t, ht, hφ, fun q => ?_⟩
  constructor
  · intro h
    by_contra hn
    exact misses q ((memZ q).mpr hn) h
  · intro h
    by_contra hn
    exact (not_forced_iff three Φ j q).mpr ⟨t, ht, hφ, hn⟩ h

private theorem permitted_of_supplies {three : Fin 3 ↪ Role} {Φ : Role → (Var → Bool) → Bool}
    {j : Var} {q : Observation Role j} {t : Term Role Var} (hφ : HasProfiles Φ t)
    (hit : Supplies three t j q) : Permitted three Φ j q := by
  intro r hne
  cases bit : Φ r (ProfileBounds.atomicBits r (probe three q.1 j q.2)) with
  | false => rfl
  | true =>
    have h := (hφ _ r).mpr bit
    rw [Supplies, h] at hit
    exact (hne hit.symm).elim

/-- Resetting an arbitrary core word against the least member of the fiber
clips its distinguished source coefficient to the two profile bounds. -/
theorem exists_clipped [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (admissible : AdmissibleProfiles Φ) (j : Var)
    (t : Term Role Var) (ht : t.IsCore) :
    ∃ s : Term Role Var, s.IsCore ∧ HasProfiles Φ s ∧ ∀ q,
      Supplies three s j q ↔ Forced three Φ j q ∨ (Supplies three t j q ∧ Permitted three Φ j q) := by
  classical
  obtain ⟨l, hl, hlφ, least⟩ := exists_least three Φ admissible j
  let s := Reset.Term.resetTerm three Finset.univ.toList t l
  have eval (v : Var → WinnerSet Role) : s.eval v = (t.eval v).reset (l.eval v) :=
    Reset.Term.eval_resetTerm three Finset.univ.toList (by simp) t l v
  have hsφ : HasProfiles Φ s := fun v r =>
    (eval v ▸ WinnerSet.reset_eq_singleton (t.eval v) (l.eval v) r).trans (hlφ v r)
  refine ⟨s, Reset.Term.isCore_resetTerm three _ _ _ ht hl, hsφ, fun q => ?_⟩
  let v := probe three q.1 j q.2
  have mem : Supplies three s j q ↔ Supplies three l j q ∨
      ((l.eval v).Ambiguous ∧ Supplies three t j q) := by
    simp only [Supplies, eval, WinnerSet.mem_reset, v]
  constructor
  · intro h
    rcases mem.mp h with forced | ⟨_, raw⟩
    · exact Or.inl ((least q).mp forced)
    · exact Or.inr ⟨raw, permitted_of_supplies hsφ h⟩
  · rintro (forced | ⟨raw, permitted⟩)
    · exact mem.mpr (Or.inl ((least q).mpr forced))
    · by_cases amb : (l.eval v).Ambiguous
      · exact mem.mpr (Or.inr ⟨amb, raw⟩)
      · obtain ⟨r, hr⟩ : ∃ r, l.eval v = WinnerSet.singleton r := by
          simpa only [WinnerSet.Ambiguous, not_forall, not_not] using amb
        have eq : r = q.1 := by
          by_contra hne
          have yes := (hlφ v r).mp hr
          exact Bool.noConfusion (yes.symm.trans (permitted r hne))
        apply mem.mpr
        left
        change q.1 ∈ (l.eval v).val
        rw [hr, eq]
        exact rfl

/-- Among independently realizable one-head predicates, imposing a full
profile tuple gives exactly the interval between the explicit omission and
competing-singleton bounds. -/
theorem exists_iff_between [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (admissible : AdmissibleProfiles Φ) (j : Var)
    (P : Observation Role j → Prop) :
    (∃ s : Term Role Var, s.IsCore ∧ HasProfiles Φ s ∧ ∀ q, Supplies three s j q ↔ P q) ↔
      (∃ t : Term Role Var, t.IsCore ∧ ∀ q, Supplies three t j q ↔ P q) ∧
      (∀ q, Forced three Φ j q → P q) ∧ (∀ q, P q → Permitted three Φ j q) := by
  constructor
  · rintro ⟨s, hs, hφ, hP⟩
    refine ⟨⟨s, hs, hP⟩, ?_, fun q h => permitted_of_supplies hφ ((hP q).mpr h)⟩
    intro q forced
    by_contra hn
    exact (not_forced_iff three Φ j q).mpr ⟨s, hs, hφ, fun hit => hn ((hP q).mp hit)⟩ forced
  · rintro ⟨⟨t, ht, raw⟩, lower, upper⟩
    obtain ⟨s, hs, hφ, clipped⟩ := exists_clipped three Φ admissible j t ht
    refine ⟨s, hs, hφ, fun q => (clipped q).trans ?_⟩
    exact ⟨fun h => h.elim (lower q) (fun hit => (raw q).mp hit.1),
      fun hit => Or.inr ⟨(raw q).mpr hit, upper q hit⟩⟩

end KFOL.Core.ProfileSourceFiber
