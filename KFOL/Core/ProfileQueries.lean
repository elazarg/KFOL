module

public import KFOL.Core.ProfileBounds
public import KFOL.Core.WholeInputs

/-! # Direct one-budget rainbow queries

A winner can be retained while all rainbow profile demands are installed
exactly when the direct source and foreign-owner tests hold.
-/

@[expose] public section
namespace KFOL.Core.ProfileBounds
universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

omit [DecidableEq Role] in
private theorem choice_bound (r : Role)
    (x y : Equational.Term (Equational.CoreSymbol Role) Var)
    (values : Var → WinnerSet Role) (U : Set Role)
    (hx : (x.realize values).val ⊆ U) (hy : (y.realize values).val ⊆ U) :
    ((choiceTerm r x y).realize values).val ⊆ U :=
  (WinnerSet.choice_subset_union r _ _).trans (Set.union_subset hx hy)

private theorem repair_pair (J : Finset Role) (A : Role → Var → Bool)
    (r : Role) (hr : r ∈ J) (B : Var → Bool) (values : Var → WinnerSet Role) (U : Set Role)
    (u : Equational.Term (Equational.CoreSymbol Role) Var)
    (hu : ∀ q ∈ J, profile q (A q) u = true) (hub : (u.realize values).val ⊆ U)
    (v : Equational.Term (Equational.CoreSymbol Role) Var)
    (hva : profile r (A r) v = true) (hvb : profile r B v = false)
    (hvbound : (v.realize values).val ⊆ U) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ q ∈ J, profile q (A q) t = true) ∧
      profile r (A r) t = true ∧ profile r B t = false ∧ (t.realize values).val ⊆ U := by
  classical
  have build (K : Finset Role) (hK : K ⊆ J) :
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ q ∈ K, profile q (A q) t = true) ∧
        profile r (A r) t = true ∧ profile r B t = false ∧ (t.realize values).val ⊆ U := by
    induction K using Finset.induction_on with
    | empty => exact ⟨v,by simp,hva,hvb,hvbound⟩
    | @insert q K hq ih =>
      obtain ⟨t,ht,hta,htb,htbound⟩ := ih (fun s hs => hK (Finset.mem_insert_of_mem hs))
      by_cases hqr : q = r
      · subst q
        exact ⟨t,fun s hs => (Finset.mem_insert.mp hs).elim (fun h => h ▸ hta) (ht s),
          hta,htb,htbound⟩
      · refine ⟨choiceTerm q t u,?_,?_,?_,choice_bound q t u values U htbound hub⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with hsq | hsK
          · subst s
            simp [profile_choice,hu q (hK (Finset.mem_insert_self _ _))]
          · by_cases hqs : q = s
            · subst s
              simp [profile_choice,ht q hsK]
            · simp [profile_choice,hqs,ht s hsK,hu s (hK (Finset.mem_insert_of_mem hsK))]
        · simp [profile_choice,hqr,hta,hu r hr]
        · simp [profile_choice,hqr,htb]
  exact build J (fun _ h => h)

/-- A rainbow and one negative bit of a participating owner can be combined
under a single upper bound exactly when both separate tests are feasible. -/
theorem rainbow_pair_iff (J : Finset Role) (A : Role → Var → Bool)
    (r : Role) (hr : r ∈ J) (B : Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) :
    (RainbowSafe J A values U ∧ PairSafe r (A r) B values U) ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ q ∈ J, profile q (A q) t = true) ∧
        profile r B t = false ∧ (t.realize values).val ⊆ U := by
  constructor
  · rintro ⟨hR,hP⟩
    obtain ⟨u,hu,hub⟩ := (rainbowSafe_iff J A values U).mp hR
    obtain ⟨v,hva,hvb,hvbound⟩ := (pairSafe_iff r (A r) B values U).mp hP
    obtain ⟨t,ht,_,htb,htbound⟩ := repair_pair J A r hr B values U u hu hub v hva hvb hvbound
    exact ⟨t,ht,htb,htbound⟩
  · rintro ⟨t,ht,htb,htbound⟩
    exact ⟨(rainbowSafe_iff J A values U).mpr ⟨t,ht,htbound⟩,
      (pairSafe_iff r (A r) B values U).mpr ⟨t,ht r hr,htb,htbound⟩⟩

private theorem atomicBits_false_iff
    (r : Role) (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (values : Var → WinnerSet Role) :
    profile r (atomicBits r values) t = false ↔ t.realize values ≠ WinnerSet.singleton r := by
  classical
  have hh := winnerSet_eq_singleton_iff_profile t r values
  change profile r (fun j => decide (values j = WinnerSet.singleton r)) t = false ↔ _
  constructor
  · intro hf he
    have ht := hh.mp he
    rw [hf] at ht
    cases ht
  · intro hn
    cases hp : profile r (fun j => decide (values j = WinnerSet.singleton r)) t with
    | false => rfl
    | true => exact (hn (hh.mpr hp)).elim

/-- The direct query test exactly characterizes bounded rainbow feasibility
with one required winner at the same input. No finiteness or role-count
hypothesis is needed. -/
theorem querySafe_iff (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) (k : Role) :
    QuerySafe J A values U k ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r ∈ J, profile r (A r) t = true) ∧
        (t.realize values).val ⊆ U ∧ k ∈ (t.realize values).val := by
  classical
  constructor
  · rintro ⟨hR,⟨j,hjk,hjb⟩,hP⟩
    obtain ⟨u,hu,hub⟩ := (rainbowSafe_iff J A values U).mp hR
    have build (K : Finset Role) (hK : K ⊆ J) :
        ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
          (∀ r ∈ K, profile r (A r) t = true) ∧
          (t.realize values).val ⊆ U ∧ k ∈ (t.realize values).val := by
      induction K using Finset.induction_on with
      | empty => exact ⟨.var j,by simp,hjb,hjk⟩
      | @insert r K hr ih =>
        obtain ⟨t,ht,htb,htk⟩ := ih (fun s hs => hK (Finset.mem_insert_of_mem hs))
        have hrJ := hK (Finset.mem_insert_self r K)
        have side : ∃ h : Equational.Term (Equational.CoreSymbol Role) Var,
            (∀ s ∈ J, profile s (A s) h = true) ∧ (h.realize values).val ⊆ U ∧
            (r ≠ k → h.realize values ≠ WinnerSet.singleton r) := by
          by_cases hrk : r = k
          · exact ⟨u,hu,hub,fun hn => (hn hrk).elim⟩
          · obtain ⟨h,hh,hneg,hhb⟩ := (rainbow_pair_iff J A r hrJ
                (atomicBits r values) values U).mp ⟨hR,hP r hrJ hrk⟩
            exact ⟨h,hh,hhb,fun _ => (atomicBits_false_iff r h values).mp hneg⟩
        obtain ⟨h,hh,hhb,hhnot⟩ := side
        refine ⟨choiceTerm r t h,?_,choice_bound r t h values U htb hhb,?_⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with hsr | hsK
          · subst s
            simp [profile_choice,hh r hrJ]
          · by_cases hrs : r = s
            · subst s
              simp [profile_choice,ht r hsK]
            · simp [profile_choice,hrs,ht s hsK,hh s (hK (Finset.mem_insert_of_mem hsK))]
        · change k ∈ (WinnerSet.choice r (t.realize values) (h.realize values)).val
          by_cases habs : t.realize values = WinnerSet.singleton r ∨
              h.realize values = WinnerSet.singleton r
          · have hrk : r = k := by
              by_contra hn
              rcases habs with he | he
              · have : k = r := by simpa [he] using htk
                exact hn this.symm
              · exact hhnot hn he
            subst r
            simp [WinnerSet.choice,habs]
          · simp only [WinnerSet.choice,habs,ite_false]
            exact Or.inl htk
    exact build J (fun _ h => h)
  · rintro ⟨t,ht,htb,htk⟩
    refine ⟨(rainbowSafe_iff J A values U).mpr ⟨t,ht,htb⟩,
      whole_input_provenance_bounded t values U htb k htk,?_⟩
    intro r hr hrk
    apply (pairSafe_iff r (A r) (atomicBits r values) values U).mpr
    refine ⟨t,ht r hr,(atomicBits_false_iff r t values).mpr ?_,htb⟩
    intro he
    have : k = r := by simpa [he] using htk
    exact hrk this.symm

end KFOL.Core.ProfileBounds
