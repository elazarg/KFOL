module

public import KFOL.Core.CompletionDepth

/-! # Restricting a greatest completion to its live input ports

A fixed port contributes its owner's atom flag or no flag. A live port
reads its reindexed Boolean input at the owners enabled there. An owner
whose resulting profile loses even at the top receives unanimity.
-/

@[expose] public section
namespace KFOL.Core.CompletionDepth.Gate
universe u
variable {Role : Type u} [DecidableEq Role] {n m : ℕ}

/-- Lift a coalition of live inputs to the enabled ports and fixed flags. -/
def restrictedBits (port : Fin (n + 1) → Option (Fin (m + 1)))
    (dead : Fin (n + 1) → Option Role) (enabled : Role → Fin (n + 1) → Bool)
    (r : Role) (A : Fin (m + 1) → Bool) (j : Fin (n + 1)) : Bool :=
  match port j with
  | some i => enabled r j && A i
  | none => decide (dead j = some r)

/-- The masked profile, completed by unanimity when its top bit is false. -/
def restrictedProfiles (g : Gate Role n)
    (port : Fin (n + 1) → Option (Fin (m + 1)))
    (dead : Fin (n + 1) → Option Role) (enabled : Role → Fin (n + 1) → Bool)
    (r : Role) (A : Fin (m + 1) → Bool) : Bool :=
  if g.profiles r (restrictedBits port dead enabled r (fun _ => true)) then
    g.profiles r (restrictedBits port dead enabled r A)
  else decide (∀ i, A i = true)

/-- Excluding a singleton forced entirely by the fixed ports makes the
restricted profiles admissible. -/
theorem admissible_restrictedProfiles (g : Gate Role n)
    (port : Fin (n + 1) → Option (Fin (m + 1)))
    (dead : Fin (n + 1) → Option Role) (enabled : Role → Fin (n + 1) → Bool)
    (hdead : ∀ r, g.profiles r (restrictedBits port dead enabled r (fun _ => false)) = false) :
    AdmissibleProfiles (g.restrictedProfiles port dead enabled) := by
  let bits := restrictedBits port dead enabled
  let active (r : Role) := g.profiles r (bits r (fun _ => true)) = true
  have wins {r A} (h : g.restrictedProfiles port dead enabled r A = true) (ha : active r) :
      g.profiles r (bits r A) = true := by
    unfold restrictedProfiles at h
    rwa [ite_eq_left ha] at h
  have unanimous {r A} (h : g.restrictedProfiles port dead enabled r A = true) (ha : ¬active r) :
      ∀ i, A i = true := by
    unfold restrictedProfiles at h
    rwa [ite_eq_right ha, decide_eq_true_eq] at h
  constructor
  · intro r A B hAB hA
    by_cases ha : active r
    · unfold restrictedProfiles
      rw [ite_eq_left ha]
      apply g.admissible.mono r _ _ _ (wins hA ha)
      intro j hj
      cases h : port j with
      | none => simpa [bits, restrictedBits, h] using hj
      | some i =>
        simp only [bits, restrictedBits, h, Bool.and_eq_true] at hj ⊢
        exact ⟨hj.1, hAB i hj.2⟩
    · unfold restrictedProfiles
      rw [ite_eq_right ha, decide_eq_true_eq]
      exact fun i => hAB i (unanimous hA ha i)
  · intro r
    by_cases ha : active r
    · unfold restrictedProfiles
      rw [ite_eq_left ha]
      exact ha
    · unfold restrictedProfiles
      rw [ite_eq_right ha, decide_eq_true_eq]
      exact fun _ => rfl
  · classical
    intro A hA
    let B (r : Role) : Fin (n + 1) → Bool :=
      if active r then bits r (A r) else fun _ => true
    have hB (r : Role) : g.profiles r (B r) = true := by
      by_cases ha : active r
      · simpa [B, ha] using wins (hA r) ha
      · simpa [B, ha] using g.admissible.top r
    obtain ⟨j, hj⟩ := g.admissible.common_source B hB
    cases hport : port j with
    | some i =>
      refine ⟨i, fun r => ?_⟩
      by_cases ha : active r
      · have h := hj r
        simp only [B, ha, ite_true, bits, restrictedBits, hport, Bool.and_eq_true] at h
        exact h.2
      · exact unanimous (hA r) ha i
    | none =>
      have hlabel (r : Role) (ha : active r) : dead j = some r := by
        simpa only [B, ha, ite_true, bits, restrictedBits, hport, decide_eq_true_eq] using hj r
      by_cases hex : ∃ r, active r
      · obtain ⟨r, hr⟩ := hex
        have hnonempty : ∃ i, A r i = true := by
          by_contra! h
          have hempty : A r = fun _ => false := funext fun i => by simpa using h i
          have hw := wins (hA r) hr
          rw [hempty, hdead r] at hw
          contradiction
        obtain ⟨i, hi⟩ := hnonempty
        refine ⟨i, fun s => ?_⟩
        by_cases hs : active s
        · have heq : s = r := Option.some.inj ((hlabel s hs).symm.trans (hlabel r hr))
          exact heq ▸ hi
        · exact unanimous (hA s) hs i
      · exact ⟨0, fun r => unanimous (hA r) (fun ha => hex ⟨r, ha⟩) 0⟩

/-- A single greatest completion represents the restricted profiles at
the smaller arity, so restricting the ports adds no completion layer. -/
theorem exists_restriction [Fintype Role] (g : Gate Role n) (three : Fin 3 ↪ Role)
    (port : Fin (n + 1) → Option (Fin (m + 1)))
    (dead : Fin (n + 1) → Option Role) (enabled : Role → Fin (n + 1) → Bool)
    (hdead : ∀ r, g.profiles r (restrictedBits port dead enabled r (fun _ => false)) = false) :
    ∃ g' : Gate Role m, g'.profiles = g.restrictedProfiles port dead enabled :=
  exists_of_admissible three _ (g.admissible_restrictedProfiles port dead enabled hdead)

/-- Replacing fixed inputs by their background and suppressing unavailable
singleton flags on live inputs preserves both the winner bounds and the
exact atomic information needed by the next gate. -/
theorem restriction_eval (g : Gate Role n) (g' : Gate Role m)
    (port : Fin (n + 1) → Option (Fin (m + 1)))
    (dead : Fin (n + 1) → Option Role) (enabled : Role → Fin (n + 1) → Bool)
    (hg' : g'.profiles = g.restrictedProfiles port dead enabled)
    (hport : ∀ i, ∃ j, port j = some i)
    (x : Fin (n + 1) → WinnerSet Role) (y : Fin (m + 1) → WinnerSet Role) (B : Set Role)
    (hlive : ∀ j i, port j = some i →
      (y i).val ⊆ (x j).val ∧ (x j).val ⊆ (y i).val ∪ B ∧
      ∀ r, x j = WinnerSet.singleton r ↔ enabled r j = true ∧ y i = WinnerSet.singleton r)
    (hfixed : ∀ j, port j = none → (x j).val ⊆ B ∧
      ∀ r, x j = WinnerSet.singleton r ↔ dead j = some r) :
    (g'.eval y).val ⊆ (g.eval x).val ∧ (g.eval x).val ⊆ (g'.eval y).val ∪ B ∧
    ∀ r, g.eval x = WinnerSet.singleton r ↔
      g.profiles r (restrictedBits port dead enabled r (fun _ => true)) = true ∧
      g'.eval y = WinnerSet.singleton r := by
  classical
  have hbits (r : Role) : ProfileBounds.atomicBits r x =
      restrictedBits port dead enabled r (ProfileBounds.atomicBits r y) := by
    funext j
    apply Bool.eq_iff_iff.mpr
    cases hj : port j with
    | none => simpa [ProfileBounds.atomicBits, restrictedBits, hj] using (hfixed j hj).2 r
    | some i => simpa [ProfileBounds.atomicBits, restrictedBits, hj] using (hlive j i hj).2.2 r
  have hsingle (r : Role) : g.eval x = WinnerSet.singleton r ↔
      g.profiles r (restrictedBits port dead enabled r (fun _ => true)) = true ∧
        g'.eval y = WinnerSet.singleton r := by
    rw [g.singleton_iff, hbits, g'.singleton_iff, hg', restrictedProfiles]
    by_cases ha : g.profiles r (restrictedBits port dead enabled r (fun _ => true)) = true
    · rw [ite_eq_left ha]
      exact ⟨fun h => ⟨ha, h⟩, And.right⟩
    · constructor
      · intro h
        apply (ha (g.admissible.mono r _ _ ?_ h)).elim
        intro j hj
        cases hp : port j with
        | none => simpa [restrictedBits, hp] using hj
        | some i => simpa [restrictedBits, hp] using (Bool.and_eq_true_iff.mp
            (by simpa only [restrictedBits, hp] using hj)).1
      · exact fun h => (ha h.1).elim
  obtain ⟨hl, hu⟩ :
      (g'.eval y).val ⊆ (g.eval x).val ∧ (g.eval x).val ⊆ (g'.eval y).val ∪ B := by
    by_cases h : (g.eval x).Ambiguous
    · have hfull : (g'.eval y).val = ⋃ i, (y i).val := by
        by_cases h' : (g'.eval y).Ambiguous
        · exact g'.union_of_ambiguous y h'
        · obtain ⟨r, hr⟩ : ∃ r, g'.eval y = WinnerSet.singleton r := by
            simpa only [WinnerSet.Ambiguous, not_forall, not_not] using h'
          have hinactive : ¬g.profiles r (restrictedBits port dead enabled r (fun _ => true)) = true :=
            fun ha => h r ((hsingle r).2 ⟨ha, hr⟩)
          have hall := (g'.singleton_iff y r).1 hr
          rw [hg', restrictedProfiles, ite_eq_right hinactive, decide_eq_true_eq] at hall
          have hy (i) : y i = WinnerSet.singleton r := of_decide_eq_true (hall i)
          simp [hr, hy]
      rw [hfull, g.union_of_ambiguous x h]
      constructor
      · intro r hr
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
        obtain ⟨j, hj⟩ := hport i
        exact Set.mem_iUnion.mpr ⟨j, (hlive j i hj).1 hi⟩
      · intro r hr
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hr
        cases hp : port j with
        | none => exact Or.inr ((hfixed j hp).1 hj)
        | some i =>
          rcases (hlive j i hp).2.1 hj with hi | hB
          · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
          · exact Or.inr hB
    · obtain ⟨r, hr⟩ : ∃ r, g.eval x = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous, not_forall, not_not] using h
      rw [((hsingle r).1 hr).2, hr]
      exact ⟨Set.Subset.rfl, Set.subset_union_left⟩
  exact ⟨hl, hu, hsingle⟩

end KFOL.Core.CompletionDepth.Gate
