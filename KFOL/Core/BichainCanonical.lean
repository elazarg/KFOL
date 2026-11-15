module

public import KFOL.Core.BichainSeparatingSource

/-! # Canonical extensions obey the stable separating-source law -/

@[expose] public section
namespace KFOL.Bichain

universe u
variable {Var : Type u} [Fintype Var] [DecidableEq Var]

omit [Fintype Var] [DecidableEq Var] in
@[simp] theorem cubeLower_ofBool (v : Var → Bool) :
    cubeLower (fun j => Value.ofBool (v j)) = v := by
  funext j
  cases h : v j <;> simp [cubeLower, Value.ofBool, h]

omit [Fintype Var] [DecidableEq Var] in
@[simp] theorem cubeUpper_ofBool (v : Var → Bool) :
    cubeUpper (fun j => Value.ofBool (v j)) = v := by
  funext j
  cases h : v j <;> simp [cubeUpper, Value.ofBool, h]

@[simp] theorem canonicalExtension_ofBool (f : (Var → Bool) → Bool) (v : Var → Bool) :
    canonicalExtension f (fun j => Value.ofBool (v j)) = Value.ofBool (f v) := by
  simp only [canonicalExtension, cubeLower_ofBool, cubeUpper_ofBool]
  cases f v <;> rfl

/-- A possible canonical output always has a genuinely essential marked source. -/
theorem exists_essential_of_canonicalExtension_possible (f : (Var → Bool) → Bool)
    (v : Var → Value) (h : canonicalExtension f v = .possible) :
    ∃ j, v j = .possible ∧ Essential f (cubeLower v) (cubeUpper v) j := by
  unfold canonicalExtension at h
  split at h
  · contradiction
  · split at h
    · split at h
      · assumption
      · contradiction
    · contradiction

omit [Fintype Var] in
@[simp] theorem markedCube_self (lower upper : Var → Bool) (j : Var) :
    markedCube lower upper j j = .possible := by simp [markedCube]

omit [Fintype Var] in
@[simp] theorem markedCube_possible_iff (lower upper : Var → Bool) (j i : Var) :
    markedCube lower upper j i = .possible ↔ i = j := by
  by_cases hij : i = j
  · simp [markedCube, hij]
  · cases hl : lower i <;> cases hu : upper i <;> simp_all [markedCube]

omit [Fintype Var] in
theorem cubeLower_markedCube (lower upper : Var → Bool) (j : Var)
    (hj : lower j = false) : cubeLower (markedCube lower upper j) = lower := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [cubeLower, markedCube, hj]
  · cases hl : lower i <;> cases hu : upper i <;>
      simp [cubeLower, markedCube, hij, hl, hu]

omit [Fintype Var] in
theorem cubeUpper_markedCube (lower upper : Var → Bool) (j : Var)
    (h : lower ≤ upper) (hj : upper j = true) :
    cubeUpper (markedCube lower upper j) = upper := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [cubeUpper, markedCube, hj]
  · have hi := h i
    cases hl : lower i <;> cases hu : upper i <;>
      simp_all [cubeUpper, markedCube]
    exact Bool.noConfusion ((Bool.le_iff_imp.mp hi) rfl)

/-- The source selected from one positive/negative pair remains essential in
all compatible cubes. This includes realizations using observer union. -/
theorem HasCanonicalRealizer.stableSeparatingSource
    {f : (Var → Bool) → Bool} (hf : HasCanonicalRealizer f) : StableSeparatingSource f := by
  obtain ⟨t, ht⟩ := hf
  intro A B hA hB
  have htA : t.eval (fun j => Value.ofBool (A j)) = .c := by
    rw [ht, canonicalExtension_ofBool, hA]
    rfl
  have htB : t.eval (fun j => Value.ofBool (B j)) = .b := by
    rw [ht, canonicalExtension_ofBool, hB]
    rfl
  obtain ⟨j, hjA, hjB, hj⟩ := t.stable_separating_source A B htA htB
  refine ⟨j, hjA, hjB, ?_⟩
  intro lower upper hlu hlB hAu
  have hlj : lower j = false := by
    have hle := hlB j
    rw [hjB] at hle
    cases hlj : lower j
    · rfl
    · exact Bool.noConfusion ((Bool.le_iff_imp.mp hle) hlj)
  have huj : upper j = true := (Bool.le_iff_imp.mp (hAu j)) hjA
  let v := markedCube lower upper j
  have hvl : cubeLower v = lower := cubeLower_markedCube lower upper j hlj
  have hvu : cubeUpper v = upper := cubeUpper_markedCube lower upper j hlu huj
  have hp : t.eval v = .possible := by
    apply hj v
    · intro i hi
      have hui : cubeUpper v i = true := by
        rw [hvu]
        exact (Bool.le_iff_imp.mp (hAu i)) hi
      simpa [cubeUpper] using hui
    · intro i hi
      have hli : cubeLower v i = true := by simp [cubeLower, hi]
      rw [hvl] at hli
      exact (Bool.le_iff_imp.mp (hlB i)) hli
    · exact markedCube_self lower upper j
  rw [ht] at hp
  obtain ⟨i, hi, he⟩ := exists_essential_of_canonicalExtension_possible f v hp
  have hij : i = j := (markedCube_possible_iff lower upper j i).mp hi
  subst i
  simpa only [hvl, hvu] using he

end KFOL.Bichain
