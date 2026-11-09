module

public import KFOL.Core.PairModel
public import KFOL.Core.AtomicNative

/-! # The typed upper-clone cover, through its generated-pair construction -/

@[expose] public section

namespace KFOL.Core

universe u v w

open FirstOrder

variable {Role : Type u} [DecidableEq Role]
variable {C : Type v} [(Equational.language (Equational.CoreSymbol Role)).Structure C]
variable {P : Type w} [(Equational.language (Equational.CoreSymbol Role)).Structure P]

attribute [local instance] Equational.coreStructure Native.structureOf pairStructure

omit [DecidableEq Role] in
theorem upperChoice_comm
    (hC : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) C)
    (e : C) (r : Role) (x y : Option C) : upperChoice e r x y = upperChoice e r y x := by
  cases x <;> cases y <;> simp only [upperChoice]
  exact congrArg some (operation_comm hC r _ _)

/-- The typed-cover hypotheses are exactly the independent proper native
typing and reflecting-ideal hypotheses. The proof constructs a generated
subalgebra and an actual surjective homomorphism onto the upper clone. -/
theorem typed_upper_clone_cover
    (three : Fin 3 ↪ Role)
    (hC : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) C)
    (e : C)
    (reflecting : ∀ (r : Role) (c : C),
      join three (operation r e c) e = e → join three c e = e)
    (R : Set Role) (proper : R ≠ Set.univ)
    (η : ideal hC three e →[Equational.language (Equational.CoreSymbol Role)] Native.atomicRestriction R)
    (typed : ∀ (c : ideal hC three e) (r : Role),
      (η c).val = Native.atom r ↔ operation r e c.val ≠ e)
    (hP : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) P)
    (q : P →[Equational.language (Equational.CoreSymbol Role)] C)
    (onto : Function.Surjective q)
    (label : P →[Equational.language (Equational.CoreSymbol Role)] Native.atomicRestriction R)
    (compatible : ∀ (u : P) (hu : join three (q u) e = e), label u = η ⟨q u, hu⟩) :
    letI := upperStructure (Role := Role) e
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Option C) := by
  classical
  obtain ⟨u₀, hu₀⟩ := onto e
  have heta : (η ⟨e, join_idem hC three e⟩).val = Native.lower := by
    apply Native.ext_atoms_upper
    · intro r
      simp only [reduceCtorEq, iff_false]
      exact fun he => (typed _ r).mp he (operation_idem hC r e)
    · simp [Native.atomic_ne_upper]
  have hlower : (label u₀).val = Native.lower := by
    have hu : join three (q u₀) e = e := by rw [hu₀]; exact join_idem hC three e
    rw [compatible u₀ hu]
    have harg : (⟨q u₀, hu⟩ : ideal hC three e) = ⟨e, join_idem hC three e⟩ :=
      Subtype.ext hu₀
    rw [harg]
    exact heta
  let D := Native.restriction R
  have hopD (r : Role) (u v : D) :
      (operation r u v).val = Native.choice r u.val v.val := rfl
  let θ := Native.collapseHom R
  let Rel : P × D → Prop := fun x => θ x.2 = label x.1
  have rel_op (r : Role) (x y : P × D) (hx : Rel x) (hy : Rel y) : Rel (operation r x y) := by
    unfold Rel
    rw [operation_pair]
    change θ (operation r x.2 y.2) = label (operation r x.1 y.1)
    rw [hom_operation θ, hom_operation label, hx, hy]
  let Good : P × D → Prop := fun x => Rel x ∧
    (x.2.val = Native.upper → join three (q x.1) e = e → q x.1 = e)
  have split_marker (r : Role) (x y : P × D) (hx : Good x) (hy : Good y)
      (hp : Native.choice r x.2.val y.2.val = Native.upper)
      (hz : join three (q (operation r x.1 y.1)) e = e) :
      operation r e (q (operation r x.1 y.1)) = e ∧
        ((q x.1 = e ∧ x.2.val = Native.upper) ∨ (q y.1 = e ∧ y.2.val = Native.upper)) := by
    have hrel := congrArg (fun a : Native.atomicRestriction R => a.val) (rel_op r x y hx.1 hy.1)
    rw [operation_pair] at hrel
    change Native.collapseUpper (Native.choice r x.2.val y.2.val) = (label (operation r x.1 y.1)).val at hrel
    rw [hp] at hrel
    have hc := congrArg (fun a : Native.atomicRestriction R => a.val)
      (compatible (operation r x.1 y.1) hz)
    have hetaLower : (η ⟨q (operation r x.1 y.1), hz⟩).val = Native.lower := hc.symm.trans hrel.symm
    have hez : operation r e (q (operation r x.1 y.1)) = e := by
      by_contra hn
      have ha := (typed ⟨q (operation r x.1 y.1), hz⟩ r).mpr hn
      rw [hetaLower] at ha
      cases ha
    have hf := operation_absorb_factors hC r e (q x.1) (q y.1) (by
      rw [← hom_operation q]
      exact hez)
    have hxe : join three (q x.1) e = e := reflecting r (q x.1) (by
      rw [hf.1]
      exact join_idem hC three e)
    have hye : join three (q y.1) e = e := reflecting r (q y.1) (by
      rw [hf.2]
      exact join_idem hC three e)
    refine ⟨hez, ?_⟩
    rcases (Native.choice_eq_upper r _ _).mp hp with ⟨hp | hp, _, _⟩
    · exact Or.inl ⟨hx.2 hp hxe, hp⟩
    · exact Or.inr ⟨hy.2 hp hye, hp⟩
  have good_op (r : Role) (x y : P × D) (hx : Good x) (hy : Good y) : Good (operation r x y) := by
    refine ⟨rel_op r x y hx.1 hy.1, ?_⟩
    rw [operation_pair]
    intro hp hz
    obtain ⟨hez, hx | hy⟩ := split_marker r x y hx hy hp hz
    · have hsame : operation r e (q (operation r x.1 y.1)) = q (operation r x.1 y.1) := by
        rw [hom_operation q, hx.1, operation_absorb_left hC]
      exact hsame.symm.trans hez
    · have hsame : operation r e (q (operation r x.1 y.1)) = q (operation r x.1 y.1) := by
        rw [hom_operation q, hy.1, operation_comm hC r (q x.1) e, operation_absorb_left hC]
      exact hsame.symm.trans hez
  let graph : P → P × D := fun u => (u, ⟨(label u).val, (label u).property.1⟩)
  let special : P × D := (u₀, ⟨Native.upper, by intro r he; cases he⟩)
  let seeds : Set (P × D) := Set.range graph ∪ {special}
  let M := Language.Substructure.closure (Equational.language (Equational.CoreSymbol Role)) seeds
  have good_seed : ∀ x ∈ seeds, Good x := by
    intro x hx
    rcases hx with ⟨u, rfl⟩ | rfl
    · constructor
      · apply Subtype.ext
        exact Native.collapseUpper_eq_self (Native.atomic_ne_upper (label u))
      · exact fun hp => False.elim (Native.atomic_ne_upper (label u) hp)
    · constructor
      · apply Subtype.ext
        change Native.lower = (label u₀).val
        exact hlower.symm
      · exact fun _ _ => hu₀
  have good_mem : ∀ x ∈ M, Good x := by
    intro x hx
    refine Language.Substructure.closure_induction (p := Good) hx good_seed ?_
    intro n f args hargs
    cases f with
    | choice r =>
      rw [funMap_choice r args]
      exact good_op r (args 0) (args 1) (hargs 0) (hargs 1)
  let mapPair : P × D → Option C := fun x =>
    if q x.1 = e ∧ x.2.val = Native.upper then none else some (q x.1)
  have map_op (r : Role) (x y : P × D) (hx : Good x) (hy : Good y) :
      mapPair (operation r x y) = upperChoice e r (mapPair x) (mapPair y) := by
    have mixed (x y : P × D) (hx : Good x) (hy : Good y)
        (hxeps : q x.1 = e ∧ x.2.val = Native.upper)
        (hyeps : ¬(q y.1 = e ∧ y.2.val = Native.upper)) :
        mapPair (operation r x y) = upperChoice e r (mapPair x) (mapPair y) := by
      have hq : q (operation r x.1 y.1) = operation r e (q y.1) := by
        rw [hom_operation q, hxeps.1]
      have hmx : mapPair x = none := ite_eq_left hxeps
      have hmy : mapPair y = some (q y.1) := ite_eq_right hyeps
      by_cases hec : operation r e (q y.1) = e
      · have hye : join three (q y.1) e = e := reflecting r (q y.1) (by
          rw [hec]
          exact join_idem hC three e)
        have hetan : (η ⟨q y.1, hye⟩).val ≠ Native.atom r :=
          fun ha => (typed _ r).mp ha hec
        have hny : y.2.val ≠ Native.atom r := by
          intro ha
          apply hetan
          have hrel := congrArg (fun a : Native.atomicRestriction R => a.val) hy.1
          change Native.collapseUpper y.2.val = (label y.1).val at hrel
          rw [ha] at hrel
          rw [← compatible y.1 hye]
          exact hrel.symm
        have hp : Native.choice r x.2.val y.2.val = Native.upper := by
          rw [hxeps.2]
          exact (Native.choice_eq_upper r _ _).mpr ⟨Or.inl rfl, by simp, hny⟩
        have htag : q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper :=
          ⟨hq.trans hec, by rw [hopD]; exact hp⟩
        rw [operation_pair]
        change (if q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper
          then none else some (q (operation r x.1 y.1))) = _
        rw [ite_eq_left htag, hmx, hmy]
        change none = if operation r e (q y.1) = e then none else some (operation r e (q y.1))
        rw [ite_eq_left hec]
      · have htag : ¬(q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper) := by
          rintro ⟨he, _⟩
          exact hec (hq.symm.trans he)
        rw [operation_pair]
        change (if q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper
          then none else some (q (operation r x.1 y.1))) = _
        rw [ite_eq_right htag, hmx, hmy]
        change some (q (operation r x.1 y.1)) =
          if operation r e (q y.1) = e then none else some (operation r e (q y.1))
        rw [ite_eq_right hec, hq]
    by_cases hxeps : q x.1 = e ∧ x.2.val = Native.upper
    · by_cases hyeps : q y.1 = e ∧ y.2.val = Native.upper
      · have hq : q (operation r x.1 y.1) = e := by
          rw [hom_operation q, hxeps.1, hyeps.1, operation_idem hC]
        have hp : Native.choice r x.2.val y.2.val = Native.upper := by
          rw [hxeps.2, hyeps.2, Native.choice_self]
        have htag : q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper :=
          ⟨hq, by rw [hopD]; exact hp⟩
        have hmx : mapPair x = none := ite_eq_left hxeps
        have hmy : mapPair y = none := ite_eq_left hyeps
        rw [operation_pair]
        change (if q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper
          then none else some (q (operation r x.1 y.1))) = _
        rw [ite_eq_left htag, hmx, hmy]
        rfl
      · exact mixed x y hx hy hxeps hyeps
    · by_cases hyeps : q y.1 = e ∧ y.2.val = Native.upper
      · have hcomm : operation r x y = operation r y x := by
          rw [operation_pair, operation_pair]
          exact Prod.ext (operation_comm hP r _ _) (by
            apply Subtype.ext
            exact Native.choice_comm r _ _)
        rw [hcomm, mixed y x hy hx hyeps hxeps, upperChoice_comm hC]
      · have hn : ¬(q (operation r x.1 y.1) = e ∧ Native.choice r x.2.val y.2.val = Native.upper) := by
          rintro ⟨hq, hp⟩
          have hz : join three (q (operation r x.1 y.1)) e = e := by
            rw [hq]
            exact join_idem hC three e
          obtain ⟨_, hxe | hye⟩ := split_marker r x y hx hy hp hz
          · exact hxeps hxe
          · exact hyeps hye
        have htag : ¬(q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper) := by
          simpa only [hopD] using hn
        have hmx : mapPair x = some (q x.1) := ite_eq_right hxeps
        have hmy : mapPair y = some (q y.1) := ite_eq_right hyeps
        rw [operation_pair]
        change (if q (operation r x.1 y.1) = e ∧ (operation r x.2 y.2).val = Native.upper
          then none else some (q (operation r x.1 y.1))) = _
        rw [ite_eq_right htag, hmx, hmy]
        exact congrArg some (hom_operation q r x.1 y.1)
  let _ := upperStructure (Role := Role) e
  let φ : M →[Equational.language (Equational.CoreSymbol Role)] Option C :=
    { toFun x := mapPair x.val
      map_fun' := by
        intro n f args
        cases f with
        | choice r =>
          rw [funMap_choice r args]
          change mapPair (operation r (args 0) (args 1)).val = upperChoice e r _ _
          have hs := hom_operation M.subtype.toHom r (args 0) (args 1)
          change (operation r (args 0) (args 1)).val = operation r (args 0).val (args 1).val at hs
          rw [hs]
          exact map_op r (args 0).val (args 1).val (good_mem _ (args 0).property) (good_mem _ (args 1).property)
      map_rel' := by intro n r; exact nomatch r }
  have surj : Function.Surjective φ := by
    intro x
    cases x with
    | none =>
      refine ⟨⟨special, Language.Substructure.subset_closure (Or.inr rfl)⟩, ?_⟩
      change mapPair special = none
      simp [mapPair, special, hu₀]
    | some c =>
      obtain ⟨u, hu⟩ := onto c
      refine ⟨⟨graph u, Language.Substructure.subset_closure (Or.inl ⟨u, rfl⟩)⟩, ?_⟩
      change mapPair (graph u) = some c
      simp [mapPair, graph, Native.atomic_ne_upper (label u), hu]
  have : Nonempty M := ⟨⟨special, Language.Substructure.subset_closure (Or.inr rfl)⟩⟩
  have hD := Native.restriction_inVariety three R proper
  have hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M :=
    (pair_inVariety hP hD).substructure M
  exact hM.of_surjective φ surj

end KFOL.Core
