module

public import KFOL.Algebra.ReductTests
public import Mathlib.Data.Fin.Embedding

/-! # The sharp cardinality of complete reduct test domains -/

@[expose] public section

namespace KFOL

universe u

variable {Role : Type u} [Fintype Role]

/-- All atomic values, as a finite domain. -/
noncomputable def singletonDomain (Role : Type u) [Fintype Role] : Finset (WinnerSet Role) := by
  classical
  exact Finset.univ.image WinnerSet.singleton

@[simp] theorem mem_singletonDomain (A : WinnerSet Role) :
    A ∈ singletonDomain Role ↔ ∃ r, A = WinnerSet.singleton r := by
  classical
  simp [singletonDomain, eq_comm]

@[simp] theorem card_singletonDomain : (singletonDomain Role).card = Fintype.card Role := by
  classical
  rw [singletonDomain, Finset.card_image_of_injective _ (fun _ _ h => WinnerSet.singleton_inj.mp h),
    Finset.card_univ]

/-- All singletons and pairs, as a finite domain. -/
noncomputable def pairDomain (Role : Type u) [Fintype Role] : Finset (WinnerSet Role) := by
  classical
  exact (Finset.univ : Finset (Role × Role)).image
    (fun (a, b) => WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b))

@[simp] theorem mem_pairDomain (A : WinnerSet Role) :
    A ∈ pairDomain Role ↔ ∃ a b, A.val = {a, b} := by
  classical
  simp only [pairDomain, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨a, b, he⟩
    exact ⟨a, b, congrArg Subtype.val he.symm⟩
  · rintro ⟨a, b, he⟩
    exact ⟨a, b, Subtype.ext he.symm⟩

@[simp] theorem card_pairDomain :
    (pairDomain Role).card = Fintype.card Role * (Fintype.card Role + 1) / 2 := by
  classical
  rw [← card_pairValues Role, Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype (pairDomain Role) (fun A => mem_pairDomain A)).symm

private theorem singletonDomain_subset {D : Finset (WinnerSet Role)}
    (hat : ∀ r, WinnerSet.singleton r ∈ D) : singletonDomain Role ⊆ D := by
  intro A hA
  obtain ⟨r, rfl⟩ := (mem_singletonDomain A).mp hA
  exact hat r

private theorem ambiguous_not_mem_singletonDomain (A : WinnerSet Role) (hA : A.Ambiguous) :
    A ∉ singletonDomain Role := by
  rintro h
  obtain ⟨r, hr⟩ := (mem_singletonDomain A).mp h
  exact hA r hr

/-- Any complete domain contains the K atoms and at least two ambiguous values. -/
theorem card_public_domain_lower (three : Fin 3 ↪ Role) (D : Finset (WinnerSet Role))
    (hD : CompletePublicTestDomain (D : Set (WinnerSet Role))) :
    Fintype.card Role + 2 ≤ D.card := by
  classical
  obtain ⟨hat, hcover⟩ := (completePublicTestDomain_iff three _).mp hD
  obtain ⟨A, hAD, hA, _⟩ := hcover (three 0)
  obtain ⟨a, ha⟩ := A.property
  obtain ⟨B, hBD, hB, hb⟩ := hcover a
  have hne : A ≠ B := fun he => hb (he ▸ ha)
  have hAs := ambiguous_not_mem_singletonDomain A hA
  have hBs := ambiguous_not_mem_singletonDomain B hB
  have hsub : insert A (insert B (singletonDomain Role)) ⊆ D :=
    Finset.insert_subset hAD (Finset.insert_subset hBD (singletonDomain_subset hat))
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_insert_of_notMem, hne, hAs, hBs, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hcard

private theorem cover_three (hcard : Fintype.card Role = 3) (a b k : Role)
    (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (x : Role) :
    x = a ∨ x = b ∨ x = k := by
  classical
  by_contra hn
  have hxa : x ≠ a := fun h => hn (Or.inl h)
  have hxb : x ≠ b := fun h => hn (Or.inr (Or.inl h))
  have hxk : x ≠ k := fun h => hn (Or.inr (Or.inr h))
  have hle := Finset.card_le_card (Finset.subset_univ ({x, a, b, k} : Finset Role))
  have he : ({x, a, b, k} : Finset Role).card = 4 := by
    simp [hxa, hxb, hxk, hab, hak, hbk]
  rw [he, Finset.card_univ, hcard] at hle
  omega

/-- On three roles, coverage forces every pair as well as every singleton. -/
theorem pairDomain_subset_of_three (three : Fin 3 ↪ Role) (hcard : Fintype.card Role = 3)
    (D : Finset (WinnerSet Role)) (hD : CompletePublicTestDomain (D : Set (WinnerSet Role))) :
    pairDomain Role ⊆ D := by
  classical
  obtain ⟨hat, hc⟩ := (completePublicTestDomain_iff three _).mp hD
  intro A hA
  obtain ⟨a, b, hab⟩ := (mem_pairDomain A).mp hA
  by_cases heq : a = b
  · subst b
    have he : A = WinnerSet.singleton a := Subtype.ext (by simpa using hab)
    exact he ▸ hat a
  · obtain ⟨k, hka, hkb⟩ := exists_role_outside_pair three a b
    obtain ⟨F, hFD, hF, hk⟩ := hc k
    have hsub : F.val ⊆ {a, b} := by
      intro x hx
      rcases cover_three hcard a b k heq hka.symm hkb.symm x with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hk (h ▸ hx))
    have hFA : F = A := Subtype.ext ((WinnerSet.eq_pair_of_ambiguous_subset F a b hF hsub).trans hab.symm)
    exact hFA ▸ hFD

/-- The all-pairs domain is complete in the public reduct. -/
theorem completePublicTestDomain_pairDomain (three : Fin 3 ↪ Role) :
    CompletePublicTestDomain (pairDomain Role : Set (WinnerSet Role)) := by
  have hc : CompleteTestDomain (pairDomain Role : Set (WinnerSet Role)) :=
    (completeTestDomain_iff three _).mpr (fun a b => (mem_pairDomain _).mpr ⟨a, b, rfl⟩)
  intro n s t _ _ he
  exact hc n s t he

/-- Four distinct roles give a domain of K atoms and two disjoint pairs. -/
theorem exists_public_domain_card_add_two (three : Fin 3 ↪ Role) (four : Fin 4 ↪ Role) :
    ∃ D : Finset (WinnerSet Role), CompletePublicTestDomain (D : Set (WinnerSet Role)) ∧
      D.card = Fintype.card Role + 2 ∧
      ∀ X, X ∈ D ↔ (∃ r, X = WinnerSet.singleton r) ∨
        X.val = {four 0, four 1} ∨ X.val = {four 2, four 3} := by
  classical
  let A := WinnerSet.union (WinnerSet.singleton (four 0)) (WinnerSet.singleton (four 1))
  let B := WinnerSet.union (WinnerSet.singleton (four 2)) (WinnerSet.singleton (four 3))
  have hA : A.Ambiguous := WinnerSet.ambiguous_of_two_mem A (four 0) (four 1)
    (four.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
  have hB : B.Ambiguous := WinnerSet.ambiguous_of_two_mem B (four 2) (four 3)
    (four.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
  have hd : Disjoint A.val B.val := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals have he := four.injective (hx.symm.trans hy); cases he
  have hne : A ≠ B := fun he => Set.disjoint_left.mp hd (Or.inl rfl) (he ▸ Or.inl rfl)
  refine ⟨insert A (insert B (singletonDomain Role)), ?_, ?_, ?_⟩
  · apply (completePublicTestDomain_iff three _).mpr
    constructor
    · intro r
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((mem_singletonDomain _).mpr ⟨r, rfl⟩))
    · intro k
      by_cases hk : k ∈ A.val
      · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hB,
          fun hb => Set.disjoint_left.mp hd hk hb⟩
      · exact ⟨A, Finset.mem_insert_self _ _, hA, hk⟩
  · have hAs := ambiguous_not_mem_singletonDomain A hA
    have hBs := ambiguous_not_mem_singletonDomain B hB
    simp [hne, hAs, hBs, Nat.add_comm, Nat.add_left_comm]
  · intro X
    have hXA : X = A ↔ X.val = {four 0, four 1} :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hXB : X = B ↔ X.val = {four 2, four 3} :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    simp only [Finset.mem_insert, mem_singletonDomain, hXA, hXB]
    tauto

/-- Both the sharp lower bound and an attaining finite domain. -/
theorem public_domain_minimum (three : Fin 3 ↪ Role) :
    IsLeast {m : ℕ | ∃ D : Finset (WinnerSet Role),
      CompletePublicTestDomain (D : Set (WinnerSet Role)) ∧ D.card = m}
      (if Fintype.card Role = 3 then 6 else Fintype.card Role + 2) := by
  classical
  by_cases hthree : Fintype.card Role = 3
  · simp only [ite_eq_left hthree]
    constructor
    · exact ⟨pairDomain Role, completePublicTestDomain_pairDomain three,
        by simp [card_pairDomain, hthree]⟩
    · rintro n ⟨D, hD, rfl⟩
      have he := Finset.card_le_card (pairDomain_subset_of_three three hthree D hD)
      simpa [card_pairDomain, hthree] using he
  · simp only [ite_eq_right hthree]
    constructor
    · have hc : 3 ≤ Fintype.card Role := by simpa using Fintype.card_le_of_embedding three
      have hfour : 4 ≤ Fintype.card Role := by omega
      let four : Fin 4 ↪ Role := (Fin.castLEEmb hfour).trans (Fintype.equivFin Role).symm.toEmbedding
      obtain ⟨D, hD, hcard, _⟩ := exists_public_domain_card_add_two three four
      exact ⟨D, hD, hcard⟩
    · rintro n ⟨D, hD, rfl⟩
      exact card_public_domain_lower three D hD

end KFOL
