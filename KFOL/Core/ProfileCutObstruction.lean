module

public import KFOL.Core.PurePostingPaths
import Mathlib.Data.Fintype.Powerset

/-! # An eight-input guard family passing its boundary cuts and all pure source tests -/

@[expose] public section
namespace KFOL.Core.ProfileCutObstruction

inductive Input | A | a | X | B | Y | b | Z | U deriving DecidableEq, Inhabited

instance : Fintype Input := ⟨{.A, .a, .X, .B, .Y, .b, .Z, .U}, by intro j; cases j <;> simp⟩

/-- The labels 0, 1 and 2 represent α, β and d, respectively. -/
def owner : Input → Fin 3
  | .A | .a | .U => 0
  | .B | .b => 1
  | .X | .Y | .Z => 2

/-- The unique loss at each head posts the listed inputs at its own color. -/
def tail : Input → List Input
  | .A => [.X, .B, .b, .Z, .U]
  | .a => [.B, .b, .Z, .U]
  | .X => [.A, .B, .Y]
  | .B => [.A, .a, .Y, .Z]
  | .Y => [.a, .X, .B]
  | .b => [.A, .X, .Z]
  | .Z => [.A, .b]
  | .U => [.A, .a]

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 4096 in
/-- Every consistent cut enclosing an edge contains one of the three
reciprocal monochromatic pairs AU, aU, XY, with no palette restriction. -/
theorem compatible_cut_contains_pair :
    ∀ H : Finset Input,
      (∀ k ∉ H, ∀ i ∈ H, ∀ j ∈ H, k ∈ tail i → k ∈ tail j → owner i = owner j) →
      (∃ i ∈ H, ∃ j ∈ H, j ∈ tail i) →
      (.U ∈ H ∧ (.A ∈ H ∨ .a ∈ H)) ∨ (.X ∈ H ∧ .Y ∈ H) := by decide

variable {Role : Type*}
attribute [local instance] Equational.coreStructure
open MonochromaticCutObstruction (pureProbe)
open PurePostingPaths (ReachesPair)

/-- In the α-deleted graph all remaining heads reach X,Y. Otherwise the
α-pairs A,U and a,U are available from each remaining head. -/
private theorem avoids_color (three : Fin 3 ↪ Role) (r : Role) (i : Input) (away : three (owner i) ≠ r) :
    ReachesPair (fun j => three (owner j)) (fun j u => (tail j).contains u) r i := by
  let R := ReachesPair (fun j => three (owner j)) (fun j u => (tail j).contains u) r
  by_cases ha : three 0 = r
  · have hd : three 2 ≠ r := fun h => (by decide : (2 : Fin 3) ≠ 0) (three.injective (h.trans ha.symm))
    have hb : three 1 ≠ r := fun h => (by decide : (1 : Fin 3) ≠ 0) (three.injective (h.trans ha.symm))
    have x : R .X := .pair (j := .Y) hd rfl rfl rfl
    have y : R .Y := .pair (j := .X) hd rfl rfl rfl
    have b : R .b := .step hb rfl x
    cases i with
    | A | a | U => exact (away ha).elim
    | X => exact x
    | Y => exact y
    | B => exact .step hb rfl y
    | b => exact b
    | Z => exact .step hd rfl b
  · have A : R .A := .pair (j := .U) ha rfl rfl rfl
    have a : R .a := .pair (j := .U) ha rfl rfl rfl
    cases i with
    | A => exact A
    | a => exact a
    | U => exact .pair (j := .A) ha rfl rfl rfl
    | B | b | X | Z => exact .step away rfl A
    | Y => exact .step away rfl a

/-- One and the same bounded word agrees with every pure source observation
and with every singleton profile of the eight-head family. -/
theorem exists_pure_and_profile_realizer [Fintype Role] [DecidableEq Role] (three : Fin 3 ↪ Role) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Input,
      (∀ h r k (other : r ≠ k) (T : Input → Bool), T h = false →
        (k ∈ (t.realize (pureProbe three k h r other T)).val ↔
          three (owner h) ≠ r ∨ ∃ u ∈ tail h, T u = false)) ∧
      ∀ r (T : Input → Bool), profile r T t = true ↔
        ∀ h, T h = true ∨ three (owner h) = r ∧ ∀ u ∈ tail h, T u = true := by
  classical
  have noSelf : ∀ i, (tail i).contains i = false := by decide
  have recip : ∀ i j, owner i = owner j → (tail i).contains j = true → (tail j).contains i = true := by
    decide
  obtain ⟨t, ht⟩ := PurePostingPaths.exists_pure_realizer three (fun i => three (owner i))
    (fun i j => (tail i).contains j) noSelf (fun i j eq => recip i j (three.injective eq)) (avoids_color three)
  simp only [List.contains_iff_mem] at ht
  refine ⟨t, ht, fun r T => ?_⟩
  let _ : Nontrivial Role := ⟨three 0, three 1, three.injective.ne (by decide)⟩
  obtain ⟨k, hk⟩ := exists_ne r
  rw [PurePostingPaths.profile_iff_pure_omissions three r k hk.symm]
  constructor
  · intro quiet h
    cases hh : T h with
    | true => exact Or.inl rfl
    | false =>
      have neg := fun hp => quiet h hh ((ht h r k hk.symm T hh).mpr hp)
      refine Or.inr ⟨not_not.mp (fun ne => neg (Or.inl ne)), fun u hu => ?_⟩
      exact Bool.eq_true_of_not_eq_false (fun no => neg (Or.inr ⟨u, hu, no⟩))
  · intro all h hh hm
    obtain ⟨eq, postings⟩ := (all h).resolve_left (by simp [hh])
    rcases (ht h r k hk.symm T hh).mp hm with ne | ⟨u, hu, no⟩
    · exact ne eq
    · rw [postings u hu] at no
      contradiction

end KFOL.Core.ProfileCutObstruction
