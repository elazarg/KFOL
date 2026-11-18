module

public import KFOL.Core.EdgeSupportPruning
import Mathlib.Data.Fintype.Powerset

/-! # A compatible graph with an edge in no robust rectangle -/

@[expose] public section
namespace KFOL.Core.NonrectangularPruning

open ProfileBudgets GraphPruning

inductive Vertex | u | v | a | b | x | y | z deriving DecidableEq

open Vertex

instance : Fintype Vertex := ⟨{u, v, a, b, x, y, z}, by intro p; cases p <;> decide⟩

/-- One orientation of each of the ten edges. -/
def directed : Vertex → Vertex → Bool
  | .u, .v | .u, .a | .u, .b | .v, .x | .v, .y
  | .a, .x | .b, .y | .x, .y | .z, .a | .z, .b => true
  | _, _ => false

def graph : SimpleGraph Vertex where
  Adj p q := directed p q = true ∨ directed q p = true
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun p => by cases p <;> decide⟩

instance : DecidableRel graph.Adj := fun p q =>
  inferInstanceAs (Decidable (directed p q = true ∨ directed q p = true))

local infixr:65 " ⋏ " => choiceTerm false
local infixr:60 " ⋎ " => choiceTerm true

/-- A rectangle at the four edges between `zu` and `ab`, followed by the
two factors that supply the remaining six edges. -/
def word : CoreTerm Bool Vertex :=
  ((.var z ⋎ .var u) ⋏ (.var a ⋎ .var b)) ⋎
    ((.var y ⋎ ((.var x ⋎ .var u) ⋏ (.var v ⋎ .var a))) ⋏
     (.var x ⋎ ((.var y ⋎ .var u) ⋏ (.var v ⋎ .var b))))

private def enumeration (r : Bool) : CoreTerm Bool Vertex → List (Finset Vertex)
  | .var i => [{i}]
  | .func (.choice q) c =>
    let l := enumeration r (c 0)
    let h := enumeration r (c 1)
    if q = r then l.flatMap fun A => h.map fun B => A ∪ B else l ++ h

private theorem enumerates (r : Bool) (t : CoreTerm Bool Vertex) (H : Set Vertex) :
    H ∈ Supports r t ↔ ∃ A ∈ enumeration r t, (A : Set Vertex) = H := by
  induction t using induction_choice generalizing H with
  | var i =>
    change H = {i} ↔ ∃ A ∈ [({i} : Finset Vertex)], (A : Set Vertex) = H
    simp [eq_comm]
  | choice q l h il ih =>
    by_cases qr : q = r
    · subst q
      simp only [Supports, choiceTerm, enumeration, ite_true, Set.mem_ofPred_eq,
        List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨L, hl, R, hr, rfl⟩
        obtain ⟨A, ha, rfl⟩ := (il L).mp hl
        obtain ⟨B, hb, rfl⟩ := (ih R).mp hr
        exact ⟨A ∪ B, ⟨A, ha, B, hb, rfl⟩, Finset.coe_union _ _⟩
      · rintro ⟨_, ⟨A, ha, B, hb, rfl⟩, rfl⟩
        exact ⟨A, (il _).mpr ⟨_, ha, rfl⟩, B, (ih _).mpr ⟨_, hb, rfl⟩, (Finset.coe_union _ _).symm⟩
    · simp only [Supports, choiceTerm, enumeration, ite_eq_right qr, Set.mem_union, ite_true, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), List.mem_append]
      rw [il H, ih H]
      grind

private def Cover (C : Finset Vertex) : Prop :=
  ∀ p q, graph.Adj p q → p ∈ C ∨ q ∈ C

private def MinimalCover (C : Finset Vertex) : Prop :=
  Cover C ∧ ∀ p ∈ C, ∃ q ∉ C, graph.Adj p q

private instance (C : Finset Vertex) : Decidable (Cover C) := by unfold Cover; infer_instance
private instance (C : Finset Vertex) : Decidable (MinimalCover C) := by unfold MinimalCover; infer_instance

private theorem minimal_iff (C : Finset Vertex) :
    MinimalCover C ↔ Minimal graph.IsVertexCover (C : Set Vertex) := by
  classical
  constructor
  · rintro ⟨cov, witnesses⟩
    refine ⟨fun p q e => cov p q e, ?_⟩
    intro D d sub p hp
    obtain ⟨q, hq, e⟩ := witnesses p hp
    exact (d e).resolve_right (fun here => hq (sub here))
  · intro m
    refine ⟨fun _ _ e => m.prop e, ?_⟩
    intro p hp
    by_contra! no
    have cov : graph.IsVertexCover ((C : Set Vertex) \ {p}) := by
      intro s t e
      by_cases sp : s = p
      · subst s
        exact Or.inr ⟨by_contra (fun h => no t h e), e.ne'⟩
      · by_cases tp : t = p
        · subst t
          exact Or.inl ⟨by_contra (fun h => no s h e.symm), e.ne⟩
        · exact (m.prop e).imp (fun h => ⟨h, sp⟩) (fun h => ⟨h, tp⟩)
    exact (m.le_of_le cov Set.sdiff_subset hp).2 rfl

private def covers : List (Finset Vertex) :=
  [{z, u, v, a, y}, {v, a, b, y}, {z, u, v, b, x}, {v, a, b, x}, {z, u, y, x}, {u, a, b, y, x}]

section
set_option maxRecDepth 8192

private theorem cover_certificate : ∀ C ∈ covers, MinimalCover C := by decide

private theorem positive_certificate :
    ∀ H ∈ enumeration false word, H.Nonempty ∧ ∀ p ∈ H, ∃ q ∈ H, graph.Adj p q := by decide

private theorem negative_certificate :
    ∀ H ∈ enumeration true word, Cover H ∧ ∀ p ∈ H, ∃ C ∈ covers, C ⊆ H ∧ p ∈ C := by decide

theorem word_compatible : Compatible graph word := by
  constructor
  · intro H hh
    obtain ⟨A, ha, rfl⟩ := (enumerates false word H).mp hh
    exact positive_certificate A ha
  · intro H hh
    obtain ⟨A, ha, rfl⟩ := (enumerates true word H).mp hh
    obtain ⟨cov, points⟩ := negative_certificate A ha
    refine ⟨fun p q e => cov p q e, ?_⟩
    intro p hp
    obtain ⟨C, hc, sub, hit⟩ := points p hp
    exact ⟨C, sub, (minimal_iff C).mp (cover_certificate C hc), hit⟩

/-- If every minimal cover through p meets T, so does each robust shore
through p, provided that T itself is independent. -/
private theorem robust_hits {S : Set Vertex} (hs : Robust graph S) {p : Vertex} (hp : p ∈ S)
    (T : Finset Vertex) (indep : ∀ s ∈ T, ∀ t ∈ T, ¬ graph.Adj s t)
    (hits : ∀ C : Finset Vertex, MinimalCover C → p ∈ C → ∃ t ∈ T, t ∈ C) :
    ∃ t ∈ T, t ∈ S := by
  classical
  by_contra! disjoint
  have cov : graph.IsVertexCover (T : Set Vertex)ᶜ := by
    intro s t e
    by_cases atT : s ∈ T
    · exact Or.inr (fun bt => indep s atT t bt e)
    · exact Or.inl atT
  obtain ⟨D, sub, m, pd⟩ := hs cov (fun s ha h => disjoint s h ha) p hp
  let C := D.toFinite.toFinset
  have eq : (C : Set Vertex) = D := by simp [C]
  have good : MinimalCover C := (minimal_iff C).mpr (eq ▸ m)
  obtain ⟨t, ht, hc⟩ := hits C good (show p ∈ (C : Set Vertex) from eq ▸ pd)
  exact sub (show t ∈ D from eq ▸ hc) ht

theorem edge_uncovered : graph.Adj u v ∧
    ¬ ∃ L R : Set Vertex, Robust graph L ∧ Robust graph R ∧
      u ∈ L ∧ v ∈ R ∧ ∀ l ∈ L, ∀ r ∈ R, graph.Adj l r := by
  refine ⟨by decide, ?_⟩
  rintro ⟨L, R, hl, hr, ul, vr, cross⟩
  have zl : z ∉ L := fun hz => (by decide : ¬ graph.Adj z v) (cross z hz v vr)
  have xl : x ∈ L := by
    obtain ⟨t, ht, h⟩ := robust_hits hl ul {z, x} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact (zl h).elim
    · exact h
  have yl : y ∈ L := by
    obtain ⟨t, ht, h⟩ := robust_hits hl ul {z, y} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact (zl h).elim
    · exact h
  obtain ⟨t, ht, h⟩ := robust_hits hr vr {a, b} (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact (by decide : ¬ graph.Adj y a) (cross y yl a h)
  · exact (by decide : ¬ graph.Adj x b) (cross x xl b h)

theorem exists_nonedge_support (t : CoreTerm Bool Vertex) (ht : Compatible graph t) :
    ∃ H ∈ Supports false t, ¬ ∃ first second, graph.Adj first second ∧ H = {first, second} := by
  classical
  by_contra! allPairs
  obtain ⟨uv, uncovered⟩ := edge_uncovered
  exact uncovered ((exists_edge_supports_iff_robust_rectangles graph ⟨u, v, uv⟩).mp
    ⟨t, ht, allPairs⟩ u v uv)

end
end KFOL.Core.NonrectangularPruning
