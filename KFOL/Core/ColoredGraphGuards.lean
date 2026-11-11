module

public import KFOL.Core.ColoredGraphRealization
public import KFOL.Core.SourceCompatibility

/-! # Joint source guards as prime clique guards of colored graphs

The graph witness is independent of term syntax. Each observer/source family
is exactly the prime exclusion boxes of its clique predicate on source probes.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v
variable {Role : Type u} {Var : Type v}

/-- Canonical source families are jointly realizable precisely when they are
the prime clique guards of one finite graph with neither forbidden pattern. -/
theorem guard_realization_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Sources.Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ Sources.normalForm three (fun v => t.eval v) = G) ↔
      ∃ (n : ℕ) (H : Graph Role (Fin n)) (label : Fin n → Var),
        0 < n ∧ H.NoRainbow ∧ H.NoAlternatingPath ∧ ∀ k j g,
          g ∈ G k j ↔ Sources.Prime
            (fun p => H.Wins Set.univ label (Sources.probe three k j p) k) g := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩
    let _ : Nonempty Role := ⟨three 0⟩
    obtain ⟨n, H, label, hn, hTri, hPath, hH⟩ := represents_of_term t ht
    refine ⟨n, H, label, hn, hTri, hPath, ?_⟩
    intro k j g
    rw [Sources.mem_normalForm]
    have he : (fun p => k ∈ (t.eval (Sources.probe three k j p)).val) =
        (fun p => H.Wins Set.univ label (Sources.probe three k j p) k) :=
      funext fun p => propext (hH (Sources.probe three k j p) k)
    rw [he]
  · rintro ⟨n, H, label, hn, hTri, hPath, hG⟩
    have hA : (Set.univ : Set (Fin n)).Nonempty := ⟨⟨0, hn⟩, Set.mem_univ _⟩
    obtain ⟨t, ht, hT⟩ := H.exists_term hTri hPath label hA
    refine ⟨t, ht, ?_⟩
    funext k j
    apply Finset.ext
    intro g
    rw [Sources.mem_normalForm, hG k j g]
    have he : (fun p => k ∈ (t.eval (Sources.probe three k j p)).val) =
        (fun p => H.Wins Set.univ label (Sources.probe three k j p) k) :=
      funext fun p => propext (hT (Sources.probe three k j p) k).2
    rw [he]

/-- The independent source-guard compatibility predicate agrees with the
structural graph criterion. -/
theorem admissible_iff_graph [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Sources.Guard k j)) :
    Sources.Admissible three G ↔
      ∃ (n : ℕ) (H : Graph Role (Fin n)) (label : Fin n → Var),
        0 < n ∧ H.NoRainbow ∧ H.NoAlternatingPath ∧ ∀ k j g,
          g ∈ G k j ↔ Sources.Prime
            (fun p => H.Wins Set.univ label (Sources.probe three k j p) k) g :=
  (Sources.admissible_iff three G).trans (guard_realization_iff three G)

end KFOL.Core.ColoredGraph
