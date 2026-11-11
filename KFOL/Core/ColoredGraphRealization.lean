module

public import KFOL.Core.ColoredGraphConstruction
public import KFOL.Core.ColoredGraphReconstruction
public import Mathlib.Data.Fintype.EquivFin

/-! # Finite graph representations of every core term operation

The representation uses only the two forbidden colored subgraphs and the
maximal-clique formula from `Definitions.CoreGraph`. Independent occurrences
can carry the same variable label.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v
variable {Role : Type u} {Var : Type v}

private theorem sum_cut {O P : Type*} [Nonempty O] [Nonempty P]
    (G : Graph Role O) (H : Graph Role P) (r : Role) :
    (G.sum H r).Cut Set.univ r (Set.range Sum.inl) (Set.range Sum.inr) := by
  classical
  refine ⟨⟨.inl (Classical.choice inferInstance), ⟨_, rfl⟩⟩,
    ⟨.inr (Classical.choice inferInstance), ⟨_, rfl⟩⟩, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (by rintro x ⟨a, rfl⟩ ⟨b, h⟩; cases h)
  · ext x
    cases x <;> simp
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rfl

private theorem exists_graph [Nonempty Role] (t : Term Role Var) (ht : t.IsCore) :
    ∃ (O : Type) (_ : Fintype O) (_ : Nonempty O) (G : Graph Role O) (label : O → Var),
      G.NoRainbow ∧ G.NoAlternatingPath ∧ ∀ v k,
        (t.eval v = WinnerSet.singleton k ↔ G.Blocks Set.univ label v k) ∧
        (k ∈ (t.eval v).val ↔ G.Wins Set.univ label v k) := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x =>
    let G : Graph Role Unit := ⟨fun _ _ => Classical.choice inferInstance, fun _ _ => rfl⟩
    refine ⟨Unit, inferInstance, inferInstance, G, fun _ => x,
      G.noRainbow_of_subsingleton, G.noAlternatingPath_of_subsingleton, ?_⟩
    intro v k
    have hu : (Set.univ : Set Unit) = {()} := by ext y; cases y; simp
    rw [hu, blocks_singleton, wins_singleton]
    exact ⟨Iff.rfl, Iff.rfl⟩
  | choice r s t ihs iht =>
    obtain ⟨O, hO, hOn, G, labelG, hGRainbow, hGPath, hG⟩ := ihs ht.1
    obtain ⟨P, hP, hPn, H, labelH, hHRainbow, hHPath, hH⟩ := iht ht.2
    let _ := hO
    let _ := hOn
    let _ := hP
    let _ := hPn
    let J := G.sum H r
    let label : O ⊕ P → Var := Sum.elim labelG labelH
    refine ⟨O ⊕ P, inferInstance, inferInstance, J, label,
      hGRainbow.sum hHRainbow r, hGPath.sum hHPath r, ?_⟩
    intro v k
    have hGL (q : Role) : J.Blocks (Set.range Sum.inl) label v q ↔
        s.eval v = WinnerSet.singleton q := by
      rw [← Set.image_univ]
      exact ((J.blocks_comap_image_iff Sum.inl Sum.inl_injective Set.univ
        label labelG (fun _ => rfl) v q).symm).trans (hG v q).1.symm
    have hHR (q : Role) : J.Blocks (Set.range Sum.inr) label v q ↔
        t.eval v = WinnerSet.singleton q := by
      rw [← Set.image_univ]
      exact ((J.blocks_comap_image_iff Sum.inr Sum.inr_injective Set.univ
        label labelH (fun _ => rfl) v q).symm).trans (hH v q).1.symm
    have hWL (q : Role) : J.Wins (Set.range Sum.inl) label v q ↔ q ∈ (s.eval v).val := by
      rw [← Set.image_univ]
      exact ((J.wins_comap_image_iff Sum.inl Sum.inl_injective Set.univ
        label labelG (fun _ => rfl) v q).symm).trans (hG v q).2.symm
    have hWR (q : Role) : J.Wins (Set.range Sum.inr) label v q ↔ q ∈ (t.eval v).val := by
      rw [← Set.image_univ]
      exact ((J.wins_comap_image_iff Sum.inr Sum.inr_injective Set.univ
        label labelH (fun _ => rfl) v q).symm).trans (hH v q).2.symm
    exact ⟨(blocks_cut_choice (sum_cut G H r) label v (s.eval v) (t.eval v) hGL hHR k).symm,
      (wins_cut_choice (sum_cut G H r) label v (s.eval v) (t.eval v)
        hWL hWR (hGL r) (hHR r) k).symm⟩

/-- Every core term has a finite occurrence graph with the independent clique
semantics. Equal variable labels still denote independent occurrences. -/
theorem represents_of_term [Nonempty Role] (t : Term Role Var) (ht : t.IsCore) :
    Represents (fun v => t.eval v) := by
  classical
  obtain ⟨O, hO, hOn, G, label, hTri, hPath, hG⟩ := exists_graph t ht
  let _ := hO
  let _ := hOn
  let e : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  refine ⟨Fintype.card O, G.comap e, label ∘ e, Fintype.card_pos,
    hTri.comap e e.injective, hPath.comap e e.injective, ?_⟩
  intro v k
  exact (hG v k).2.trans (by simpa using (G.wins_comap_iff e Set.univ label v k).symm)

/-- A finite graph satisfying the two forbidden-pattern conditions always
reconstructs to one core term, simultaneously at every valuation. -/
theorem term_of_represents (f : (Var → WinnerSet Role) → WinnerSet Role)
    (h : Represents f) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v := by
  obtain ⟨n, G, label, hn, hTri, hPath, hG⟩ := h
  have hA : (Set.univ : Set (Fin n)).Nonempty := ⟨⟨0, hn⟩, Set.mem_univ _⟩
  obtain ⟨t, ht, hT⟩ := G.exists_term hTri hPath label hA
  refine ⟨t, ht, ?_⟩
  intro v
  exact Subtype.ext (Set.ext fun k => (hT v k).2.trans (hG v k).symm)

/-- Complete structural representation by finite colored graphs: no rainbow
triangle, no two-colored induced four-vertex path, and the clique source law. -/
theorem represents_iff [Nonempty Role] (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Represents f ↔ ∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v := by
  refine ⟨term_of_represents f, ?_⟩
  rintro ⟨t, ht, he⟩
  simpa only [he] using represents_of_term t ht

end KFOL.Core.ColoredGraph
