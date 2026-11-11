module

public import KFOL.Definitions.CoreGraph
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.FinCases

/-! # Decomposition of finite colored graphs

A complete colored graph without a rainbow triangle or a two-colored induced
four-vertex path has a nontrivial monochromatic cut. The proof follows the
finite layered-sequence argument of Gurvich, *Decomposing complete
edge-chromatic graphs and hypergraphs. Revisited* (2009), §§1–2:
complementary paths first shorten to two
edges, and a graph without a cut would admit arbitrarily many distinct layers.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v
variable {Role : Type u} {Vertex : Type v} (G : Graph Role Vertex)

namespace Graph

private theorem no_path_four (hPath : G.NoAlternatingPath)
    {x y z w : Vertex} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    {a b : Role} (hab : a ≠ b)
    (h₀₁ : G.color x y = a) (h₁₂ : G.color y z = a)
    (h₂₃ : G.color z w = a) (h₀₂ : G.color x z = b)
    (h₀₃ : G.color x w = b) (h₁₃ : G.color y w = b) : False := by
  let e : Fin 4 ↪ Vertex := ⟨![x, y, z, w], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  exact hPath e a b hab ⟨h₀₁, h₁₂, h₂₃, h₀₂, h₀₃, h₁₃⟩

private def Avoid (r : Role) (x y : Vertex) : Prop :=
  x ≠ y ∧ G.color x y ≠ r

private def Short (A : Set Vertex) (r : Role) (x y : Vertex) : Prop :=
  x = y ∨ G.Avoid r x y ∨ ∃ z ∈ A, G.Avoid r x z ∧ G.Avoid r z y

private theorem short_step (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath)
    {A : Set Vertex} {r : Role} {x y z : Vertex} (hy : y ∈ A)
    (hxy : G.Short A r x y) (hyz : G.Avoid r y z) : G.Short A r x z := by
  classical
  rcases hxy with rfl | hxy | ⟨w, hw, hxw, hwy⟩
  · exact Or.inr (Or.inl hyz)
  · exact Or.inr (Or.inr ⟨y, hy, hxy, hyz⟩)
  by_cases hxz : x = z
  · exact Or.inl hxz
  by_cases hxzc : G.color x z ≠ r
  · exact Or.inr (Or.inl ⟨hxz, hxzc⟩)
  have hxzc : G.color x z = r := not_not.mp hxzc
  by_cases hxy : x = y
  · subst y; exact Or.inr (Or.inl hyz)
  have hwz : w ≠ z := by
    intro h
    subst z
    exact hxw.2 hxzc
  by_cases hwzc : G.color w z ≠ r
  · exact Or.inr (Or.inr ⟨w, hw, hxw, ⟨hwz, hwzc⟩⟩)
  have hwzc : G.color w z = r := not_not.mp hwzc
  by_cases hxyc : G.color x y ≠ r
  · exact Or.inr (Or.inr ⟨y, hy, ⟨hxy, hxyc⟩, hyz⟩)
  have hxyc : G.color x y = r := not_not.mp hxyc
  have h₁ : G.color x w = G.color w y := by
    rcases hTri x w y hxw.1 hxy hwy.1 with h | h | h
    · exact h
    · exact False.elim (hxw.2 (h.trans hxyc))
    · exact False.elim (hwy.2 (h.trans hxyc))
  have h₂ : G.color w y = G.color y z := by
    rcases hTri w y z hwy.1 hwz hyz.1 with h | h | h
    · exact h
    · exact False.elim (hwy.2 (h.trans hwzc))
    · exact False.elim (hyz.2 (h.trans hwzc))
  exact False.elim (G.no_path_four hPath hxw.1 hxy hxz hwy.1 hwz hyz.1
    hxw.2 rfl h₁.symm (h₂.symm.trans h₁.symm) hxyc hxzc hwzc)

private theorem common_neighbor (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath)
    {A : Set Vertex} (hcut : ¬∃ r L R, G.Cut A r L R)
    {x y : Vertex} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    ∃ z ∈ A, z ≠ x ∧ z ≠ y ∧ G.color z x = G.color z y ∧
      G.color z x ≠ G.color x y := by
  classical
  let r := G.color x y
  let L : Set Vertex := {z | z ∈ A ∧ G.Short A r x z}
  have hxL : x ∈ L := ⟨hx, Or.inl rfl⟩
  have hLA : L ⊆ A := fun _ h => h.1
  have hcross : ∀ u ∈ L, ∀ v ∈ A \ L, G.color u v = r := by
    intro u hu v hv
    by_contra h
    have huv : u ≠ v := by
      intro he
      exact hv.2 (he ▸ hu)
    exact hv.2 ⟨hv.1, G.short_step hTri hPath hu.1 hu.2 ⟨huv, h⟩⟩
  have hyL : y ∈ L := by
    by_contra hyn
    apply hcut
    refine ⟨r, L, A \ L, ⟨x, hxL⟩, ⟨y, hy, hyn⟩, Set.disjoint_sdiff_right,
      ?_, hcross⟩
    ext z
    constructor
    · rintro (hz | hz)
      · exact hLA hz
      · exact hz.1
    · intro hz
      by_cases h : z ∈ L
      · exact Or.inl h
      · exact Or.inr ⟨hz, h⟩
  rcases hyL.2 with he | he | ⟨z, hz, hxz, hzy⟩
  · exact False.elim (hxy he)
  · exact False.elim (he.2 rfl)
  have hsame : G.color z x = G.color z y := by
    rcases hTri x z y hxz.1 hxy hzy.1 with h | h | h
    · exact (G.symm z x).trans h
    · exact False.elim (hxz.2 h)
    · exact False.elim (hzy.2 h)
  exact ⟨z, hz, hxz.1.symm, hzy.1, hsame,
    fun he => hxz.2 ((G.symm x z).trans he)⟩


private theorem extend_color (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath)
    {x y w z : Vertex} (hxy : x ≠ y) (hxw : x ≠ w) (hxz : x ≠ z)
    (hyw : y ≠ w) (hyz : y ≠ z) (hwz : w ≠ z)
    (hxwc : G.color x w = G.color x y) (hywc : G.color x y ≠ G.color y w)
    (hzxy : G.color z x = G.color z y) (hzxc : G.color z x ≠ G.color x y) :
    G.color z w = G.color z x := by
  by_contra hzwc
  have hzw : G.color z w = G.color x y := by
    rcases hTri x z w hxz hxw hwz.symm with h | h | h
    · exact False.elim (hzwc (h.symm.trans (G.symm x z)))
    · exact False.elim (hzxc ((G.symm z x).trans (h.trans hxwc)))
    · exact h.trans hxwc
  have hywcol : G.color y w = G.color z x := by
    rcases hTri y z w hyz hyw hwz.symm with h | h | h
    · exact False.elim (hzxc ((hzxy.trans (G.symm z y)).trans (h.trans hzw)))
    · exact h.symm.trans ((G.symm y z).trans hzxy.symm)
    · exact False.elim (hywc (hzw.symm.trans h))
  exact G.no_path_four hPath hxy.symm hyw hyz hxw hxz hwz
    hzxc.symm (G.symm y x) hxwc ((G.symm w z).trans hzw) hywcol
    ((G.symm y z).trans hzxy.symm) (G.symm x z)

private def Layered : List Vertex → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ∉ y :: xs ∧
      (∀ z ∈ xs, G.color x z = G.color x y) ∧
      (∀ z ∈ xs, G.color x y ≠ G.color y z) ∧ Layered (y :: xs)

private theorem layered_nodup {xs : List Vertex} (h : G.Layered xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    cases xs with
    | nil => exact List.nodup_singleton x
    | cons y xs => exact List.nodup_cons.mpr ⟨h.1, ih h.2.2.2⟩

private theorem layered_extend (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath)
    {A : Set Vertex} (hcut : ¬∃ r L R, G.Cut A r L R)
    {x y : Vertex} {xs : List Vertex} (hx : x ∈ A) (hy : y ∈ A)
    (hl : G.Layered (x :: y :: xs)) :
    ∃ z ∈ A, G.Layered (z :: x :: y :: xs) := by
  have hxy : x ≠ y := by
    intro he
    exact hl.1 (List.mem_cons.mpr (Or.inl he))
  obtain ⟨z, hz, hzx, hzy, hzxy, hzxc⟩ := G.common_neighbor hTri hPath hcut hx hy hxy
  have hzall : ∀ w ∈ y :: xs, G.color z w = G.color z x := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hzxy.symm
    have hxw : x ≠ w := by
      intro he
      subst w
      exact hl.1 (List.mem_cons.mpr (Or.inr hw))
    have hyw : y ≠ w := by
      intro he
      have hnodup := G.layered_nodup hl.2.2.2
      subst w
      exact (List.nodup_cons.mp hnodup).1 hw
    have hzw : z ≠ w := by
      intro he
      apply hzxc
      subst z
      exact (G.symm w x).trans (hl.2.1 w hw)
    exact G.extend_color hTri hPath hxy hxw hzx.symm hyw hzy.symm hzw.symm
      (hl.2.1 w hw) (hl.2.2.1 w hw) hzxy hzxc
  refine ⟨z, hz, ?_, hzall, ?_, hl⟩
  · intro hm
    rcases List.mem_cons.mp hm with he | hm
    · exact hzx he
    · rcases List.mem_cons.mp hm with he | hm
      · exact hzy he
      · exact hzxc ((G.symm z x).trans (hl.2.1 z hm))
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hzxc
    · exact fun he => hzxc (he.trans (hl.2.1 w hw))

/-- A finite complete colored graph with neither forbidden induced pattern
has a nontrivial monochromatic cut on every nonsingleton vertex region. -/
theorem exists_cut [Finite Vertex] (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath)
    {A : Set Vertex} (_hA : A.Nonempty) (hA₂ : ¬ A.Subsingleton) :
    ∃ r L R, G.Cut A r L R := by
  classical
  let _ := Fintype.ofFinite Vertex
  by_contra hcut
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hA₂
  have many (n : ℕ) : ∃ xs : List Vertex, xs.length = n + 2 ∧ G.Layered xs ∧
      ∀ z ∈ xs, z ∈ A := by
    induction n with
    | zero =>
      exact ⟨[x, y], rfl, ⟨by simpa using hxy, by simp, by simp, trivial⟩,
        by simp_all⟩
    | succ n ih =>
      obtain ⟨xs, hlen, hl, hm⟩ := ih
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
        cases xs with
        | nil => simp at hlen
        | cons b xs =>
          obtain ⟨z, hz, hnew⟩ := G.layered_extend hTri hPath hcut
            (hm a (by simp)) (hm b (by simp)) hl
          exact ⟨z :: a :: b :: xs, by simp only [List.length_cons] at hlen ⊢; omega, hnew,
            by intro w hw; rcases List.mem_cons.mp hw with rfl | hw
               · exact hz
               · exact hm w hw⟩
  obtain ⟨xs, hlen, hl, _⟩ := many (Fintype.card Vertex)
  have hbound := (G.layered_nodup hl).length_le_card
  omega

end Graph

end KFOL.Core.ColoredGraph
