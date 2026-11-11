module

public import KFOL.Definitions.CoreGraph
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Tauto
public import Mathlib.Logic.Equiv.Set

/-! # Building and renaming colored-graph representations -/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v w
variable {Role : Type u} {Vertex : Type v} {Vertex' : Type w}

theorem Graph.NoRainbow.comap {G : Graph Role Vertex} (h : G.NoRainbow)
    (f : Vertex' → Vertex) (hf : Function.Injective f) : (G.comap f).NoRainbow := by
  intro x y z hxy hxz hyz
  exact h (f x) (f y) (f z) (hf.ne hxy) (hf.ne hxz) (hf.ne hyz)

theorem Graph.NoAlternatingPath.comap {G : Graph Role Vertex}
    (h : G.NoAlternatingPath) (f : Vertex' → Vertex) (hf : Function.Injective f) :
    (G.comap f).NoAlternatingPath := by
  intro x a b hab hp
  exact h (x.trans ⟨f, hf⟩) a b hab hp

theorem Graph.noRainbow_of_subsingleton [Subsingleton Vertex] (G : Graph Role Vertex) :
    G.NoRainbow := by
  intro x y _ hxy
  exact False.elim (hxy (Subsingleton.elim _ _))

theorem Graph.noAlternatingPath_of_subsingleton [Subsingleton Vertex]
    (G : Graph Role Vertex) : G.NoAlternatingPath := by
  intro x
  have h := x.injective (Subsingleton.elim (x 0) (x 1))
  exact False.elim ((show (0 : Fin 4) ≠ 1 by decide) h)

theorem Graph.NoRainbow.sum {G : Graph Role Vertex} {H : Graph Role Vertex'}
    (hG : G.NoRainbow) (hH : H.NoRainbow) (r : Role) : (G.sum H r).NoRainbow := by
  intro x y z hxy hxz hyz
  cases x <;> cases y <;> cases z
  all_goals simp only [Graph.sum]
  · exact hG _ _ _ (fun he => hxy (congrArg Sum.inl he))
      (fun he => hxz (congrArg Sum.inl he)) (fun he => hyz (congrArg Sum.inl he))
  all_goals try tauto
  · exact hH _ _ _ (fun he => hxy (congrArg Sum.inr he))
      (fun he => hxz (congrArg Sum.inr he)) (fun he => hyz (congrArg Sum.inr he))

theorem Graph.NoAlternatingPath.sum {G : Graph Role Vertex} {H : Graph Role Vertex'}
    (hG : G.NoAlternatingPath) (hH : H.NoAlternatingPath) (r : Role) :
    (G.sum H r).NoAlternatingPath := by
  intro x a b hab hp
  cases hx₀ : x 0 with
  | inl v₀ =>
    cases hx₁ : x 1 with
    | inl v₁ =>
      cases hx₂ : x 2 with
      | inl v₂ =>
        cases hx₃ : x 3 with
        | inl v₃ =>
          let e : Fin 4 ↪ Vertex := ⟨![v₀, v₁, v₂, v₃], by
            intro i j he
            apply x.injective
            fin_cases i <;> fin_cases j <;> simp_all⟩
          exact hG e a b hab (by
            change G.color v₀ v₁ = a ∧ G.color v₁ v₂ = a ∧ G.color v₂ v₃ = a ∧
              G.color v₀ v₂ = b ∧ G.color v₀ v₃ = b ∧ G.color v₁ v₃ = b
            simpa only [hx₀, hx₁, hx₂, hx₃, Graph.sum] using hp)
        | inr => simp_all [Graph.sum]; aesop
      | inr => cases hx₃ : x 3 <;> simp_all [Graph.sum] <;> aesop
    | inr => cases hx₂ : x 2 <;> cases hx₃ : x 3 <;> simp_all [Graph.sum] <;> aesop
  | inr v₀ =>
    cases hx₁ : x 1 with
    | inl => cases hx₂ : x 2 <;> cases hx₃ : x 3 <;> simp_all [Graph.sum] <;> aesop
    | inr v₁ =>
      cases hx₂ : x 2 with
      | inl => cases hx₃ : x 3 <;> simp_all [Graph.sum] <;> aesop
      | inr v₂ =>
        cases hx₃ : x 3 with
        | inl => simp_all [Graph.sum]; aesop
        | inr v₃ =>
          let e : Fin 4 ↪ Vertex' := ⟨![v₀, v₁, v₂, v₃], by
            intro i j he
            apply x.injective
            fin_cases i <;> fin_cases j <;> simp_all⟩
          exact hH e a b hab (by
            change H.color v₀ v₁ = a ∧ H.color v₁ v₂ = a ∧ H.color v₂ v₃ = a ∧
              H.color v₀ v₂ = b ∧ H.color v₀ v₃ = b ∧ H.color v₁ v₃ = b
            simpa only [hx₀, hx₁, hx₂, hx₃, Graph.sum] using hp)

/-- Renaming vertices carries each monochromatic clique to its image. -/
theorem Graph.isClique_comap_iff (G : Graph Role Vertex) (e : Vertex' ≃ Vertex)
    (r : Role) (D : Set Vertex') :
    ((G.comap e).component r).IsClique D ↔ (G.component r).IsClique (e '' D) := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨hxy, (h hx hy (fun he => hxy (congrArg e he))).2⟩
  · intro h x hx y hy hxy
    exact ⟨hxy, (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (e.injective.ne hxy)).2⟩

/-- Maximal monochromatic cliques are unchanged by an equivalence of vertices. -/
theorem Graph.maxClique_comap_iff (G : Graph Role Vertex) (e : Vertex' ≃ Vertex)
    (A : Set Vertex) (r : Role) (D : Set Vertex') :
    (G.comap e).MaxClique (e ⁻¹' A) r D ↔ G.MaxClique A r (e '' D) := by
  constructor
  · rintro ⟨⟨hDA, hD⟩, hmax⟩
    refine ⟨⟨?_, (G.isClique_comap_iff e r D).mp hD⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hDA hx
    · intro E hE hDE y hy
      let E' := e ⁻¹' E
      have hc : ((G.comap e).component r).IsClique E' := by
        intro x hx z hz hxz
        exact ⟨hxz, (hE.2 hx hz (e.injective.ne hxz)).2⟩
      have hED : E' ⊆ D := hmax ⟨fun _ hx => hE.1 hx, hc⟩
        (fun x hx => hDE ⟨x, hx, rfl⟩)
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, hED hy, rfl⟩
  · rintro ⟨⟨hDA, hD⟩, hmax⟩
    refine ⟨⟨fun x hx => hDA ⟨x, hx, rfl⟩,
      (G.isClique_comap_iff e r D).mpr hD⟩, ?_⟩
    intro E hE hDE x hx
    have hED : e '' E ⊆ e '' D := hmax
      ⟨by rintro _ ⟨z, hz, rfl⟩; exact hE.1 hz,
        (G.isClique_comap_iff e r E).mp hE.2⟩ (Set.image_mono hDE)
    obtain ⟨y, hy, he⟩ := hED ⟨x, hx, rfl⟩
    exact e.injective he ▸ hy

variable {Var : Type*}

/-- An injective change of vertices identifies cliques with cliques in its image. -/
theorem Graph.isClique_comap_image_iff (G : Graph Role Vertex) (f : Vertex' → Vertex)
    (hf : Function.Injective f) (r : Role) (D : Set Vertex') :
    ((G.comap f).component r).IsClique D ↔ (G.component r).IsClique (f '' D) := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨hxy, (h hx hy (fun he => hxy (congrArg f he))).2⟩
  · intro h x hx y hy hxy
    exact ⟨hxy, (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (hf.ne hxy)).2⟩

/-- Maximality is relative to the image region, so injectivity suffices. -/
theorem Graph.maxClique_comap_image_iff (G : Graph Role Vertex) (f : Vertex' → Vertex)
    (hf : Function.Injective f) (A : Set Vertex') (r : Role) (D : Set Vertex') :
    (G.comap f).MaxClique A r D ↔ G.MaxClique (f '' A) r (f '' D) := by
  constructor
  · rintro ⟨⟨hDA, hD⟩, hmax⟩
    refine ⟨⟨Set.image_mono hDA, (G.isClique_comap_image_iff f hf r D).mp hD⟩, ?_⟩
    intro E hE hDE y hy
    have hEA : f ⁻¹' E ⊆ A := by
      intro x hx
      obtain ⟨z, hz, he⟩ := hE.1 hx
      exact hf he ▸ hz
    have hc : ((G.comap f).component r).IsClique (f ⁻¹' E) := by
      intro x hx z hz hxz
      exact ⟨hxz, (hE.2 hx hz (hf.ne hxz)).2⟩
    have hED : f ⁻¹' E ⊆ D := hmax ⟨hEA, hc⟩ (fun x hx => hDE ⟨x, hx, rfl⟩)
    obtain ⟨x, _, rfl⟩ := hE.1 hy
    exact ⟨x, hED hy, rfl⟩
  · rintro ⟨⟨hDA, hD⟩, hmax⟩
    refine ⟨⟨?_, (G.isClique_comap_image_iff f hf r D).mpr hD⟩, ?_⟩
    · intro x hx
      obtain ⟨z, hz, he⟩ := hDA ⟨x, hx, rfl⟩
      exact hf he ▸ hz
    · intro E hE hDE x hx
      have hED : f '' E ⊆ f '' D := hmax
        ⟨Set.image_mono hE.1, (G.isClique_comap_image_iff f hf r E).mp hE.2⟩
        (Set.image_mono hDE)
      obtain ⟨z, hz, he⟩ := hED ⟨x, hx, rfl⟩
      exact hf he ▸ hz

/-- Blocking transports along an injection when the labels agree on its image. -/
theorem Graph.blocks_comap_image_iff (G : Graph Role Vertex) (f : Vertex' → Vertex)
    (hf : Function.Injective f) (A : Set Vertex') (label : Vertex → Var)
    (label' : Vertex' → Var) (hlabel : ∀ x, label (f x) = label' x)
    (v : Var → WinnerSet Role) (r : Role) :
    (G.comap f).Blocks A label' v r ↔ G.Blocks (f '' A) label v r := by
  constructor
  · intro h D hD
    have himage : f '' (f ⁻¹' D) = D :=
      Set.image_preimage_eq_of_subset (hD.1.1.trans (Set.image_subset_range f A))
    have hm : (G.comap f).MaxClique A r (f ⁻¹' D) :=
      (G.maxClique_comap_image_iff f hf A r _).mpr (by simpa only [himage] using hD)
    obtain ⟨x, hx, he⟩ := h _ hm
    exact ⟨f x, hx, by simpa only [hlabel] using he⟩
  · intro h D hD
    obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := h _
      ((G.maxClique_comap_image_iff f hf A r D).mp hD)
    exact ⟨x, hx, by simpa only [hlabel] using he⟩

/-- The source formula transports to any injectively renamed occurrence region. -/
theorem Graph.wins_comap_image_iff (G : Graph Role Vertex) (f : Vertex' → Vertex)
    (hf : Function.Injective f) (A : Set Vertex') (label : Vertex → Var)
    (label' : Vertex' → Var) (hlabel : ∀ x, label (f x) = label' x)
    (v : Var → WinnerSet Role) (k : Role) :
    (G.comap f).Wins A label' v k ↔ G.Wins (f '' A) label v k := by
  constructor
  · rintro ⟨x, hx, hk, hcliques⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, by simpa only [hlabel] using hk, ?_⟩
    intro r hr
    obtain ⟨D, hD, hxD, havoid⟩ := hcliques r hr
    refine ⟨f '' D, (G.maxClique_comap_image_iff f hf A r D).mp hD,
      ⟨x, hxD, rfl⟩, ?_⟩
    intro y hy hne
    obtain ⟨z, hz, rfl⟩ := hy
    simpa only [hlabel] using havoid z hz (fun he => hne (congrArg f he))
  · rintro ⟨_, ⟨x, hx, rfl⟩, hk, hcliques⟩
    refine ⟨x, hx, by simpa only [hlabel] using hk, ?_⟩
    intro r hr
    obtain ⟨D, hD, hxD, havoid⟩ := hcliques r hr
    have himage : f '' (f ⁻¹' D) = D :=
      Set.image_preimage_eq_of_subset (hD.1.1.trans (Set.image_subset_range f A))
    refine ⟨f ⁻¹' D,
      (G.maxClique_comap_image_iff f hf A r _).mpr (by simpa only [himage] using hD),
      hxD, ?_⟩
    intro z hz hne
    simpa only [hlabel] using havoid (f z) hz (hf.ne hne)

/-- Blocking all maximal cliques is invariant under renaming the vertices. -/
theorem Graph.blocks_comap_iff (G : Graph Role Vertex) (e : Vertex' ≃ Vertex)
    (A : Set Vertex) (label : Vertex → Var) (v : Var → WinnerSet Role) (r : Role) :
    (G.comap e).Blocks (e ⁻¹' A) (label ∘ e) v r ↔ G.Blocks A label v r := by
  constructor
  · intro h D hD
    have hm : (G.comap e).MaxClique (e ⁻¹' A) r (e ⁻¹' D) :=
      (G.maxClique_comap_iff e A r _).mpr (by simpa only [e.image_preimage] using hD)
    obtain ⟨x, hx, he⟩ := h _ hm
    exact ⟨e x, hx, he⟩
  · intro h D hD
    obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := h _ ((G.maxClique_comap_iff e A r D).mp hD)
    exact ⟨x, hx, he⟩

/-- The clique source formula depends only on the colored graph and its labels,
not on the names chosen for its vertices. -/
theorem Graph.wins_comap_iff (G : Graph Role Vertex) (e : Vertex' ≃ Vertex)
    (A : Set Vertex) (label : Vertex → Var) (v : Var → WinnerSet Role) (k : Role) :
    (G.comap e).Wins (e ⁻¹' A) (label ∘ e) v k ↔ G.Wins A label v k := by
  constructor
  · rintro ⟨x, hx, hk, hcliques⟩
    refine ⟨e x, hx, hk, ?_⟩
    intro r hr
    obtain ⟨D, hD, hxD, havoid⟩ := hcliques r hr
    refine ⟨e '' D, (G.maxClique_comap_iff e A r D).mp hD, ⟨x, hxD, rfl⟩, ?_⟩
    intro y hy hne
    obtain ⟨z, hz, rfl⟩ := hy
    exact havoid z hz (fun he => hne (congrArg e he))
  · rintro ⟨y, hy, hk, hcliques⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, hy, hk, ?_⟩
    intro r hr
    obtain ⟨D, hD, hxD, havoid⟩ := hcliques r hr
    refine ⟨e ⁻¹' D,
      (G.maxClique_comap_iff e A r _).mpr (by simpa only [e.image_preimage] using hD),
      hxD, ?_⟩
    intro z hz hne
    exact havoid (e z) hz (e.injective.ne hne)

end KFOL.Core.ColoredGraph
