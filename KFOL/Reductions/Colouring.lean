module

public import KFOL.Reductions.ResetUnionCorrectness
public import Mathlib.Data.Fintype.Card

/-! Native complete-graph equations separating successive role counts. -/

@[expose] public section

namespace KFOL.Reductions.Colouring

@[simp] theorem mem_edges (n : ℕ) (i j : Fin n) : (i, j) ∈ edges n ↔ i.val < j.val := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i', _, j', ⟨_, hlt⟩, he⟩
    cases he
    exact hlt
  · intro hij
    exact ⟨i, by simp, j, ⟨by simp, hij⟩, rfl⟩

/-- n atomic vertices inside a baseline over n roles leave no fresh marker
if every distinct edge is ambiguous. This is the required finite pigeonhole
argument, independent of the native term recursion. -/
theorem no_fresh_marker_of_atoms_and_edges (n : ℕ) (X : Fin n → WinnerSet (Fin n))
    (W : WinnerSet (Fin n)) (w : Fin n) (hw : w ∉ W.val)
    (hX : ∀ i, (X i).val ⊆ W.val) (hatom : ∀ i, ¬(X i).Ambiguous)
    (hedge : ∀ i j, i ≠ j → ((X i).union (X j)).Ambiguous) : False := by
  classical
  have hex : ∀ i, ∃ r, X i = WinnerSet.singleton r := by
    intro i
    have hi := hatom i
    unfold WinnerSet.Ambiguous at hi
    push Not at hi
    exact hi
  let f : Fin n → Fin n := fun i => Classical.choose (hex i)
  have hf : ∀ i, X i = WinnerSet.singleton (f i) := fun i => Classical.choose_spec (hex i)
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hne
    have hm := hedge i j hne
    rw [hf i, hf j, he, WinnerSet.union_self] at hm
    exact hm (f j) rfl
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj w
  apply hw
  apply hX i
  rw [hf i, hi]
  rfl

end KFOL.Reductions.Colouring

namespace KFOL.Reductions.Colouring

universe u

private theorem mem_baseline {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role)
    (hz : (v 0).Ambiguous) (w : Role) :
    w ∈ ((baseline n).eval v).val ↔ w ∈ (v 0).val ∨ ∃ i : Fin n, w ∈ (v (vertexName n i)).val := by
  rw [baseline, KFOL.ResetUnion.Term.eval_rightComb, KFOL.ResetUnion.Term.eval_var,
    WinnerSetFold.mem_right _ _ hz]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨_, ⟨i, _, rfl⟩, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, h⟩
  · rintro (h | ⟨i, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨_, ⟨i, by simp, rfl⟩, rfl⟩, h⟩

private theorem vertex_subset_baseline {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role)
    (hz : (v 0).Ambiguous) (i : Fin n) : (v (vertexName n i)).val ⊆ ((baseline n).eval v).val :=
  fun _ h => (mem_baseline n v hz _).mpr (Or.inr ⟨i, h⟩)

private theorem baseline_ambiguous {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role) :
    ((baseline n).eval v).Ambiguous ↔ (v 0).Ambiguous := by
  rw [baseline, KFOL.ResetUnion.Term.eval_rightComb, WinnerSetFold.ambiguous_right, KFOL.ResetUnion.Term.eval_var]

private theorem right_ambiguous {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role) :
    ((right n).eval v).Ambiguous ↔ (v 0).Ambiguous := by
  rw [right, KFOL.ResetUnion.Term.eval_rightComb, WinnerSetFold.ambiguous_right, baseline_ambiguous]

private theorem baseline_subset_right {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role)
    (hz : (v 0).Ambiguous) : ((baseline n).eval v).val ⊆ ((right n).eval v).val := by
  intro w hw
  rw [right, KFOL.ResetUnion.Term.eval_rightComb,
    WinnerSetFold.mem_right _ _ ((baseline_ambiguous n v).mpr hz)]
  exact Or.inl hw

private theorem left_marker {Role : Type u} (n : ℕ) (v : Fin (n + 2) → WinnerSet Role)
    (hz : (v 0).Ambiguous) (w : Role) (hw : w ∉ ((baseline n).eval v).val) :
    w ∈ ((left n).eval v).val ↔ w ∈ (v 1).val ∧
      ∀ edge ∈ edges n, ((v (vertexName n edge.1)).union (v (vertexName n edge.2))).Ambiguous := by
  rw [left, KFOL.ResetUnion.Term.eval_leftComb]
  have hsub : ∀ X ∈ (((edges n).map (fun edge => KFOL.ResetUnion.Term.union
      (.var (vertexName n edge.1)) (.var (vertexName n edge.2)))).map (fun t => t.eval v)),
      X.val ⊆ ((baseline n).eval v).val := by
    intro X hX
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp ht
    exact Set.union_subset (vertex_subset_baseline n v hz edge.1) (vertex_subset_baseline n v hz edge.2)
  simpa only [KFOL.ResetUnion.Term.eval_var, List.forall_mem_map, KFOL.ResetUnion.Term.eval_union] using
    WinnerSetFold.mem_left_outside _ _ ((baseline n).eval v).val w hw hsub

/-- The complete-graph equation on n vertices is valid on exactly n roles,
with arbitrary nonempty winner-set valuations. -/
theorem equation_holds_fin (n : ℕ) :
    letI := KFOL.ResetUnion.structureOf (Role := Fin n)
    (equation n).Holds (WinnerSet (Fin n)) := by
  change ∀ v : Fin (n + 2) → WinnerSet (Fin n),
    (KFOL.ResetUnion.Term.reset (left n) (right n)).eval v = (right n).eval v
  intro v
  rw [KFOL.ResetUnion.Term.eval_reset]
  classical
  by_cases hz : (v 0).Ambiguous
  · apply Subtype.ext
    ext w
    rw [WinnerSet.mem_reset]
    simp only [(right_ambiguous n v).mpr hz, true_and]
    constructor
    · rintro (hR | hA)
      · exact hR
      · by_cases hw : w ∈ ((baseline n).eval v).val
        · exact baseline_subset_right n v hz hw
        · obtain ⟨hC, hguard⟩ := (left_marker n v hz w hw).mp hA
          by_cases hm : ∃ i : Fin n, (v (vertexName n i)).Ambiguous
          · obtain ⟨i, hi⟩ := hm
            rw [right, KFOL.ResetUnion.Term.eval_rightComb,
              WinnerSetFold.mem_right _ _ ((baseline_ambiguous n v).mpr hz)]
            refine Or.inr ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨i, by simp, rfl⟩, rfl⟩, ?_⟩
            rw [KFOL.ResetUnion.Term.eval_reset, KFOL.ResetUnion.Term.eval_var,
              KFOL.ResetUnion.Term.eval_var, WinnerSet.mem_reset]
            exact Or.inr ⟨hi, hC⟩
          · apply False.elim
            apply no_fresh_marker_of_atoms_and_edges n (fun i => v (vertexName n i))
              ((baseline n).eval v) w hw (fun i => vertex_subset_baseline n v hz i)
              (fun i hi => hm ⟨i, hi⟩)
            intro i j hne
            by_cases hij : i.val < j.val
            · exact hguard (i, j) ((mem_edges n i j).mpr hij)
            · have hji : j.val < i.val := by
                have hnval : i.val ≠ j.val := fun he => hne (Fin.ext he)
                omega
              simpa only [WinnerSet.union_comm] using hguard (j, i) ((mem_edges n j i).mpr hji)
    · exact Or.inl
  · unfold WinnerSet.Ambiguous at hz
    push Not at hz
    obtain ⟨r, hr⟩ := hz
    have hbase : (baseline n).eval v = WinnerSet.singleton r := by
      rw [baseline, KFOL.ResetUnion.Term.eval_rightComb, KFOL.ResetUnion.Term.eval_var, hr]
      exact WinnerSetFold.right_singleton _ r
    have hR : (right n).eval v = WinnerSet.singleton r := by
      rw [right, KFOL.ResetUnion.Term.eval_rightComb, hbase]
      exact WinnerSetFold.right_singleton _ r
    rw [hR, WinnerSet.reset_singleton]

end KFOL.Reductions.Colouring

namespace KFOL.Reductions.Colouring

theorem vertexName_injective (n : ℕ) : Function.Injective (vertexName n) := by
  intro i j he
  apply Fin.ext
  have h := congrArg Fin.val he
  change i.val + 2 = j.val + 2 at h
  omega

@[simp] theorem successorValuation_vertex (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    successorValuation n hn (vertexName n i) = WinnerSet.singleton i.castSucc :=
  (vertexName_injective n).extend_apply _ _ i

@[simp] theorem successorValuation_zero (n : ℕ) (hn : 2 ≤ n) :
    successorValuation n hn 0 =
      (WinnerSet.singleton ⟨0, by omega⟩).union (WinnerSet.singleton ⟨1, by omega⟩) := by
  rw [successorValuation, Function.extend_apply']
  · simp
  · rintro ⟨i, he⟩
    have h := congrArg Fin.val he
    change i.val + 2 = 0 at h
    omega

@[simp] theorem successorValuation_one (n : ℕ) (hn : 2 ≤ n) :
    successorValuation n hn 1 = WinnerSet.singleton (Fin.last n) := by
  have h10 : (1 : Fin (n + 2)) ≠ 0 := by
    intro he
    have h := congrArg Fin.val he
    change 1 % (n + 2) = 0 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  rw [successorValuation, Function.extend_apply']
  · simp only [h10, ite_false]
  · rintro ⟨i, he⟩
    have h := congrArg Fin.val he
    change i.val + 2 = 1 % (n + 2) at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- Explicit fresh-marker separation on n+1 roles by the same finite-arity
native equation that holds on n roles. -/
theorem successor_separates (n : ℕ) (hn : 2 ≤ n) :
    let v := successorValuation n hn
    Fin.last n ∈ ((KFOL.ResetUnion.Term.reset (left n) (right n)).eval v).val ∧
      Fin.last n ∉ ((right n).eval v).val := by
  let v := successorValuation n hn
  have hz : (v 0).Ambiguous := by
    rw [show v 0 = _ from successorValuation_zero n hn]
    apply WinnerSet.ambiguous_of_two_mem _ ⟨0, by omega⟩ ⟨1, by omega⟩
    · intro he
      have h := congrArg Fin.val he
      simp only at h
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hvertex (i : Fin n) : Fin.last n ∉ (v (vertexName n i)).val := by
    rw [show v (vertexName n i) = _ from successorValuation_vertex n hn i]
    intro he
    have h := congrArg Fin.val (Set.mem_singleton_iff.mp he)
    change n = i.val at h
    omega
  have hw : Fin.last n ∉ ((baseline n).eval v).val := by
    rw [mem_baseline n v hz]
    rintro (h | ⟨i, hi⟩)
    · rw [show v 0 = _ from successorValuation_zero n hn] at h
      rcases h with h | h
      · have he := congrArg Fin.val (Set.mem_singleton_iff.mp h)
        change n = 0 at he
        omega
      · have he := congrArg Fin.val (Set.mem_singleton_iff.mp h)
        change n = 1 at he
        omega
    · exact hvertex i hi
  have hR : Fin.last n ∉ ((right n).eval v).val := by
    rw [right, KFOL.ResetUnion.Term.eval_rightComb,
      WinnerSetFold.mem_right _ _ ((baseline_ambiguous n v).mpr hz)]
    rintro (h | ⟨X, hX, h⟩)
    · exact hw h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      rw [KFOL.ResetUnion.Term.eval_reset, KFOL.ResetUnion.Term.eval_var,
        KFOL.ResetUnion.Term.eval_var, show v (vertexName n i) = _ from successorValuation_vertex n hn i,
        WinnerSet.reset_singleton] at h
      apply hvertex i
      rw [show v (vertexName n i) = _ from successorValuation_vertex n hn i]
      exact h
  have hA : Fin.last n ∈ ((left n).eval v).val := by
    apply (left_marker n v hz (Fin.last n) hw).mpr
    refine ⟨?_, ?_⟩
    · rw [show v 1 = _ from successorValuation_one n hn]
      rfl
    · intro edge he
      have hij := (mem_edges n edge.1 edge.2).mp he
      rw [show v (vertexName n edge.1) = _ from successorValuation_vertex n hn edge.1,
        show v (vertexName n edge.2) = _ from successorValuation_vertex n hn edge.2]
      apply WinnerSet.ambiguous_of_two_mem _ edge.1.castSucc edge.2.castSucc
      · intro heq
        have hv := congrArg Fin.val heq
        change edge.1.val = edge.2.val at hv
        omega
      · exact Or.inl rfl
      · exact Or.inr rfl
  refine ⟨?_, hR⟩
  rw [KFOL.ResetUnion.Term.eval_reset, WinnerSet.mem_reset]
  exact Or.inr ⟨(right_ambiguous n v).mpr hz, hA⟩

/-- The literal finite-arity identity fails at the next role count. -/
theorem not_equation_holds_fin_succ (n : ℕ) (hn : 2 ≤ n) :
    letI := KFOL.ResetUnion.structureOf (Role := Fin (n + 1))
    ¬(equation n).Holds (WinnerSet (Fin (n + 1))) := by
  change ¬∀ v : Fin (n + 2) → WinnerSet (Fin (n + 1)),
    (KFOL.ResetUnion.Term.reset (left n) (right n)).eval v = (right n).eval v
  intro h
  obtain ⟨hl, hr⟩ := successor_separates n hn
  exact hr (h _ ▸ hl)

end KFOL.Reductions.Colouring

namespace KFOL.Reductions.Colouring

universe u v

@[simp] theorem embedWinnerSet_singleton {Role : Type u} {Role' : Type v}
    (f : Role ↪ Role') (r : Role) : embedWinnerSet f (WinnerSet.singleton r) = WinnerSet.singleton (f r) := by
  apply Subtype.ext
  exact Set.image_singleton

theorem embedWinnerSet_injective {Role : Type u} {Role' : Type v} (f : Role ↪ Role') :
    Function.Injective (embedWinnerSet f) := by
  intro A B he
  apply Subtype.ext
  exact Set.image_injective.mpr f.injective (congrArg Subtype.val he)

@[simp] theorem embedWinnerSet_union {Role : Type u} {Role' : Type v} (f : Role ↪ Role')
    (A B : WinnerSet Role) : embedWinnerSet f (A.union B) = (embedWinnerSet f A).union (embedWinnerSet f B) := by
  apply Subtype.ext
  exact Set.image_union _ _ _

@[simp] theorem embedWinnerSet_ambiguous {Role : Type u} {Role' : Type v} (f : Role ↪ Role')
    (A : WinnerSet Role) : (embedWinnerSet f A).Ambiguous ↔ A.Ambiguous := by
  constructor
  · intro h r he
    apply h (f r)
    rw [he, embedWinnerSet_singleton]
  · intro hA r he
    obtain ⟨x, hx⟩ := A.property
    have hfx : f x = r := by
      have hi : f x ∈ (embedWinnerSet f A).val := ⟨x, hx, rfl⟩
      rw [he] at hi
      exact Set.mem_singleton_iff.mp hi
    apply hA x
    apply WinnerSet.eq_singleton_of_subset
    intro y hy
    have hfy : f y = r := by
      have hi : f y ∈ (embedWinnerSet f A).val := ⟨y, hy, rfl⟩
      rw [he] at hi
      exact Set.mem_singleton_iff.mp hi
    exact f.injective (hfy.trans hfx.symm)

@[simp] theorem embedWinnerSet_reset {Role : Type u} {Role' : Type v} (f : Role ↪ Role')
    (A B : WinnerSet Role) : embedWinnerSet f (A.reset B) = (embedWinnerSet f A).reset (embedWinnerSet f B) := by
  classical
  by_cases hB : B.Ambiguous
  · rw [WinnerSet.reset_of_ambiguous _ _ hB, WinnerSet.reset_of_ambiguous _ _
      ((embedWinnerSet_ambiguous f B).mpr hB), embedWinnerSet_union]
  · have hB' : ¬(embedWinnerSet f B).Ambiguous := fun h => hB ((embedWinnerSet_ambiguous f B).mp h)
    simp only [WinnerSet.reset, hB, hB', ite_false]

theorem eval_embedWinnerSet {Role : Type u} {Role' : Type v} {Var : Type*} (f : Role ↪ Role')
    (t : KFOL.ResetUnion.Term Var) (valuation : Var → WinnerSet Role) :
    embedWinnerSet f (t.eval valuation) = t.eval (fun j => embedWinnerSet f (valuation j)) := by
  induction t with
  | var => rfl
  | @func n symbol args ih =>
    cases symbol
    · change embedWinnerSet f ((KFOL.ResetUnion.Term.eval (args 0) valuation).reset
        (KFOL.ResetUnion.Term.eval (args 1) valuation)) =
        (KFOL.ResetUnion.Term.eval (args 0) (fun j => embedWinnerSet f (valuation j))).reset
          (KFOL.ResetUnion.Term.eval (args 1) (fun j => embedWinnerSet f (valuation j)))
      rw [embedWinnerSet_reset, ih 0, ih 1]
    · change embedWinnerSet f ((KFOL.ResetUnion.Term.eval (args 0) valuation).union
        (KFOL.ResetUnion.Term.eval (args 1) valuation)) =
        (KFOL.ResetUnion.Term.eval (args 0) (fun j => embedWinnerSet f (valuation j))).union
          (KFOL.ResetUnion.Term.eval (args 1) (fun j => embedWinnerSet f (valuation j)))
      rw [embedWinnerSet_union, ih 0, ih 1]

/-- Every identity on a larger role carrier holds on the embedded smaller
carrier. The operation preservation is proved on all nonempty sets. -/
theorem holds_of_role_embedding {Role : Type u} {Role' : Type v} (f : Role ↪ Role')
    (e : Equational.Identity KFOL.ResetUnion.Symbol)
    (he : letI := KFOL.ResetUnion.structureOf (Role := Role'); e.Holds (WinnerSet Role')) :
    letI := KFOL.ResetUnion.structureOf (Role := Role)
    e.Holds (WinnerSet Role) := by
  change ∀ valuation : Fin e.arity → WinnerSet Role,
    KFOL.ResetUnion.Term.eval e.lhs valuation = KFOL.ResetUnion.Term.eval e.rhs valuation
  intro valuation
  apply embedWinnerSet_injective f
  rw [eval_embedWinnerSet, eval_embedWinnerSet]
  exact he (fun j => embedWinnerSet f (valuation j))

/-- The complete reset/union identity theories strictly decrease at each
successive role count. The finite-arity witness is the native graph equation. -/
theorem theory_succ_ssubset (n : ℕ) (hn : 3 ≤ n) :
    {e : Equational.Identity KFOL.ResetUnion.Symbol |
      letI := KFOL.ResetUnion.structureOf (Role := Fin (n + 1)); e.Holds (WinnerSet (Fin (n + 1)))} ⊂
    {e : Equational.Identity KFOL.ResetUnion.Symbol |
      letI := KFOL.ResetUnion.structureOf (Role := Fin n); e.Holds (WinnerSet (Fin n))} := by
  rw [Set.ssubset_def]
  constructor
  · intro e he
    exact holds_of_role_embedding ⟨Fin.castSucc, Fin.castSucc_injective n⟩ e he
  · intro hreverse
    have hlarge := hreverse (equation_holds_fin n)
    exact not_equation_holds_fin_succ n (by omega) hlarge

end KFOL.Reductions.Colouring
