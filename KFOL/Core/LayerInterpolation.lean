module

public import KFOL.Definitions.LayerInterpolation
public import KFOL.Core.CompletionDepthStep
public import KFOL.Algebra.Atomic.CoreSupport

/-! # Exact row interpolation at bounded completion depth -/

@[expose] public section

namespace KFOL.Core.Interpolation

open CompletionDepth

universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}
variable [DecidableEq Row] [DecidableEq Role]

omit [DecidableEq Role] [DecidableEq Row] in
private theorem profileCondition_mono
    {P Q : Finset (Row × Role) → Option (Row × Role) → Prop}
    (h : ∀ E o, P E o → Q E o) {D p} (hp : ProfileCondition P D p) :
    ProfileCondition Q D p := by
  refine ⟨fun S hS hr => h _ _ (hp.1 S hS hr), ?_⟩
  cases p with
  | none => trivial
  | some qk =>
    obtain ⟨q, k⟩ := qk
    obtain ⟨hpos, hother⟩ := hp.2
    refine ⟨h _ _ hpos, fun d hd hdk => ?_⟩
    obtain ⟨s, hs, hw⟩ := hother d hd hdk
    exact ⟨s, hs, h _ _ hw⟩

omit [DecidableEq Role] [DecidableEq Row] in
private theorem fits_left_or_right {N : Finset Row} {U : Row → Set Role} {D p}
    (x y : Row → WinnerSet Role) (h : Fits N U D p (fun i => (x i).union (y i))) :
    Fits N U D p x ∨ Fits N U D p y := by
  have hx : Bounded N U x := fun i hi _ hk => h.1 i hi (Or.inl hk)
  have hy : Bounded N U y := fun i hi _ hk => h.1 i hi (Or.inr hk)
  have hat (d) (hd : d ∈ D) := (WinnerSet.union_eq_singleton_iff _ _ _).mp (h.2.1 d hd)
  have hD := And.intro (show Atomic D x from fun d hd => (hat d hd).1)
    (show Atomic D y from fun d hd => (hat d hd).2)
  cases p with
  | none => exact Or.inl ⟨hx, hD.1, trivial⟩
  | some qk =>
    obtain ⟨q, k⟩ := qk
    have hk : k ∈ (x q).val ∨ k ∈ (y q).val := h.2.2
    exact hk.imp (fun hq => ⟨hx, hD.1, hq⟩) (fun hq => ⟨hy, hD.2, hq⟩)

private theorem layerFits_of_input (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role) (j : Var) (d : ℕ)
    {N D p} (h : Fits N U D p (fun i => values i j)) : LayerFits values U d N D p := by
  induction d generalizing N D p with
  | zero => exact ⟨j, h⟩
  | succ d ih =>
    refine ⟨∅, Finset.empty_subset _, fun _ => three 0, by simp, ?_⟩
    simp only [Finset.sdiff_empty, Finset.image_empty, Finset.union_empty]
    refine ⟨fun S hS _ => ih ⟨h.1, fun e he => h.2.1 e (hS he), trivial⟩, ?_⟩
    cases p with
    | none => trivial
    | some qk =>
      obtain ⟨q, k⟩ := qk
      refine ⟨ih ⟨h.1, by simp [Atomic], h.2.2⟩, ?_⟩
      intro e he hne
      exact ⟨k, hne.symm, ih ⟨h.1, fun f hf => Finset.mem_singleton.mp hf ▸ h.2.1 e he, h.2.2⟩⟩

variable [Fintype Role]

private theorem layerFits_of_expr (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role) (e : Expr Role Var)
    (d : ℕ) {N D p} (hd : e.depth ≤ d) (hf : Fits N U D p (fun i => e.eval (values i))) :
    LayerFits values U d N D p := by
  classical
  induction e generalizing d N D p with
  | var j => exact layerFits_of_input three values U j d hf
  | union x y hx hy =>
    obtain h | h := fits_left_or_right (fun i => x.eval (values i)) (fun i => y.eval (values i)) hf
    · exact hx _ ((le_max_left _ _).trans hd) h
    · exact hy _ ((le_max_right _ _).trans hd) h
  | @gate n g args ih =>
    cases d with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hd)
    | succ d =>
      let cols (i : Row) (j : Fin (n + 1)) := (args j).eval (values i)
      let out (i : Row) := g.eval (cols i)
      let B := N.filter (fun i => ∃ r, out i = WinnerSet.singleton r)
      let owner (i : Row) := if h : ∃ r, out i = WinnerSet.singleton r then h.choose else three 0
      have hat (i : Row) (hi : i ∈ B) : out i = WinnerSet.singleton (owner i) := by
        have h := (Finset.mem_filter.mp hi).2
        simpa only [owner, dite_eq_left h] using h.choose_spec
      have hN (j) : Bounded (N \ B) U (fun i => cols i j) := by
        intro i hi k hk
        obtain ⟨hiN, hiB⟩ := Finset.mem_sdiff.mp hi
        have hamb : (out i).Ambiguous :=
          fun r hr => hiB (Finset.mem_filter.mpr ⟨hiN, r, hr⟩)
        apply hf.1 i hiN
        change k ∈ (g.eval (cols i)).val
        rw [g.union_of_ambiguous _ hamb]
        exact Set.mem_iUnion.mpr ⟨j, hk⟩
      refine ⟨B, Finset.filter_subset _ _, owner, ?_, ?_⟩
      · intro i hi
        apply hf.1 i (Finset.mem_filter.mp hi).1
        change owner i ∈ (out i).val
        rw [hat i hi]
        rfl
      · apply profileCondition_mono (P := fun E o => ∃ j,
          Atomic E (fun i => cols i j) ∧ Positive o (fun i => cols i j))
        · rintro E o ⟨j, hD, hp⟩
          apply ih j d _ ⟨hN j, hD, hp⟩
          exact (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j)).trans
            (Nat.le_of_succ_le_succ hd)
        · apply (exists_gate_iff_profileCondition three cols _ p).mp
          refine ⟨g, ?_, hf.2.2⟩
          intro a ha
          rcases Finset.mem_union.mp ha with hD | hB
          · exact hf.2.1 _ hD
          · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
            exact hat i hi

private theorem gate_bounded (three : Fin 3 ↪ Role) {n : ℕ} (g : Gate Role n)
    (cols : Fin (n + 1) → WinnerSet Role) (U : Set Role) (h : ∀ j, (cols j).val ⊆ U) :
    (g.eval cols).val ⊆ U := by
  classical
  obtain ⟨t, ht⟩ := g.exists_core three
  rw [← ht, ← Equational.Core.eval_decode]
  exact (Equational.Core.isCore_decode t).eval_subset_of_support cols U (fun j _ => h j)

/-- The row test at layer count \(d\) is exact, including expressions with
arbitrarily many free unions and arbitrary finite positive gate arities. -/
theorem layerFits_iff_exists_expr [Fintype Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role) (d : ℕ)
    (N : Finset Row) (D : Finset (Row × Role)) (p : Option (Row × Role)) :
    LayerFits values U d N D p ↔
      ∃ e : Expr Role Var, e.depth ≤ d ∧ Fits N U D p (fun i => e.eval (values i)) := by
  classical
  refine ⟨?_, fun ⟨e, hd, hf⟩ => layerFits_of_expr three values U e d hd hf⟩
  induction d generalizing N D p with
  | zero =>
    rintro ⟨j, hj⟩
    exact ⟨.var j, Nat.le_refl _, hj⟩
  | succ d ih =>
    rintro ⟨B, hBN, owner, hallowed, hprof⟩
    let reachable (x : Row → WinnerSet Role) := ∃ e : Expr Role Var,
      e.depth ≤ d ∧ (fun i => e.eval (values i)) = x ∧ Bounded (N \ B) U x
    let Port := {x : Row → WinnerSet Role // reachable x}
    have findPort {E o} (h : LayerFits values U d (N \ B) E o) :
        ∃ a : Port, Atomic E a.val ∧ Positive o a.val := by
      obtain ⟨e, hd, hfit⟩ := ih _ _ _ h
      exact ⟨⟨_, e, hd, rfl, hfit.1⟩, hfit.2⟩
    have hPort : Nonempty Port := by
      obtain ⟨a, _⟩ := findPort (hprof.1 ∅ (Finset.empty_subset _) (by simp [Rainbow]))
      exact ⟨a⟩
    let _ : Fintype Port := Fintype.ofFinite Port
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hPort))
    let ports : Fin (n + 1) ≃ Port := (Fintype.equivFinOfCardEq hn).symm
    let cols (i : Row) (j : Fin (n + 1)) := (ports j).val i
    have hpcols := profileCondition_mono (Q := fun E o => ∃ j,
        Atomic E (fun i => cols i j) ∧ Positive o (fun i => cols i j)) (fun E o h => by
      obtain ⟨a, ha⟩ := findPort h
      exact ⟨ports.symm a, by simpa only [cols, Equiv.apply_symm_apply] using ha⟩) hprof
    obtain ⟨g, hat, hpos⟩ := (exists_gate_iff_profileCondition three cols _ p).mpr hpcols
    choose args hdepth heval hbound using (fun j => (ports j).property)
    have he (i) : (Expr.gate g args).eval (values i) = g.eval (cols i) := by
      apply congrArg g.eval
      exact funext fun j => congrFun (heval j) i
    refine ⟨.gate g args, Nat.succ_le_succ (Finset.sup_le fun j _ => hdepth j), ?_⟩
    simp only [he]
    refine ⟨?_, fun a ha => hat a (Finset.mem_union_left _ ha), hpos⟩
    intro i hi
    by_cases hiB : i ∈ B
    · have hsing := hat (i, owner i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hiB))
      change g.eval (cols i) = WinnerSet.singleton (owner i) at hsing
      change (g.eval (cols i)).val ⊆ U i
      rw [hsing]
      exact Set.singleton_subset_iff.mpr (hallowed i hiB)
    · exact gate_bounded three g _ _ (fun j => hbound j i (Finset.mem_sdiff.mpr ⟨hi, hiB⟩))

/-- Exact table recognition preserves the layer bound: free unions can
combine witnesses for all requested winners. -/
theorem recognizesAtDepth_iff [Fintype Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role) (d : ℕ) :
    RecognizesAtDepth values U d ↔
      ∃ e : Expr Role Var, e.depth ≤ d ∧ ∀ i, (e.eval (values i)).val = U i := by
  classical
  simp only [RecognizesAtDepth, layerFits_iff_exists_expr three, Fits, Atomic,
    Finset.notMem_empty, false_implies, implies_true, Positive, true_and, and_true]
  constructor
  · rintro ⟨hbase, hpos⟩
    let S : Finset (Row × Role) := Finset.univ.filter (fun p => p.2 ∈ U p.1)
    have join (T : Finset (Row × Role)) (hT : T ⊆ S) :
        ∃ e : Expr Role Var, e.depth ≤ d ∧ Bounded Finset.univ U (fun i => e.eval (values i)) ∧
          ∀ x ∈ T, x.2 ∈ (e.eval (values x.1)).val := by
      induction T using Finset.induction_on with
      | empty =>
        obtain ⟨e, hd, hb⟩ := hbase
        exact ⟨e, hd, hb, by simp⟩
      | @insert x T hx ih =>
        have hxS := hT (Finset.mem_insert_self x T)
        obtain ⟨e, he, hbe, hxe⟩ := hpos x.1 x.2 (Finset.mem_filter.mp hxS).2
        obtain ⟨f, hf, hbf, hT'⟩ := ih (fun _ h => hT (Finset.mem_insert_of_mem h))
        refine ⟨.union e f, max_le he hf, ?_, ?_⟩
        · intro i hi
          exact Set.union_subset (hbe i hi) (hbf i hi)
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Or.inl hxe
          · exact Or.inr (hT' y hy)
    obtain ⟨e, hd, hb, hm⟩ := join S (fun _ h => h)
    refine ⟨e, hd, fun i => Set.Subset.antisymm (hb i (Finset.mem_univ _)) ?_⟩
    intro k hk
    exact hm (i, k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  · rintro ⟨e, hd, he⟩
    have hb : Bounded Finset.univ U (fun i => e.eval (values i)) :=
      fun i _ => (he i).subset
    exact ⟨⟨e, hd, hb⟩, fun i k hk => ⟨e, hd, hb, (he i).symm ▸ hk⟩⟩

/-- At every finite arity the test reads the least permitted completion
depth of an operation from its complete value table. -/
theorem operationAtDepth_iff [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (d : ℕ) :
    RecognizesOperationAtDepth f d ↔ FeasibleAtDepth d (fun g => g = f) := by
  classical
  let _ : Fintype (WinnerSet Role) := Fintype.ofFinite (WinnerSet Role)
  unfold RecognizesOperationAtDepth
  rw [recognizesAtDepth_iff three]
  constructor
  · rintro ⟨e, hd, he⟩
    exact ⟨e, hd, funext fun v => Subtype.ext (he v)⟩
  · rintro ⟨e, hd, he⟩
    exact ⟨e, hd, fun v => congrArg Subtype.val (congrFun he v)⟩

end KFOL.Core.Interpolation
