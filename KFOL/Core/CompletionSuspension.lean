module

public import KFOL.Core.CompletionDepthErasure
public import KFOL.Core.SingletonProfileAbsorption
public import KFOL.Definitions.Views

/-! # Suspension raises minimum completion depth by one -/

@[expose] public section
namespace KFOL.Core.CompletionDepth
universe u v
variable {Role : Type u} {Var : Type v}
attribute [local instance] Equational.coreStructure

private def liftExpr : Expr Role Var → Expr Role (Var ⊕ Unit)
  | .var j => .var (.inl j)
  | .union e f => .union (liftExpr e) (liftExpr f)
  | .gate g args => .gate g (fun j => liftExpr (args j))

private theorem liftExpr_eval (e : Expr Role Var) (v : Var ⊕ Unit → WinnerSet Role) :
    (liftExpr e).eval v = e.eval (fun j => v (.inl j)) := by
  induction e with
  | var => rfl
  | union e f he hf => exact congrArg₂ WinnerSet.union he hf
  | gate g args ih => exact congrArg g.eval (funext ih)

private theorem liftExpr_depth (e : Expr Role Var) : (liftExpr e).depth = e.depth := by
  induction e with
  | var => rfl
  | union e f he hf => exact congrArg₂ max he hf
  | gate g args ih => simp only [liftExpr, Expr.depth, ih]

open Classical in
private theorem exists_cap_gate [Fintype Role] (three : Fin 3 ↪ Role) (b c : Role) :
    ∃ g : Gate Role 1, ∀ x : Fin 2 → WinnerSet Role,
      g.eval x = if x 1 = WinnerSet.singleton b ∨ x 1 = WinnerSet.singleton c then x 1
        else (x 0).union (x 1) := by
  classical
  let F (r : Role) (A : Fin 2 → Bool) := if r = b ∨ r = c then A 1 else A 0 && A 1
  have had : AdmissibleProfiles F := by
    constructor
    · intro r A B h hA
      by_cases hr : r = b ∨ r = c <;> simp [F, hr] at hA ⊢
      · exact h 1 hA
      · exact ⟨h 0 hA.1, h 1 hA.2⟩
    · intro r; simp [F]
    · intro A hA
      refine ⟨1, fun r => ?_⟩
      by_cases hr : r = b ∨ r = c
      · simpa [F, hr] using hA r
      · have h := hA r; simp [F, hr] at h; exact h.2
  obtain ⟨g, hg⟩ := Gate.exists_of_admissible three F had
  refine ⟨g, fun x => ?_⟩
  have special (r : Role) (hr : r = b ∨ r = c) :
      g.eval x = WinnerSet.singleton r ↔ x 1 = WinnerSet.singleton r := by
    rw [g.singleton_iff, hg]; simp [F, hr, ProfileBounds.atomicBits]
  by_cases h : x 1 = WinnerSet.singleton b ∨ x 1 = WinnerSet.singleton c
  · rw [ite_eq_left h]
    rcases h with hb | hc
    · exact ((special b (Or.inl rfl)).2 hb).trans hb.symm
    · exact ((special c (Or.inr rfl)).2 hc).trans hc.symm
  · rw [ite_eq_right h]
    by_cases ha : (g.eval x).Ambiguous
    · apply Subtype.ext
      rw [g.union_of_ambiguous x ha]
      ext k
      simp only [Set.mem_iUnion, WinnerSet.val_union, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩; fin_cases i <;> tauto
      · exact fun hh => hh.elim (fun h0 => ⟨0, h0⟩) (fun h1 => ⟨1, h1⟩)
    · obtain ⟨r, hr⟩ : ∃ r, g.eval x = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous, not_forall, not_not] using ha
      have hn : ¬(r = b ∨ r = c) := by
        rintro (rfl | rfl)
        · exact h (Or.inl ((special _ (Or.inl rfl)).1 hr))
        · exact h (Or.inr ((special _ (Or.inr rfl)).1 hr))
      have hs := (g.singleton_iff x r).1 hr
      rw [hg] at hs
      simp [F, hn, ProfileBounds.atomicBits] at hs
      exact hr.trans ((WinnerSet.union_eq_singleton_iff _ _ _).2 hs).symm

private noncomputable abbrev neutral (three : Fin 3 ↪ Role) (k : Role) :=
  PlayerView.representative three k .impossible

private theorem neutral_ambiguous (three : Fin 3 ↪ Role) (k : Role) : (neutral three k).Ambiguous := by
  intro r he
  obtain ⟨q, hqk, hqr⟩ := exists_role_outside_pair three k r
  have hq : q ∈ (neutral three k).val := hqk
  rw [he] at hq
  exact hqr hq

private def Forces (e : Expr Role (Var ⊕ Unit)) (r : Role) : Prop :=
  ∀ v : Var → WinnerSet Role, e.eval (Sum.elim v (fun _ => WinnerSet.singleton r)) = WinnerSet.singleton r

private theorem forced_neutral_ambiguous [Fintype Role] (three : Fin 3 ↪ Role)
    {e : Expr Role (Var ⊕ Unit)} {b c : Role} (hbc : b ≠ c)
    (hb : Forces e b) (hc : Forces e c) (v : Var → WinnerSet Role) (k : Role) :
    (e.eval (Sum.elim v (fun _ => neutral three k))).Ambiguous := by
  classical
  obtain ⟨t, ht⟩ := e.exists_core three
  let j : Var ⊕ Unit := .inr ()
  have hp (r : Role) (h : Forces e r) : profile r (fun i => decide (i = j)) t = true := by
    obtain ⟨s, hsr, _⟩ := exists_role_outside_pair three r r
    let w : Var ⊕ Unit → WinnerSet Role := Sum.elim (fun _ => WinnerSet.singleton s) (fun _ => WinnerSet.singleton r)
    have heq : t.realize w = WinnerSet.singleton r := (ht w).trans (h _)
    have hbits : (fun i => decide (w i = WinnerSet.singleton r)) = (fun i => decide (i = j)) := by
      funext i
      cases i with
      | inl i => simp [w, j, hsr]
      | inr i => cases i; simp [w, j]
    simpa only [hbits] using (winnerSet_eq_singleton_iff_profile t r w).1 heq
  let w : Var ⊕ Unit → WinnerSet Role := Sum.elim v (fun _ => neutral three k)
  have hx : (neutral three k).val ⊆ (e.eval w).val := by
    have h₁ := eq_singleton_or_subset_of_profile_singleton t b j w (hp b hb)
    have h₂ := eq_singleton_or_subset_of_profile_singleton t c j w (hp c hc)
    rw [ht] at h₁ h₂
    rcases h₁ with hs | hs
    · rcases h₂ with hs' | hs'
      · exact (hbc (WinnerSet.singleton_inj.mp (hs.symm.trans hs'))).elim
      · exact hs'
    · exact hs
  intro r hr
  apply neutral_ambiguous three k r
  apply WinnerSet.eq_singleton_of_subset
  exact hx.trans (by rw [show e.eval w = WinnerSet.singleton r from hr]; rfl)

/-- The surviving old inputs are represented uniformly for every neutral
complement, including the case in which the entire expression disappears. -/
private theorem erased [Fintype Role] (three : Fin 3 ↪ Role) (e : Expr Role (Var ⊕ Unit)) :
    ∃ T : Finset (Expr Role Var), (∀ u ∈ T, u.depth ≤ e.depth) ∧
      ∀ v k, k ∈ (e.eval (Sum.elim v (fun _ => neutral three k))).val ↔
        ∃ u ∈ T, k ∈ (u.eval v).val := by
  classical
  obtain ⟨z, hd, hz⟩ := Expr.exists_erasure three e (fun _ => none)
  have hrep (k : Role) := hz (fun _ => neutral three k) (fun _ r =>
    ⟨fun h => (neutral_ambiguous three k r h).elim, fun h => by cases h⟩)
  have hnot (k : Role) : k ∉ ⋃ _ : Unit, (neutral three k).val := by
    simp [neutral, PlayerView.representative]
  cases z with
  | dead a =>
    refine ⟨∅, by simp, fun v k => ?_⟩
    obtain ⟨x, hx, _, he⟩ := hrep k
    rw [show e.eval (Sum.elim v (fun _ => neutral three k)) = x from he v]
    simp only [Finset.notMem_empty, false_and, exists_false, iff_false]
    exact fun hk => hnot k (hx hk)
  | live u M =>
    refine ⟨{u}, by simpa [Residual.depth] using hd, fun v k => ?_⟩
    simp only [Finset.mem_singleton, exists_eq_left]
    obtain ⟨hl, hu, _⟩ := hrep k v
    exact ⟨fun hk => (hu hk).resolve_right (hnot k), fun hk => hl hk⟩

/-- At an outer completion with both forcing conditions the neutral slice is
ambiguous, so its surviving output is already the union of its child slices. -/
private theorem strip [Fintype Role] (three : Fin 3 ↪ Role)
    (b c : Role) (hbc : b ≠ c) (e : Expr Role (Var ⊕ Unit))
    (hb : Forces e b) (hc : Forces e c) :
    ∃ T : Finset (Expr Role Var), (∀ u ∈ T, u.depth + 1 ≤ e.depth) ∧
      ∀ v k, k ∈ (e.eval (Sum.elim v (fun _ => neutral three k))).val ↔
        ∃ u ∈ T, k ∈ (u.eval v).val := by
  classical
  induction e with
  | var j =>
    cases j with
    | inl j => exact (hbc (WinnerSet.singleton_inj.mp (hb (fun _ => WinnerSet.singleton c))).symm).elim
    | inr j =>
      refine ⟨∅, by simp, fun v k => ?_⟩
      change k ≠ k ↔ _
      simp
  | union e f he hf =>
    have split (r : Role) (h : Forces (.union e f) r) : Forces e r ∧ Forces f r :=
      ⟨fun v => ((WinnerSet.union_eq_singleton_iff _ _ r).1 (h v)).1,
       fun v => ((WinnerSet.union_eq_singleton_iff _ _ r).1 (h v)).2⟩
    obtain ⟨T, hT, hTL⟩ := he (split b hb).1 (split c hc).1
    obtain ⟨S, hS, hSR⟩ := hf (split b hb).2 (split c hc).2
    refine ⟨T ∪ S, ?_, fun v k => ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp hu with h | h
      · exact (hT u h).trans (le_max_left _ _)
      · exact (hS u h).trans (le_max_right _ _)
    · change (_ ∨ _) ↔ _
      simp only [hTL, hSR, Finset.mem_union]
      grind
  | gate g args _ =>
    choose T hT hrep using fun i => erased three (args i)
    refine ⟨Finset.univ.biUnion T, ?_, fun v k => ?_⟩
    · intro u hu
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
      exact Nat.succ_le_succ ((hT i u hi).trans
        (Finset.le_sup (f := fun i => (args i).depth) (Finset.mem_univ i)))
    · have hamb := forced_neutral_ambiguous three hbc hb hc v k
      change k ∈ (g.eval _).val ↔ _
      rw [g.union_of_ambiguous _ hamb, Set.mem_iUnion]
      simp only [hrep, Finset.mem_biUnion, Finset.mem_univ, true_and]
      grind

private theorem union_all (T : Finset (Expr Role Var)) (base : Expr Role Var) (d : ℕ)
    (hb : base.depth ≤ d) (hT : ∀ u ∈ T, u.depth ≤ d) :
    ∃ e : Expr Role Var, e.depth ≤ d ∧
      ∀ v k, k ∈ (e.eval v).val ↔ k ∈ (base.eval v).val ∨ ∃ u ∈ T, k ∈ (u.eval v).val := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨base, hb, by simp⟩
  | @insert u T hu ih =>
    obtain ⟨e, hd, he⟩ := ih (fun s hs => hT s (Finset.mem_insert_of_mem hs))
    refine ⟨.union u e, max_le (hT u (Finset.mem_insert_self _ _)) hd, fun v k => ?_⟩
    change (_ ∨ _) ↔ _
    simp only [he, Finset.mem_insert]
    grind

/-- At every depth, suspension requires exactly one additional completion
layer. The equivalence also applies when no expression realizes the operation. -/
theorem suspension_atDepth [Fintype Role] (three : Fin 3 ↪ Role) (b c : Role) (hbc : b ≠ c)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (d : ℕ) :
    FeasibleAtDepth d (fun g => g = suspension b c f) ↔
      ∃ h, h + 1 ≤ d ∧ FeasibleAtDepth h (fun g => g = f) := by
  classical
  constructor
  · rintro ⟨e, he, heval⟩
    have hforce (r : Role) (hr : r = b ∨ r = c) : Forces e r := by
      intro v
      rw [heval]
      rcases hr with rfl | rfl <;> simp [suspension]
    obtain ⟨T, hT, hread⟩ := strip three b c hbc e (hforce b (Or.inl rfl)) (hforce c (Or.inr rfl))
    have hread' (v : Var → WinnerSet Role) (k : Role) :
        k ∈ (f v).val ↔ ∃ u ∈ T, k ∈ (u.eval v).val := by
      have h := hread v k
      rw [heval] at h
      have hn : k ∉ (neutral three k).val := fun hk => hk rfl
      simpa only [suspension, Sum.elim_inr, Sum.elim_inl, neutral_ambiguous three k b,
        neutral_ambiguous three k c, or_self, ite_false, WinnerSet.val_union, Set.mem_union,
        hn, or_false] using h
    obtain ⟨k, hk⟩ := (f (fun _ => WinnerSet.singleton b)).property
    obtain ⟨base, hbase, _⟩ := (hread' _ k).1 hk
    obtain ⟨u, hu, huv⟩ := union_all T base (d-1) (by have := (hT base hbase).trans he; omega)
      (fun u hu => by have := (hT u hu).trans he; omega)
    refine ⟨d-1, by have := (hT base hbase).trans he; omega, u, hu, funext fun v => ?_⟩
    apply Subtype.ext
    ext k
    rw [huv, hread']
    exact ⟨fun h => h.elim (fun hk => ⟨base, hbase, hk⟩) id, Or.inr⟩
  · rintro ⟨h, hsucc, e, hd, heval⟩
    obtain ⟨g, hg⟩ := exists_cap_gate three b c
    let args (i : Fin 2) : Expr Role (Var ⊕ Unit) := if i = 0 then liftExpr e else .var (.inr ())
    refine ⟨.gate g args, ?_, funext fun v => ?_⟩
    · apply Nat.le_trans (Nat.succ_le_succ (Finset.sup_le (fun i _ => ?_))) hsucc
      fin_cases i <;> simp [args, liftExpr_depth, Expr.depth, hd]
    · change g.eval _ = _
      rw [hg]
      simp [args, liftExpr_eval, Expr.eval, heval, suspension]

end KFOL.Core.CompletionDepth
