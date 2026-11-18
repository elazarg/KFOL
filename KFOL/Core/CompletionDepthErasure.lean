module

public import KFOL.Core.CompletionGateRestriction

/-! # Fixing background inputs without increasing completion depth -/

@[expose] public section
namespace KFOL.Core.CompletionDepth
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} {Fix : Type w}

namespace Residual

private def body : Residual Role Var → Option (Expr Role Var)
  | .dead _ => none
  | .live e _ => some e

private def atom : Residual Role Var → Option Role
  | .dead a => a
  | .live _ _ => none

private def enabled : Residual Role Var → Role → Bool
  | .dead _, _ => false
  | .live _ M, r => M r

omit [DecidableEq Role] in
private theorem of_dead {B : Set Role} {f : (Var → WinnerSet Role) → WinnerSet Role}
    {z : Residual Role Var} (hz : z.body = none) (h : Represents B f z) :
    ∃ c : WinnerSet Role, c.val ⊆ B ∧
      (∀ r, c = WinnerSet.singleton r ↔ z.atom = some r) ∧ ∀ v, f v = c := by
  cases z with
  | dead a => exact h
  | live e M => cases hz

omit [DecidableEq Role] in
private theorem of_live {B : Set Role} {f : (Var → WinnerSet Role) → WinnerSet Role}
    {z : Residual Role Var} {e : Expr Role Var} (hz : z.body = some e)
    (h : Represents B f z) (v : Var → WinnerSet Role) :
    (e.eval v).val ⊆ (f v).val ∧ (f v).val ⊆ (e.eval v).val ∪ B ∧
      ∀ r, f v = WinnerSet.singleton r ↔ z.enabled r = true ∧ e.eval v = WinnerSet.singleton r := by
  cases z with
  | dead a => cases hz
  | live e' M =>
    obtain rfl : e' = e := Option.some.inj hz
    exact h v

omit [DecidableEq Role] in
private theorem depth_of_live {z : Residual Role Var} {e : Expr Role Var}
    (h : z.body = some e) : z.depth = e.depth := by
  cases z with
  | dead a => cases h
  | live e' M => exact congrArg Expr.depth (Option.some.inj h)

private def unionResidual : Residual Role Var → Residual Role Var → Residual Role Var
  | .dead a, .dead b => .dead (if a = b then a else none)
  | .dead a, .live t M | .live t M, .dead a => .live t (fun r => decide (a = some r) && M r)
  | .live s L, .live t M => .live (.union s t) (fun r => L r && M r)

private theorem depth_unionResidual (x y : Residual Role Var) :
    (unionResidual x y).depth ≤ max x.depth y.depth := by
  cases x <;> cases y <;> simp [unionResidual, depth, Expr.depth]

private theorem represents_union {B : Set Role} {f g : (Var → WinnerSet Role) → WinnerSet Role}
    {x y : Residual Role Var} (hf : Represents B f x) (hg : Represents B g y) :
    Represents B (fun v => (f v).union (g v)) (unionResidual x y) := by
  cases x with
  | dead a =>
    obtain ⟨c, hc, hs, he⟩ := hf
    cases y with
    | dead b =>
      obtain ⟨d, hd, ht, hq⟩ := hg
      refine ⟨c.union d, Set.union_subset hc hd, fun r => ?_, fun v => congrArg₂ WinnerSet.union (he v) (hq v)⟩
      rw [WinnerSet.union_eq_singleton_iff, hs, ht]
      by_cases hab : a = b
      · simp [hab]
      · simp only [ite_eq_right hab, reduceCtorEq, iff_false]
        exact fun h => hab (h.1.trans h.2.symm)
    | live t M =>
      intro v
      obtain ⟨hl, hu, ha⟩ := hg v
      simp only [he v]
      refine ⟨fun _ hk => Or.inr (hl hk), ?_, fun r => ?_⟩
      · exact Set.union_subset (fun _ hk => Or.inr (hc hk)) hu
      · simp only [WinnerSet.union_eq_singleton_iff, hs, ha, Bool.and_eq_true,
          decide_eq_true_eq, and_assoc]
  | live s L =>
    cases y with
    | dead a =>
      obtain ⟨c, hc, hs, he⟩ := hg
      intro v
      obtain ⟨hl, hu, ha⟩ := hf v
      simp only [he v]
      refine ⟨fun _ hk => Or.inl (hl hk), ?_, fun r => ?_⟩
      · exact Set.union_subset hu (fun _ hk => Or.inr (hc hk))
      · simp only [WinnerSet.union_eq_singleton_iff, hs, ha, Bool.and_eq_true, decide_eq_true_eq]
        tauto
    | live t M =>
      intro v
      obtain ⟨hfl, hfu, hfa⟩ := hf v
      obtain ⟨hgl, hgu, hga⟩ := hg v
      refine ⟨Set.union_subset_union hfl hgl, ?_, fun r => ?_⟩
      · exact Set.union_subset (hfu.trans (Set.union_subset_union_left _ Set.subset_union_left))
          (hgu.trans (Set.union_subset_union_left _ Set.subset_union_right))
      · simp only [Expr.eval, WinnerSet.union_eq_singleton_iff, hfa, hga, Bool.and_eq_true]
        tauto

private theorem exists_gate {n : ℕ} [Fintype Role] (three : Fin 3 ↪ Role)
    (g : Gate Role n) (z : Fin (n + 1) → Residual Role Var) :
    ∃ out : Residual Role Var, out.depth ≤ (Finset.univ.sup fun j => (z j).depth) + 1 ∧
      ∀ (B : Set Role) (f : Fin (n + 1) → (Var → WinnerSet Role) → WinnerSet Role),
        (∀ j, Represents B (f j) (z j)) → Represents B (fun v => g.eval (fun j => f j v)) out := by
  classical
  let flags (r : Role) (j : Fin (n + 1)) := decide ((z j).atom = some r)
  by_cases forced : ∃ r, g.profiles r (flags r) = true
  · obtain ⟨r, hr⟩ := forced
    refine ⟨.dead (some r), Nat.zero_le _, fun B f hf => ?_⟩
    have supplied (j) (hj : flags r j = true) :
        ∀ v, f j v = WinnerSet.singleton r := by
      have ha := of_decide_eq_true hj
      have hn : (z j).body = none := by
        cases hz : z j with
        | dead a => rfl
        | live e M => rw [hz] at ha; cases ha
      obtain ⟨c, _, hs, he⟩ := of_dead hn (hf j)
      exact fun v => (he v).trans ((hs r).2 ha)
    have wins (v) : g.eval (fun j => f j v) = WinnerSet.singleton r :=
      (g.singleton_iff _ r).2 (g.admissible.mono r _ _ (fun j hj => decide_eq_true (supplied j hj v)) hr)
    have hw : ∃ j, flags r j = true := by
      let A (s : Role) := if s = r then flags r else fun _ => true
      have hA (s) : g.profiles s (A s) = true := by
        by_cases hs : s = r
        · simpa [A, hs] using hr
        · simpa [A, hs] using g.admissible.top s
      obtain ⟨j, hj⟩ := g.admissible.common_source A hA
      exact ⟨j, by simpa [A] using hj r⟩
    obtain ⟨j, hj⟩ := hw
    have ha := of_decide_eq_true hj
    have hn : (z j).body = none := by
      cases hz : z j with
      | dead a => rfl
      | live e M => rw [hz] at ha; cases ha
    obtain ⟨c, hB, hs, _⟩ := of_dead hn (hf j)
    refine ⟨WinnerSet.singleton r, (hs r).2 ha ▸ hB, ?_, wins⟩
    simp
  have hzero (r) : g.profiles r (flags r) = false := by
    cases h : g.profiles r (flags r)
    · rfl
    · exact (forced ⟨r, h⟩).elim
  let L := {j : Fin (n + 1) // (z j).body.isSome}
  by_cases hL : Nonempty L
  · let _ : Fintype L := Fintype.ofFinite L
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hL))
    let idx : Fin (m + 1) ≃ L := (Fintype.equivFinOfCardEq hm).symm
    let port (j) := if h : (z j).body.isSome then some (idx.symm ⟨j, h⟩) else none
    let args (i : Fin (m + 1)) := (z (idx i).val).body.get (idx i).property
    have port_spec {j i} (h : port j = some i) : (idx i).val = j := by
      dsimp only [port] at h
      split_ifs at h with hbody
      · have hi := Option.some.inj h
        rw [← hi, Equiv.apply_symm_apply]
    have hbody (i) : (z (idx i).val).body = some (args i) := (Option.some_get _).symm
    have bits (r) : Gate.restrictedBits port (fun j => (z j).atom) (fun r j => (z j).enabled r)
        r (fun _ => false) = flags r := by
      funext j
      cases hz : z j with
      | dead a => simp [Gate.restrictedBits, port, hz, body, flags, atom]
      | live e M => simp [Gate.restrictedBits, port, hz, body, flags, atom]
    obtain ⟨g', hg'⟩ := g.exists_restriction three port (fun j => (z j).atom)
      (fun r j => (z j).enabled r) (fun r => by rw [bits r]; exact hzero r)
    let mask r := g.profiles r (Gate.restrictedBits port (fun j => (z j).atom)
      (fun s j => (z j).enabled s) r (fun _ => true))
    refine ⟨.live (.gate g' args) mask, Nat.succ_le_succ (Finset.sup_le fun i _ => ?_),
      fun B f hf v => ?_⟩
    · rw [← depth_of_live (hbody i)]
      exact Finset.le_sup (f := fun j => (z j).depth) (Finset.mem_univ _)
    · apply g.restriction_eval g' port (fun j => (z j).atom) (fun r j => (z j).enabled r)
        hg' (fun i => ⟨(idx i).val, by simp [port, (idx i).property]⟩)
        (fun j => f j v) (fun i => (args i).eval v) B
      · intro j i hj
        obtain rfl := port_spec hj
        exact of_live (hbody i) (hf _) v
      · intro j hj
        have hn : (z j).body = none := by
          apply Option.not_isSome_iff_eq_none.1
          intro h
          simp [port, h] at hj
        obtain ⟨c, hc, hs, he⟩ := of_dead hn (hf j)
        rw [he v]
        exact ⟨hc, hs⟩
  · refine ⟨.dead none, Nat.zero_le _, fun B f hf => ?_⟩
    have hn (j) : (z j).body = none :=
      Option.not_isSome_iff_eq_none.1 (fun h => hL ⟨⟨j, h⟩⟩)
    choose c hc hs he using (fun j => of_dead (hn j) (hf j))
    have eqbits (r) : ProfileBounds.atomicBits r c = flags r := by
      funext j
      exact Bool.eq_iff_iff.mpr (by simpa [ProfileBounds.atomicBits, flags] using hs j r)
    have hamb : (g.eval c).Ambiguous := by
      intro r hr
      have h := (g.singleton_iff c r).1 hr
      rw [eqbits, hzero] at h
      cases h
    refine ⟨g.eval c, ?_, fun r => ⟨fun h => (hamb r h).elim, fun h => by cases h⟩, ?_⟩
    · rw [g.union_of_ambiguous c hamb]
      exact Set.iUnion_subset hc
    · exact fun v => congrArg g.eval (funext fun j => he j v)

end Residual

/-- Fixing any collection of background inputs preserves the depth bound.
One residual and mask work for every choice of actual background menus with
the indicated singleton statuses. -/
theorem Expr.exists_erasure [Fintype Role] (three : Fin 3 ↪ Role)
    (e : Expr Role (Var ⊕ Fix)) (status : Fix → Option Role) :
    ∃ z : Residual Role Var, z.depth ≤ e.depth ∧
      ∀ (w : Fix → WinnerSet Role), (∀ j r, w j = WinnerSet.singleton r ↔ status j = some r) →
        Residual.Represents (⋃ j, (w j).val) (fun v => e.eval (Sum.elim v w)) z := by
  classical
  induction e with
  | var j =>
    cases j with
    | inl i =>
      refine ⟨.live (.var i) (fun _ => true), le_rfl, fun w _ v => ?_⟩
      exact ⟨fun _ h => h, Set.subset_union_left, fun _ => by simp [Expr.eval]⟩
    | inr j =>
      exact ⟨.dead (status j), le_rfl, fun w hw =>
        ⟨w j, Set.subset_iUnion (fun i => (w i).val) j, hw j, fun _ => rfl⟩⟩
  | union e f ih ih' =>
    obtain ⟨a, ha, hA⟩ := ih
    obtain ⟨b, hb, hB⟩ := ih'
    exact ⟨Residual.unionResidual a b, (Residual.depth_unionResidual _ _).trans (max_le_max ha hb),
      fun w hw => Residual.represents_union (hA w hw) (hB w hw)⟩
  | gate g args ih =>
    choose z hz hr using ih
    obtain ⟨out, hd, ho⟩ := Residual.exists_gate three g z
    refine ⟨out, hd.trans (Nat.succ_le_succ (Finset.sup_le fun j _ => ?_)), ?_⟩
    · exact (hz j).trans (Finset.le_sup (f := fun i => (args i).depth) (Finset.mem_univ j))
    · exact fun w hw => ho _ _ (fun j => hr j w hw)

end KFOL.Core.CompletionDepth
