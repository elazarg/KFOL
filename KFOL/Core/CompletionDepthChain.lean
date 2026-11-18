module

public import KFOL.Core.CompletionDepth
public import KFOL.Core.SingletonProfileAbsorption
public import KFOL.Core.Protected

/-! # An alternating chain has exact completion depth

A single posting at each negative row suffices. If a word were atomic on
two successive rows of different colors in the wrong order, singleton-profile
absorption would transmit the marked head on the second row.
-/

@[expose] public section
namespace KFOL.Core.CompletionDepth

variable {Role : Type*}
attribute [local instance] Equational.coreStructure

private def pair (r s : Role) := (WinnerSet.singleton r).union (WinnerSet.singleton s)

private theorem pair_ambiguous {r s : Role} (hrs : r ≠ s) : (pair r s).Ambiguous := by
  intro k hk
  obtain ⟨hr, hs⟩ := (WinnerSet.union_eq_singleton_iff _ _ k).mp hk
  exact hrs (WinnerSet.singleton_inj.mp (hr.trans hs.symm))

private def color (three : Fin 3 ↪ Role) (k : ℕ) : Role :=
  if k % 2 = 0 then three 1 else three 2

private theorem color_changes (three : Fin 3 ↪ Role) (k : ℕ) :
    color three k ≠ color three (k + 1) := by
  have h := three.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  unfold color
  split_ifs <;> solve | exact h | exact h.symm | omega

private def markRow (three : Fin 3 ↪ Role) {n : ℕ} (j : Fin (n + 1)) : WinnerSet Role :=
  if j.val = 0 then pair (three 0) (three 1) else pair (three 1) (three 2)

private def lossRow (three : Fin 3 ↪ Role) {n : ℕ} (k : ℕ) (j : Fin (n + 1)) :
    WinnerSet Role :=
  if j.val = k then pair (three 0) (three 1)
  else if j.val = k + 1 then WinnerSet.singleton (color three k)
  else pair (three 1) (three 2)

private theorem mark_input_ambiguous (three : Fin 3 ↪ Role) {n : ℕ} (j : Fin (n+1)) :
    (markRow three j).Ambiguous := by
  unfold markRow
  split <;> exact pair_ambiguous (three.injective.ne (by decide))

private theorem marked_iff (three : Fin 3 ↪ Role) {n : ℕ} (j : Fin (n+1)) :
    three 0 ∈ (markRow three j).val ↔ j.val = 0 := by
  have h01 := three.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := three.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  by_cases h : j.val = 0 <;> simp [markRow, pair, h, h01, h02]

private theorem loss_input_singleton_iff (three : Fin 3 ↪ Role) {n : ℕ} (j : Fin (n+1))
    (k : ℕ) (r : Role) :
    lossRow three k j = WinnerSet.singleton r ↔ j.val = k+1 ∧ color three k = r := by
  unfold lossRow
  split_ifs with hh hp
  · have h := pair_ambiguous (three.injective.ne (by decide : (0 : Fin 3) ≠ 1)) r
    simp [h, show j.val ≠ k+1 by omega]
  · simp [hp]
  · have h := pair_ambiguous (three.injective.ne (by decide : (1 : Fin 3) ≠ 2)) r
    simp [h, hp]

private theorem loss_mark_iff (three : Fin 3 ↪ Role) {n : ℕ} (j : Fin (n+1)) (k : ℕ) :
    three 0 ∈ (lossRow three k j).val ↔ j.val = k := by
  have h01 := three.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := three.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hn : three 0 ≠ color three k := by unfold color; split <;> assumption
  unfold lossRow
  split_ifs <;> simp_all [pair]

variable [DecidableEq Role]

private theorem exists_atomic_input {Var : Type*} (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (w : Var → WinnerSet Role) (r : Role) (h : t.realize w = WinnerSet.singleton r) :
    ∃ j, w j = WinnerSet.singleton r := by
  classical
  by_contra! hn
  have he : (fun j => decide (w j = WinnerSet.singleton r)) = fun _ => false :=
    funext fun j => decide_eq_false (hn j)
  have hp := (winnerSet_eq_singleton_iff_profile t r w).mp h
  rw [he, profile_false] at hp
  cases hp

variable [Fintype Role]

private theorem mark_ambiguous (three : Fin 3 ↪ Role) {n : ℕ} (e : Expr Role (Fin (n+1))) :
    (e.eval (markRow three)).Ambiguous := by
  intro r hr
  obtain ⟨t, ht⟩ := e.exists_core three
  obtain ⟨j, hj⟩ := exists_atomic_input t (markRow three) r ((ht _).trans hr)
  exact mark_input_ambiguous three j r hj

private theorem ambiguous_before_quiet (three : Fin 3 ↪ Role) {n : ℕ}
    (e : Expr Role (Fin (n+1))) (k : ℕ) (hk : k < n)
    (hquiet : three 0 ∉ (e.eval (lossRow three (k+1))).val) :
    (e.eval (lossRow three k)).Ambiguous := by
  intro r hr
  obtain ⟨t, ht⟩ := e.exists_core three
  have hat := (ht _).trans hr
  obtain ⟨v, hv⟩ := exists_atomic_input t _ r hat
  obtain ⟨hv, rfl⟩ := (loss_input_singleton_iff three v k r).mp hv
  let next : Fin (n+1) := ⟨k+1, by omega⟩
  have he : (fun j : Fin (n+1) => decide (lossRow three k j = WinnerSet.singleton (color three k))) =
      fun j => decide (j = next) := by
    funext j
    simp [loss_input_singleton_iff, Fin.ext_iff, next]
  have hp := (winnerSet_eq_singleton_iff_profile t _ _).mp hat
  rw [he] at hp
  rcases eq_singleton_or_subset_of_profile_singleton t (color three k) next
      (lossRow three (k+1)) hp with hsing | hsub
  · obtain ⟨j, hj⟩ := exists_atomic_input t _ _ hsing
    exact color_changes three k ((loss_input_singleton_iff three j _ _).mp hj).2.symm
  · apply hquiet
    rw [← ht]
    exact hsub ((loss_mark_iff three next (k+1)).mpr rfl)

private theorem depth_lower (three : Fin 3 ↪ Role) {n : ℕ} (e : Expr Role (Fin (n+1)))
    (m : ℕ) (hm : m ≤ n) (hp : three 0 ∈ (e.eval (markRow three)).val)
    (hz : ∀ k < m, three 0 ∉ (e.eval (lossRow three k)).val) : m ≤ e.depth := by
  induction e generalizing m with
  | var j =>
    have hj := (marked_iff three j).mp hp
    by_cases h : m = 0
    · simp [h]
    · exact (hz 0 (by omega) ((loss_mark_iff three j 0).mpr hj)).elim
  | union s t ihs iht =>
    rcases hp with hs | ht
    · exact le_trans (ihs m hm hs fun k hk h => hz k hk (Or.inl h)) (Nat.le_max_left _ _)
    · exact le_trans (iht m hm ht fun k hk h => hz k hk (Or.inr h)) (Nat.le_max_right _ _)
  | gate g args ih =>
    cases m with
    | zero => exact Nat.zero_le _
    | succ m =>
      let e := Expr.gate g args
      have hu (w : Fin (n+1) → WinnerSet Role) (ha : (e.eval w).Ambiguous) :
          (e.eval w).val = ⋃ j, ((args j).eval w).val := g.union_of_ambiguous _ ha
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ((hu _ (mark_ambiguous three e)) ▸ hp)
      have hdepth := ih j m (by omega) hj (by
        intro k hk hmark
        have ha := ambiguous_before_quiet three e k (by omega) (hz (k+1) (by omega))
        apply hz k (by omega)
        change three 0 ∈ (e.eval (lossRow three k)).val
        rw [hu _ ha]
        exact Set.mem_iUnion.mpr ⟨j, hmark⟩)
      exact Nat.succ_le_succ (hdepth.trans (Finset.le_sup (f := fun i => (args i).depth) (Finset.mem_univ j)))

private def atIndex (n k : ℕ) : Fin (n+1) := ⟨min k n, by omega⟩

private noncomputable def chain (three : Fin 3 ↪ Role) (n : ℕ) : ℕ → Expr Role (Fin (n+1))
  | 0 => .var 0
  | k+1 => Expr.choice (color three k) (chain three n k) (.var (atIndex n (k+1)))

omit [Fintype Role] in
private theorem chain_eval_succ (three : Fin 3 ↪ Role) (n k : ℕ) (v : Fin (n+1) → WinnerSet Role) :
    (chain three n (k+1)).eval v = WinnerSet.choice (color three k)
      ((chain three n k).eval v) (v (atIndex n (k+1))) := rfl

omit [Fintype Role] in
private theorem chain_depth_le (three : Fin 3 ↪ Role) (n k : ℕ) :
    (chain three n k).depth ≤ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [chain, Expr.choice_depth, Expr.depth, Nat.max_zero]
    exact Nat.succ_le_succ ih

private theorem chain_positive (three : Fin 3 ↪ Role) (n k : ℕ) :
    three 0 ∈ ((chain three n k).eval (markRow three)).val := by
  induction k with
  | zero => exact (marked_iff three 0).mpr rfl
  | succ k ih =>
    rw [chain_eval_succ, WinnerSet.choice, ite_eq_right (not_or.mpr
      ⟨mark_ambiguous three _ _, mark_input_ambiguous three _ _⟩)]
    exact Or.inl ih

omit [Fintype Role] in
private theorem chain_quiet (three : Fin 3 ↪ Role) (n m : ℕ) (hm : m ≤ n) :
    ∀ k < m, three 0 ∉ ((chain three n m).eval (lossRow three k)).val := by
  induction m with
  | zero => omega
  | succ m ih =>
    intro k hk hmark
    rw [chain_eval_succ] at hmark
    have hj : (atIndex n (m+1)).val = m+1 := Nat.min_eq_left hm
    by_cases he : k = m
    · subst k
      have ha := (loss_input_singleton_iff three (atIndex n (m+1)) m (color three m)).mpr ⟨hj, rfl⟩
      rw [WinnerSet.choice, ite_eq_left (Or.inr ha)] at hmark
      change three 0 = color three m at hmark
      unfold color at hmark
      split at hmark <;> have := three.injective hmark <;> omega
    · rcases WinnerSet.choice_subset_union _ _ _ hmark with h | h
      · exact ih (by omega) k (by omega) h
      · have := (loss_mark_iff three (atIndex n (m+1)) k).mp h
        omega

/-- One positive row and m negative rows can already require exactly m
layers, all testing membership of the same winner. -/
theorem exact_depth_sample (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ (p : Fin (m+1) → WinnerSet Role) (z : Fin m → Fin (m+1) → WinnerSet Role),
      ∀ d, FeasibleAtDepth d (fun f =>
        three 0 ∈ (f p).val ∧ ∀ j, three 0 ∉ (f (z j)).val) ↔ m ≤ d := by
  refine ⟨markRow three, fun j => lossRow three j.val, ?_⟩
  intro d
  constructor
  · rintro ⟨e, he, hpos, hneg⟩
    exact (depth_lower three e m le_rfl hpos fun k hk => hneg ⟨k, hk⟩).trans he
  · intro h
    exact ⟨chain three m m, (chain_depth_le three m m).trans h, chain_positive three m m,
      fun j => chain_quiet three m m le_rfl j.val j.isLt⟩

/-- At every depth there is a core operation in that layer which has no
shallower expression, even with arbitrary finite completion gates and free union. -/
theorem exact_depth (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ e : Expr Role (Fin (m+1)), e.depth = m ∧
      ∀ f : Expr Role (Fin (m+1)), (∀ v, f.eval v = e.eval v) → m ≤ f.depth := by
  refine ⟨chain three m m, le_antisymm (chain_depth_le three m m) ?_, ?_⟩
  · exact depth_lower three _ m le_rfl (chain_positive three m m) (chain_quiet three m m le_rfl)
  · intro f hf
    apply depth_lower three f m le_rfl
    · rw [hf]
      exact chain_positive three m m
    · intro k hk
      rw [hf]
      exact chain_quiet three m m le_rfl k hk

end KFOL.Core.CompletionDepth
