module

public import KFOL.Strategic.Forcing

/-! # Pure Nash and subgame-perfect winners in public trees -/

@[expose] public section

namespace KFOL.Strategic

variable {Role : Type*} {g : Tree Role}

/-- Keep the opponents' choices from the first profile and the designated
player's choices from the second, at every decision including unreached ones. -/
private theorem combine_plans (i : Role) (p q : Profile g) :
    ∃ s, Deviation i p s ∧ OpponentDeviation i q s := by
  induction p with
  | leaf w =>
    cases q
    exact ⟨.leaf w, .leaf w, .leaf w⟩
  | node r a p₁ p₂ ih₁ ih₂ =>
    cases q with
    | node _ b q₁ q₂ =>
      obtain ⟨s₁, hd₁, ho₁⟩ := ih₁ q₁
      obtain ⟨s₂, hd₂, ho₂⟩ := ih₂ q₂
      by_cases h : r = i
      · exact ⟨.node r b s₁ s₂, .node (fun ne => (ne h).elim) hd₁ hd₂,
          .node (fun _ => rfl) ho₁ ho₂⟩
      · exact ⟨.node r a s₁ s₂, .node (fun _ => rfl) hd₁ hd₂,
          .node (fun eq => (h eq).elim) ho₁ ho₂⟩

/-- A forcing plan gives a unilateral winning deviation from any profile. -/
theorem CanForce.winner_of_nash {i : Role} (hf : CanForce g i)
    {p : Profile g} (hn : IsNash p) : winner p = i := by
  obtain ⟨q, wins⟩ := hf
  obtain ⟨s, hd, ho⟩ := combine_plans i p q
  exact hn i s hd (wins s ho)

/-- Each pure Nash winner occurs in some subgame-perfect profile. -/
theorem IsNash.winner_mem_possibleWinners {p : Profile g} (hn : IsNash p) :
    winner p ∈ possibleWinners g := by
  classical
  induction p with
  | leaf w => exact ⟨.leaf w, spe_leaf w, rfl⟩
  | @node left right r a p q ihp ihq =>
    rw [possibleWinners_node]
    split_ifs with h
    · have hf : CanForce (.node r left right) r := by
        rw [canForce_node, ite_eq_left rfl]
        exact h.imp (fun eq => (canForce_iff_value_singleton _ r).mpr (Subtype.ext eq))
          (fun eq => (canForce_iff_value_singleton _ r).mpr (Subtype.ext eq))
      exact hf.winner_of_nash hn
    · cases a with
      | false =>
        apply Or.inl
        exact ihp (fun i s d win => hn i (.node r false s q)
          (.node (fun _ => rfl) d (change_refl i q)) win)
      | true =>
        apply Or.inr
        exact ihq (fun i s d win => hn i (.node r true p s)
          (.node (fun _ => rfl) (change_refl i p) d) win)

/-- Pure Nash and subgame-perfect equilibria yield exactly the same set of
winners on every finite binary public tree with one winner at each leaf. -/
theorem nashWinners_eq_possibleWinners (G : Tree Role) :
    {i | ∃ p : Profile G, IsNash p ∧ winner p = i} = possibleWinners G := by
  ext i
  constructor
  · rintro ⟨p, hn, rfl⟩
    exact hn.winner_mem_possibleWinners
  · rintro ⟨p, hs, hw⟩
    exact ⟨p, spe_nash hs, hw⟩

end KFOL.Strategic
