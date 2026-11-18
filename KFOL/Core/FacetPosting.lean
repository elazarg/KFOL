module

public import KFOL.Equational.Native
public import KFOL.Core.ProfilePruning
public import KFOL.Core.SourceProbes
public import KFOL.Algebra.Atomic.CoreSupport
public import KFOL.Algebra.SemilatticeTrace

/-! # A source forced by a monochromatic posting

A winning profile on a coalition has one member that transmits the owner
on every valuation where the coalition has no foreign singleton. Applying
this to a loss with all satellites posted at one owner gives an obstruction
visible from individual satellite probes.
-/

@[expose] public section
namespace KFOL.Core
variable {Role Var : Type*}
attribute [local instance] Equational.coreStructure

/-- Some member of a winning coalition supplies the owner whenever it carries
that winner and every coalition member is ambiguous or the owner's singleton.
Inputs outside the coalition can take arbitrary menus. -/
theorem exists_source_of_winning_profile [DecidableEq Role]
    (k : Role) (A : Var → Bool) (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (h : profile k A t = true) :
    ∃ i, A i = true ∧ ∀ v : Var → WinnerSet Role, k ∈ (v i).val →
      (∀ j, A j = true → (v j).Ambiguous ∨ v j = WinnerSet.singleton k) →
      k ∈ (t.realize v).val := by
  classical
  obtain ⟨u, _, hle⟩ := exists_view_below_of_profile k A t h
  let g := Equational.Core.decode u
  have hg : g.IsCore := Equational.Core.isCore_decode u
  obtain ⟨i, hi⟩ := hg.vars_nonempty
  refine ⟨i.val, i.property, fun v hwin hat => ?_⟩
  apply ((WinnerSet.view_below_iff _ _ _).1 (hle v)).1
  rw [← Equational.Core.eval_decode]
  change k ∈ (g.eval (fun a => v a.val)).val
  let w (a : {j // A j = true}) := if a = i then WinnerSet.singleton k else v a.val
  apply g.eval_mono (v := w) (w := fun a => v a.val) (fun a => ?_)
  · apply hg.atom_mem_of_occurs w k _ i hi (by simp [w])
    intro a
    by_cases ha : a = i
    · exact Or.inr (by simp [w, ha])
    · simpa only [w, ite_eq_right ha] using hat a.val a.property
  · by_cases ha : a = i
    · subst a
      simpa [w] using Set.singleton_subset_iff.mpr hwin
    · simpa only [w, ite_eq_right ha] using (Set.Subset.rfl : (v a.val).val ⊆ _)

namespace Sources
private theorem neutral_ambiguous (three : Fin 3 ↪ Role) (k : Role) :
    (representative three k .neutral).Ambiguous := by
  intro s hs
  by_cases he : s = k
  · subst s
    exact representative_omits three k .neutral (hs ▸ rfl)
  · have h := (representative_atom_iff three k .neutral ⟨s, he⟩).1 hs
    cases h

/-- Write `none` for a head and `some j` for its satellites. If posting
every satellite at `k` loses the head, some satellite survives on the
`k`-facet at every status of the head when the other satellites are neutral.
The same satellite works for every status. -/
theorem monochromatic_hub_loss_forces_satellite {Satellite : Type*}
    (three : Fin 3 ↪ Role) (t : Term Role (Option Satellite)) (ht : t.IsCore)
    (k l : Role) (hkl : k ≠ l)
    (loss : l ∉ (t.eval (probe three l none (fun _ => .atom ⟨k, hkl⟩))).val) :
    ∃ j : Satellite, ∀ p : Passive k,
      k ∈ (t.eval (probe three k (some j) (fun i =>
        match i.val with | none => p | some _ => .neutral))).val := by
  classical
  let v := probe three l (none : Option Satellite) (fun _ => .atom ⟨k, hkl⟩)
  have hub : v none = WinnerSet.singleton l := probe_source three l _ _
  have satellite (j : Satellite) : v (some j) = WinnerSet.singleton k :=
    (probe_other three l _ _ _ (Option.some_ne_none j)).trans rfl
  have bound := ht.eval_subset_of_support v ({l, k} : Set Role) (by
    rintro (_ | j) _
    · simp [hub]
    · simp [satellite])
  have atom : t.eval v = WinnerSet.singleton k := by
    apply WinnerSet.eq_singleton_of_subset
    intro s hs
    rcases bound hs with h | h
    · have hs0 : s = l := h
      exact (loss (show l ∈ (t.eval v).val from hs0 ▸ hs)).elim
    · exact h
  let u := Equational.Core.encode t ht
  have agrees (w : Option Satellite → WinnerSet Role) : u.realize w = t.eval w := by
    rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
  have flags : (fun i => decide (v i = WinnerSet.singleton k)) = Option.isSome := by
    funext i
    cases i <;> simp [hub, satellite, Ne.symm hkl]
  have hp := (winnerSet_eq_singleton_iff_profile u k v).1 ((agrees v).trans atom)
  rw [flags] at hp
  obtain ⟨i, hi, hwin⟩ := exists_source_of_winning_profile k Option.isSome u hp
  cases i with
  | none => cases hi
  | some j =>
    refine ⟨j, fun p => ?_⟩
    rw [← agrees]
    apply hwin _ ((mem_probe_iff three k _ _ _).2 rfl)
    rintro (_ | a) ha
    · cases ha
    · by_cases he : a = j
      · subst a
        exact Or.inr (probe_source three k _ _)
      · rw [probe_other three k _ _ _ (fun h => he (Option.some.inj h))]
        exact Or.inl (neutral_ambiguous three k)

end Sources
end KFOL.Core
