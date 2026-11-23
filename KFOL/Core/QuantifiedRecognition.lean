module

public import KFOL.Core.BichainRecognition
public import KFOL.Core.RowLosses

/-! # Quantified Boolean formulas as recognition of core term operations

The rows of a prenex formula give one explicit operation on finitely many
inputs. It is a core term operation exactly when the formula is true. The
operation has an explicit system of losses with at most four losses at each
input, so its prime guards have at most four postings each, and the formula
is true exactly when some core term has these prime guards.
-/

@[expose] public section
namespace KFOL.Bichain.Quantified

universe u

variable {Role : Type u} (three : Fin 3 ↪ Role) (F : Formula) (α : ℕ → Bool)

theorem eval_neutral {V : Type*} : ∀ p : Term V, p.IsPure → p.eval (fun _ => .neutral) = .neutral := by
  intro p
  induction p with
  | var j => intro _; rfl
  | inf x y hx hy => intro h; simp [Term.eval, hx h.1, hy h.2, Value.inf]
  | sup x y hx hy => intro h; simp [Term.eval, hx h.1, hy h.2, Value.sup]
  | union x y hx hy => intro h; exact h.elim

/-- A prenex formula is true exactly when its operation is a core term operation. -/
theorem sat_iff_operation (hwf : F.WF) :
    sat F F.n 0 α ↔ ∃ t : KFOL.Term Role (Input F), t.IsCore ∧
      ∀ v, t.eval v = operation three F α v := by
  rw [sat_iff_separator F hwf α, operation, Recognition.recognition_iff]
  constructor
  · rintro ⟨p, hp, hrows, hX, hY⟩
    refine ⟨p, hp, fun z => ?_, hX, hY⟩
    cases z with
    | inl b =>
      change p.eval (fun _ => Value.neutral) ≠ _
      rw [eval_neutral p hp]
      decide
    | inr z => exact hrows z.val z.property
  · rintro ⟨p, hp, hrows, hX, hY⟩
    exact ⟨p, hp, fun z hz => hrows (.inr ⟨z, hz⟩), hX, hY⟩

/-- The first endpoint is true at some coordinate. -/
theorem exists_start_label : ∃ e : FLab F, inI F (.br 0 (α 0)) e.val = true := by
  by_cases hn : 1 ≤ F.n
  · exact ⟨⟨.ch 1 true, mem_labels_of_isLab F ⟨le_rfl, hn⟩⟩, by simp [inI]⟩
  · refine ⟨⟨.kap 0, mem_labels_of_isLab F (Or.inr rfl)⟩, ?_⟩
    have h0 : F.n = 0 := by omega
    simp [inI, h0]

/-- The losses of the operation of a formula. -/
noncomputable abbrev operationLosses :
    Input F → List (List (Input F × Role)) :=
  Recognition.losses three (paddedRows F) (fun e => inI F (.br 0 (α 0)) e.val)
    (fun e => !inJ F (.relay 0) e.val)

/-- The operation of a formula is supplied by its inputs, and each input
fails exactly on its listed losses. -/
theorem operation_lossSystem :
    Core.Sources.LossSystem (operation three F α) (operationLosses three F α) :=
  Recognition.target_lossSystem three _ _ _ _ (exists_start_label F α)

theorem rows_eq_possible_iff (z : Vtx) (e : FLab F) :
    rows F z e = .possible ↔ mark F z = e.val := by
  unfold rows
  split_ifs <;> simp_all

/-- Every coordinate is marked by at most two rows. -/
theorem mark_two (e : Lab) :
    ∃ z1 z2 : Vtx, ∀ z ∈ allRows F, mark F z = e → z = z1 ∨ z = z2 := by
  cases e with
  | ch j s =>
    refine ⟨.br j true, .br j false, fun z _ h => ?_⟩
    obtain ⟨s', rfl, -, -⟩ := mark_eq_ch F h
    cases s' <;> simp
  | rl j => exact ⟨.relay j, .relay j, fun z _ h => Or.inl (mark_eq_rl F h)⟩
  | perm j t => exact ⟨.cl 0, .cl 0, fun z _ h => absurd h (mark_ne_perm F z j t)⟩
  | lit j t => exact ⟨.res j t, .res j t, fun z _ h => Or.inl (mark_eq_lit F h)⟩
  | kap c =>
    refine ⟨.cl c, .br (F.n + c + 1) true, fun z hz h => ?_⟩
    rcases mark_eq_kap F h with rfl | ⟨t, rfl⟩
    · exact Or.inl rfl
    · have hrow := (mem_allRows F _).1 hz
      rcases hrow with hrow | hrow
      · omega
      · rw [hrow.2.2]
        exact Or.inr rfl

/-- Every input of the operation of a formula has at most four losses. -/
theorem length_operationLosses_le (j : Input F) : (operationLosses three F α j).length ≤ 4 := by
  classical
  refine (Recognition.length_losses_le three _ _ _ j).trans ?_
  cases j with
  | inl u => simp
  | inr x =>
    suffices h : (Finset.univ.filter fun z : RowIx F =>
        Recognition.rowP (paddedRows F) z x = .possible).card ≤ 2 from
      Nat.add_le_add_left h 2
    cases x with
    | none =>
      rw [Finset.card_eq_zero.2]
      · omega
      · rw [Finset.filter_eq_empty_iff]
        intro z _ h
        cases h
    | some e =>
      obtain ⟨z1, z2, hz⟩ := mark_two F e.val
      let g : RowIx F → Vtx := fun z => match z with
        | .inl _ => z1
        | .inr z => z.val
      refine (Finset.card_le_card_of_injOn g (t := {z1, z2}) ?_ ?_).trans Finset.card_le_two
      · intro z hzmem
        have hp : Recognition.rowP (paddedRows F) z (some e) = .possible :=
          (Finset.mem_filter.1 hzmem).2
        cases z with
        | inl b => cases hp
        | inr z =>
          have hm := (rows_eq_possible_iff F z.val e).1 hp
          rcases hz z.val z.property hm with h | h <;> simp [g, h]
      · intro z hzmem z' hzmem'
        have hp : Recognition.rowP (paddedRows F) z (some e) = .possible :=
          (Finset.mem_filter.1 (Finset.mem_coe.1 hzmem)).2
        have hp' : Recognition.rowP (paddedRows F) z' (some e) = .possible :=
          (Finset.mem_filter.1 (Finset.mem_coe.1 hzmem')).2
        cases z with
        | inl b => cases hp
        | inr z =>
          cases z' with
          | inl b => cases hp'
          | inr z' =>
            intro h
            exact congrArg Sum.inr (Subtype.ext h)

/-- A prime guard of the operation of a formula has at most four postings. -/
theorem card_prime_guard_le [Fintype Role] (k : Role) (j : Input F)
    (g : Core.Sources.Guard k j)
    (hg : g ∈ Core.Sources.normalForm three (operation three F α) k j) : g.card ≤ 4 :=
  (Core.Sources.card_le_of_minimal_meetsAll _ g
    (((operation_lossSystem three F α).mem_normalForm_iff three k j g).1 hg)).trans
    (length_operationLosses_le three F α j)

/-- A prenex formula is true exactly when some core term has the prime
guards of its operation. -/
theorem sat_iff_normalForm [Fintype Role] (hwf : F.WF) :
    sat F F.n 0 α ↔ ∃ t : KFOL.Term Role (Input F), t.IsCore ∧
      Core.Sources.normalForm three (fun v => t.eval v) =
        Core.Sources.normalForm three (operation three F α) := by
  rw [sat_iff_operation three F α hwf]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, congrArg (Core.Sources.normalForm three) (funext h)⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (operation_lossSystem three F α).eq_of_normalForm_eq three t ht h⟩

end KFOL.Bichain.Quantified
