module

public import KFOL.Core.PruningContexts
import Mathlib.Data.Fintype.Basic

/-! # Independent composition of completion sets -/

@[expose] public section
namespace KFOL.Core.PruningContexts

open CompulsoryPruning ProfileBudgets

variable {Role V : Type*} [DecidableEq Role] [DecidableEq V]

def wordCompletions (legal : Role → Set (Finset V)) (r : Role) (t : CoreTerm Role V) :
    Set (Finset V) :=
  completions (legal r) (Supports r t)

private theorem attach (legal : Role → Set (Finset V))
    (base neutral : CoreTerm Role V) (owner r : Role)
    (safe : ∀ q, wordCompletions legal q neutral = Set.univ) :
    wordCompletions legal r (choiceTerm owner base neutral) =
      if r = owner then Set.univ else wordCompletions legal r base := by
  by_cases eq : r = owner
  · subst owner
    simp only [wordCompletions, owned_supports, ite_true]
    rw [supportUnions_comm]
    ext extra
    rw [mem_completion_product]
    change (∀ support ∈ Supports r base, support ∪ extra ∈ wordCompletions legal r neutral) ↔ _
    simp [safe]
  · simp only [wordCompletions, foreign_supports (Ne.symm eq), completion_union, ite_eq_right eq]
    change wordCompletions legal r base ∩ wordCompletions legal r neutral =
      wordCompletions legal r base
    rw [safe, Set.inter_univ]

/-- Attach a universally extendible word at all owners in a chosen set.
This resets their completion sets and preserves the other coordinates. -/
theorem exists_padding_context (legal : Role → Set (Finset V)) (owners : Finset Role)
    (neutral : CoreTerm Role V) (safe : ∀ q, wordCompletions legal q neutral = Set.univ) :
    ∃ ctx : Context Role V, ∀ t r,
      wordCompletions legal r (ctx.plug t) =
        if r ∈ owners then Set.univ else wordCompletions legal r t := by
  induction owners using Finset.induction_on with
  | empty => exact ⟨.hole, by simp [Context.plug]⟩
  | insert owner rest _ ih =>
    obtain ⟨ctx, hctx⟩ := ih
    refine ⟨.left owner ctx neutral, fun t r => ?_⟩
    change wordCompletions legal r (choiceTerm owner (ctx.plug t) neutral) = _
    rw [attach legal _ _ _ _ safe, hctx]
    by_cases eq : r = owner <;> simp [eq]

private theorem inter_subset_completion_product {legal A B : Set (Finset V)}
    (closed : ∀ ⦃X Y⦄, X ∈ legal → Y ∈ legal → X ∪ Y ∈ legal) :
    completions legal A ∩ completions legal B ⊆ completions legal (supportUnions A B) := by
  rintro extra ⟨left, right⟩ combined ⟨X, hx, Y, hy, rfl⟩
  have eq : (X ∪ extra) ∪ (Y ∪ extra) = (X ∪ Y) ∪ extra := by
    ext x
    simp only [Finset.mem_union]
    tauto
  exact eq ▸ closed (left X hx) (right Y hy)

private theorem completion_square {legal A : Set (Finset V)}
    (closed : ∀ ⦃X Y⦄, X ∈ legal → Y ∈ legal → X ∪ Y ∈ legal) :
    completions legal (supportUnions A A) = completions legal A := by
  apply Set.Subset.antisymm
  · apply completion_antitone
    intro S hs
    exact ⟨S, hs, S, hs, Finset.union_self _⟩
  · simpa using (inter_subset_completion_product (A := A) (B := A) closed)

private theorem inter_product_inter {legal A B : Set (Finset V)}
    (closed : ∀ ⦃X Y⦄, X ∈ legal → Y ∈ legal → X ∪ Y ∈ legal) :
    completions legal (supportUnions A B) ∩ (completions legal A ∩ completions legal B) =
      completions legal A ∩ completions legal B :=
  Set.inter_eq_right.mpr (inter_subset_completion_product closed)

private def joinWords (a b c : Role) (s t : CoreTerm Role V) : CoreTerm Role V :=
  choiceTerm c (choiceTerm a s t) (choiceTerm b s t)

private theorem completion_joinWords (a b c : Role) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (legal : Role → Set (Finset V)) (r : Role) (s t : CoreTerm Role V)
    (closed : ∀ ⦃X Y⦄, X ∈ legal r → Y ∈ legal r → X ∪ Y ∈ legal r) :
    wordCompletions legal r (joinWords a b c s t) =
      wordCompletions legal r s ∩ wordCompletions legal r t := by
  unfold wordCompletions joinWords
  by_cases ra : r = a
  · subst r
    rw [foreign_supports ac.symm, owned_supports, foreign_supports ab.symm, completion_union,
      completion_union]
    exact inter_product_inter closed
  by_cases rb : r = b
  · subst r
    rw [foreign_supports bc.symm, foreign_supports ab, owned_supports, completion_union,
      completion_union, Set.inter_comm]
    exact inter_product_inter closed
  by_cases rc : r = c
  · subst r
    rw [owned_supports, foreign_supports ac, foreign_supports bc, completion_square closed,
      completion_union]
  · rw [foreign_supports (Ne.symm rc), foreign_supports (Ne.symm ra), foreign_supports (Ne.symm rb),
      Set.union_self, completion_union]

/-- If the product has a word with universal completion sets, any tuple of
separately attainable completion sets is jointly attained by one word. -/
theorem exists_word_with_completions [Fintype Role]
    (a b c : Role) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (legal : Role → Set (Finset V))
    (closed : ∀ r ⦃X Y⦄, X ∈ legal r → Y ∈ legal r → X ∪ Y ∈ legal r)
    (neutral : CoreTerm Role V) (safe : ∀ q, wordCompletions legal q neutral = Set.univ)
    (parts : Role → CoreTerm Role V) :
    ∃ t : CoreTerm Role V, ∀ r, wordCompletions legal r t = wordCompletions legal r (parts r) := by
  classical
  suffices build : ∀ owners : Finset Role, ∃ t : CoreTerm Role V, ∀ q,
      wordCompletions legal q t =
        if q ∈ owners then wordCompletions legal q (parts q) else Set.univ by
    obtain ⟨t, ht⟩ := build Finset.univ
    exact ⟨t, fun q => by simpa using ht q⟩
  intro owners
  induction owners using Finset.induction_on with
  | empty => exact ⟨neutral, fun q => by simpa using safe q⟩
  | insert owner rest fresh ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨ctx, hctx⟩ := exists_padding_context legal (Finset.univ.erase owner) neutral safe
    refine ⟨joinWords a b c t (ctx.plug (parts owner)), fun q => ?_⟩
    rw [completion_joinWords a b c ab ac bc legal q _ _ (closed q), ht, hctx]
    by_cases eq : q = owner
    · subst q
      simp [fresh]
    · simp [eq]

/-- Universal padding makes each individual completion set observable by a
one-hole context in the joint legality language. -/
theorem joint_context_eq_iff [Fintype Role] (legal : Role → Set (Finset V))
    (neutral : CoreTerm Role V) (safe : ∀ q, wordCompletions legal q neutral = Set.univ)
    (s t : CoreTerm Role V) :
    (∀ r, wordCompletions legal r s = wordCompletions legal r t) ↔
      ∀ ctx : Context Role V,
        (∀ r, Supports r (ctx.plug s) ⊆ legal r) ↔
        (∀ r, Supports r (ctx.plug t) ⊆ legal r) := by
  classical
  constructor
  · intro eq ctx
    exact forall_congr' fun r => (completion_eq_iff r s t).mp (eq r) ctx
  · intro joint r
    apply (completion_eq_iff r s t).mpr
    intro ctx
    obtain ⟨pad, hp⟩ := exists_padding_context legal (Finset.univ.erase r) neutral safe
    have atRoot (u : CoreTerm Role V) :
        (∀ q, Supports q ((pad.comp ctx).plug u) ⊆ legal q) ↔ Supports r (ctx.plug u) ⊆ legal r := by
      simp only [Context.plug_comp, legal_iff_empty]
      change (∀ q, ∅ ∈ wordCompletions legal q (pad.plug (ctx.plug u))) ↔
        ∅ ∈ wordCompletions legal r (ctx.plug u)
      refine ⟨fun h => ?_, fun h q => ?_⟩
      · simpa [hp] using h r
      · by_cases e : q = r
        · subst q
          simpa [hp] using h
        · simp [hp, e]
    exact (atRoot s).symm.trans ((joint (pad.comp ctx)).trans (atRoot t))

end KFOL.Core.PruningContexts
