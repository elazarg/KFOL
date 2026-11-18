module

public import KFOL.Core.CompulsoryPruning

/-! # Context equivalence at a single pruning owner -/

@[expose] public section
namespace KFOL.Core.PruningContexts

open ProfileBudgets CompulsoryPruning
variable {Role V : Type*} [DecidableEq V]

/-- Extra labels that make every support in the family legal. -/
def completions (legal supports : Set (Finset V)) : Set (Finset V) :=
  {extra | ∀ support ∈ supports, support ∪ extra ∈ legal}

/-- Families are multiplied by taking all pairwise unions. -/
def supportUnions (A B : Set (Finset V)) : Set (Finset V) :=
  {combined | ∃ first ∈ A, ∃ second ∈ B, first ∪ second = combined}

theorem completion_symm {legal A B : Set (Finset V)} :
    A ⊆ completions legal B ↔ B ⊆ completions legal A := by
  constructor <;> intro sub x hx y hy
  · exact Finset.union_comm y x ▸ sub hy x hx
  · exact Finset.union_comm y x ▸ sub hy x hx

theorem completion_antitone (legal : Set (Finset V)) :
    Antitone (completions legal) :=
  fun _ _ sub _ h _ mem => h _ (sub mem)

theorem completion_union (legal A B : Set (Finset V)) :
    completions legal (A ∪ B) = completions legal A ∩ completions legal B := by
  ext extra
  change (∀ support, support ∈ A ∨ support ∈ B → support ∪ extra ∈ legal) ↔ _
  exact ⟨fun h => ⟨fun _ hs => h _ (.inl hs), fun _ hs => h _ (.inr hs)⟩,
    fun ⟨left, right⟩ _ h => h.elim (left _) (right _)⟩

theorem mem_completion_product (legal A B : Set (Finset V)) (extra : Finset V) :
    extra ∈ completions legal (supportUnions A B) ↔
      ∀ support ∈ B, support ∪ extra ∈ completions legal A := by
  constructor
  · intro h second hs first hf
    rw [← Finset.union_assoc]
    exact h _ ⟨first, hf, second, hs, rfl⟩
  · intro h combined hc
    obtain ⟨first, hf, second, hs, rfl⟩ := hc
    rw [Finset.union_assoc]
    exact h second hs first hf

theorem supportUnions_comm (A B : Set (Finset V)) : supportUnions A B = supportUnions B A := by
  ext support
  change (∃ first ∈ A, ∃ second ∈ B, first ∪ second = support) ↔
    (∃ second ∈ B, ∃ first ∈ A, second ∪ first = support)
  constructor <;> rintro ⟨first, hf, second, hs, e⟩
  · exact ⟨second, hs, first, hf, (Finset.union_comm _ _).trans e⟩
  · exact ⟨second, hs, first, hf, (Finset.union_comm _ _).trans e⟩

theorem completion_product_congr {legal A B C D : Set (Finset V)}
    (left : completions legal A = completions legal B)
    (right : completions legal C = completions legal D) :
    completions legal (supportUnions A C) = completions legal (supportUnions B D) := by
  have changeLeft {X Y Z : Set (Finset V)} (eq : completions legal X = completions legal Y) :
      completions legal (supportUnions X Z) = completions legal (supportUnions Y Z) := by
    ext extra
    rw [mem_completion_product, mem_completion_product, eq]
  rw [changeLeft left, supportUnions_comm B C, changeLeft right, supportUnions_comm D B]

/-- Equal completion sets are equivalent to equal closed support families. -/
def hull (legal A : Set (Finset V)) : Set (Finset V) :=
  completions legal (completions legal A)

theorem subset_hull (legal A : Set (Finset V)) : A ⊆ hull legal A :=
  completion_symm.mp Set.Subset.rfl

@[simp] theorem completion_hull (legal A : Set (Finset V)) :
    completions legal (hull legal A) = completions legal A := by
  exact Set.Subset.antisymm (completion_antitone legal (subset_hull legal A))
    (subset_hull legal (completions legal A))

theorem hull_product (legal A B : Set (Finset V)) :
    hull legal (supportUnions (hull legal A) (hull legal B)) =
      hull legal (supportUnions A B) := by
  exact congrArg (completions legal)
    (completion_product_congr (completion_hull legal A) (completion_hull legal B))

theorem completion_union_closed {legal A : Set (Finset V)}
    (closed : ∀ ⦃S T⦄, S ∈ legal → T ∈ legal → S ∪ T ∈ legal)
    {S T : Finset V} (hs : S ∈ completions legal A) (ht : T ∈ completions legal A) :
    S ∪ T ∈ completions legal A := by
  intro support hm
  have eq : (support ∪ S) ∪ (support ∪ T) = support ∪ (S ∪ T) := by
    ext v
    simp only [Finset.mem_union]
    tauto
  exact eq ▸ closed (hs support hm) (ht support hm)

theorem hull_product_self {legal A : Set (Finset V)}
    (closed : ∀ ⦃S T⦄, S ∈ legal → T ∈ legal → S ∪ T ∈ legal) :
    hull legal (supportUnions (hull legal A) (hull legal A)) = hull legal A := by
  suffices supportUnions (hull legal A) (hull legal A) = hull legal A by
    rw [this]
    exact congrArg (completions legal) (completion_hull legal A)
  apply Set.Subset.antisymm
  · rintro _ ⟨first, hf, second, hs, rfl⟩
    exact completion_union_closed closed hf hs
  · intro support hs
    exact ⟨support, hs, support, hs, Finset.union_self _⟩

variable [DecidableEq Role]

/-- A term with a single hole and an ordinary word at each sibling. -/
inductive Context (Role V : Type*) where
  | hole
  | left (owner : Role) (next : Context Role V) (sibling : CoreTerm Role V)
  | right (owner : Role) (sibling : CoreTerm Role V) (next : Context Role V)

def Context.plug (t : CoreTerm Role V) : Context Role V → CoreTerm Role V
  | .hole => t
  | .left q next sib => choiceTerm q (next.plug t) sib
  | .right q sib next => choiceTerm q sib (next.plug t)

def Context.comp : Context Role V → Context Role V → Context Role V
  | .hole, inner => inner
  | .left q next sib, inner => .left q (next.comp inner) sib
  | .right q sib next, inner => .right q sib (next.comp inner)

omit [DecidableEq Role] [DecidableEq V] in
@[simp] theorem Context.plug_comp (outer inner : Context Role V) (t : CoreTerm Role V) :
    (outer.comp inner).plug t = outer.plug (inner.plug t) := by
  induction outer <;> simp_all [Context.comp, Context.plug]

theorem owned_supports (r : Role) (s t : CoreTerm Role V) :
    Supports r (choiceTerm r s t) = supportUnions (Supports r s) (Supports r t) :=
  Set.ext fun _ => owned

theorem foreign_supports {r q : Role} (ne : q ≠ r) (s t : CoreTerm Role V) :
    Supports r (choiceTerm q s t) = Supports r s ∪ Supports r t :=
  Set.ext fun _ => foreign ne

theorem completion_context_congr {legal : Set (Finset V)} {r : Role} {u v : CoreTerm Role V}
    (eq : completions legal (Supports r u) = completions legal (Supports r v))
    (ctx : Context Role V) :
    completions legal (Supports r (ctx.plug u)) = completions legal (Supports r (ctx.plug v)) := by
  induction ctx with
  | hole => exact eq
  | left q next sib ih =>
    simp only [Context.plug]
    by_cases e : q = r
    · subst q
      simp only [owned_supports]
      exact completion_product_congr ih rfl
    · simp only [foreign_supports e, completion_union, ih]
  | right q sib next ih =>
    simp only [Context.plug]
    by_cases e : q = r
    · subst q
      simp only [owned_supports]
      exact completion_product_congr rfl ih
    · simp only [foreign_supports e, completion_union, ih]

/-- A nonempty support is the sole pruning support of its owned fold. -/
theorem exists_single_support (r : Role) (extra : Finset V) (hn : extra.Nonempty) :
    ∃ t : CoreTerm Role V, Supports r t = {extra} := by
  induction extra using Finset.induction_on with
  | empty => simp at hn
  | insert x S _ ih =>
    by_cases he : S = ∅
    · subst S
      exact ⟨.var x, rfl⟩
    · obtain ⟨t, ht⟩ := ih (Finset.nonempty_iff_ne_empty.mpr he)
      refine ⟨choiceTerm r (.var x) t, ?_⟩
      rw [owned_supports, ht]
      ext H
      change (∃ A : Finset V, A = {x} ∧ ∃ B : Finset V, B = S ∧ A ∪ B = H) ↔ H = insert x S
      simp [eq_comm]

theorem legal_iff_empty (legal A : Set (Finset V)) :
    A ⊆ legal ↔ ∅ ∈ completions legal A := by
  exact ⟨fun h _ hs => by simpa using h hs, fun h _ hs => by simpa using h _ hs⟩

/-- Completion sets are exactly contextual equivalence for legality at
one owner. Each distinguishing completion is an owned fold context. -/
theorem completion_eq_iff {legal : Set (Finset V)} (r : Role) (s t : CoreTerm Role V) :
    completions legal (Supports r s) = completions legal (Supports r t) ↔
      ∀ ctx : Context Role V,
        Supports r (ctx.plug s) ⊆ legal ↔ Supports r (ctx.plug t) ⊆ legal := by
  constructor
  · intro eq ctx
    rw [legal_iff_empty, legal_iff_empty, completion_context_congr eq ctx]
  · intro test
    ext extra
    by_cases he : extra = ∅
    · subst extra
      specialize test .hole
      simpa only [Context.plug, legal_iff_empty] using test
    · obtain ⟨fold, hf⟩ := exists_single_support r extra (Finset.nonempty_iff_ne_empty.mpr he)
      specialize test (.left r .hole fold)
      simpa only [legal_iff_empty, Context.plug, owned_supports, hf, mem_completion_product,
        Set.mem_singleton_iff, forall_eq, Finset.union_empty] using test

end KFOL.Core.PruningContexts
