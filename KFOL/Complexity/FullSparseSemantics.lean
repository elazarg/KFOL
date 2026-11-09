module
public import KFOL.Complexity.FullSparseBounds
public import KFOL.Algorithms.FullTermCode.View
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Bool.Basic
@[expose] public section
namespace KFOL.Complexity.FullSparseEvaluation
open KFOL.FullTermCode

def asSet (value : Value) : Set ℕ := {role | role ∈ value}
def Represents {K : ℕ} (value : Value) (winner : WinnerSet (Fin K)) : Prop :=
  asSet value = Fin.val '' winner.val

@[simp] theorem asSet_singleton (role : ℕ) : asSet [role] = {role} := by
  ext j
  simp [asSet]
@[simp] theorem asSet_append (left right : Value) : asSet (left ++ right) = asSet left ∪ asSet right := by
  ext j
  simp [asSet]

theorem singletonB_iff (owner : ℕ) (value : Value) : singletonB owner value = true ↔ asSet value = {owner} := by
  cases value with
  | nil =>
    simp only [singletonB, List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff]
    intro h
    have hm : owner ∈ asSet [] := by rw [h]; exact Set.mem_singleton _
    exact List.not_mem_nil hm
  | cons first rest =>
    simp only [singletonB, List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      ext j
      change j ∈ first :: rest ↔ j = owner
      constructor
      · exact h j
      · intro hj
        have hf := h first (List.mem_cons_self ..)
        simpa only [hj, hf] using (show first ∈ first :: rest from List.mem_cons_self)
    · intro h j hj
      change j ∈ asSet (first :: rest) at hj
      rw [h] at hj
      exact hj

theorem represents_singleton {K : ℕ} (role : Fin K) : Represents [role.val] (WinnerSet.singleton role) := by
  simp only [Represents, asSet_singleton, WinnerSet.singleton, Set.image_singleton]

theorem represents_union {K : ℕ} {left right : Value} {A B : WinnerSet (Fin K)}
    (hl : Represents left A) (hr : Represents right B) : Represents (left ++ right) (A.union B) := by
  change asSet (left ++ right) = Fin.val '' (A.val ∪ B.val)
  rw [asSet_append, Set.image_union]
  exact congrArg₂ (· ∪ ·) hl hr

theorem represents_equal_iff {K : ℕ} {left right : Value} {A B : WinnerSet (Fin K)}
    (hl : Represents left A) (hr : Represents right B) : asSet left = asSet right ↔ A = B := by
  change asSet left = Fin.val '' A.val at hl
  change asSet right = Fin.val '' B.val at hr
  rw [hl, hr]
  constructor
  · intro h
    apply Subtype.ext
    exact (show Function.Injective (Fin.val : Fin K → ℕ) from Fin.val_injective).image_injective h
  · rintro rfl
    rfl

theorem singletonB_represents_iff {K : ℕ} (owner : Fin K) {value : Value} {A : WinnerSet (Fin K)}
    (h : Represents value A) : singletonB owner.val value = true ↔ A = WinnerSet.singleton owner := by
  rw [singletonB_iff]
  simpa only [asSet_singleton] using represents_equal_iff h (represents_singleton owner)

theorem represents_choice {K : ℕ} (owner : Fin K) {left right : Value} {A B : WinnerSet (Fin K)}
    (hl : Represents left A) (hr : Represents right B) : Represents (choice owner.val left right) (WinnerSet.choice owner A B) := by
  classical
  unfold choice
  split
  next h =>
    have hm : A = WinnerSet.singleton owner ∨ B = WinnerSet.singleton owner := by
      rcases (by simpa only [Bool.or_eq_true] using h : singletonB owner.val left = true ∨ singletonB owner.val right = true) with h | h
      · exact Or.inl ((singletonB_represents_iff owner hl).mp h)
      · exact Or.inr ((singletonB_represents_iff owner hr).mp h)
    rw [WinnerSet.choice, ite_eq_left hm]
    exact represents_singleton owner
  next h =>
    have hm : ¬(A = WinnerSet.singleton owner ∨ B = WinnerSet.singleton owner) := by
      intro he
      apply h
      rcases he with he | he
      · simp only [Bool.or_eq_true]
        exact Or.inl ((singletonB_represents_iff owner hl).mpr he)
      · simp only [Bool.or_eq_true]
        exact Or.inr ((singletonB_represents_iff owner hr).mpr he)
    rw [WinnerSet.choice, ite_eq_right hm]
    exact represents_union hl hr

theorem represents_rename {K : ℕ} (permutation : Equiv.Perm (Fin K)) {value : Value} {A : WinnerSet (Fin K)}
    (h : Represents value A) : Represents (rename (permutationArray permutation) value) (A.rename permutation) := by
  change asSet (value.map (fun role => (permutationArray permutation).getD role 0)) =
    Fin.val '' (permutation '' A.val)
  ext role
  change role ∈ value.map _ ↔ _
  constructor
  · intro hm
    obtain ⟨input, hi, rfl⟩ := List.mem_map.mp hm
    have hin : input ∈ Fin.val '' A.val := h ▸ hi
    obtain ⟨r, hr, he⟩ := hin
    refine ⟨permutation r, ⟨r,hr,rfl⟩, ?_⟩
    rw [← he, permutationArray_getD]
  · rintro ⟨r, ⟨input, hi, rfl⟩, he⟩
    apply List.mem_map.mpr
    refine ⟨input.val, ?_, ?_⟩
    · have hm : input.val ∈ Fin.val '' A.val := ⟨input,hi,rfl⟩
      change input.val ∈ asSet value
      rw [h]
      exact hm
    · rw [permutationArray_getD]
      exact he


/-- The evaluator reads each variable occurrence independently. The dictionary
may include extra original payload labels without constraining valuations. -/
theorem evaluate_view_represents {K : ℕ} (context : Context) (term : KFOL.Term (Fin K) ℕ)
    (valuation : ℕ → WinnerSet (Fin K))
    (hvariables : ∀ j ∈ FullTermSize.labels (view term), Represents (leaf context j) (valuation j)) :
    Represents (evaluate context (view term)) (term.eval valuation) := by
  induction term with
  | winner role => exact represents_singleton role
  | var j => exact hvariables j (List.mem_singleton_self j)
  | choice owner left right hl hr =>
    have hleft : ∀ j ∈ FullTermSize.labels (view left), Represents (leaf context j) (valuation j) := by
      intro j hj
      apply hvariables j
      change j ∈ owner.val :: (FullTermSize.labels (view left) ++ FullTermSize.labels (view right))
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hj)
    have hright : ∀ j ∈ FullTermSize.labels (view right), Represents (leaf context j) (valuation j) := by
      intro j hj
      apply hvariables j
      change j ∈ owner.val :: (FullTermSize.labels (view left) ++ FullTermSize.labels (view right))
      exact List.mem_cons_of_mem _ (List.mem_append_right _ hj)
    change Represents
      (evaluate context (.func (.choice owner.val) (fun i => if i = 0 then view left else view right)))
      (WinnerSet.choice owner (left.eval valuation) (right.eval valuation))
    rw [evaluate_choice]
    exact represents_choice owner (hl hleft) (hr hright)
  | rename permutation term ih =>
    have hchild : ∀ j ∈ FullTermSize.labels (view term), Represents (leaf context j) (valuation j) := by
      intro j hj
      apply hvariables j
      change j ∈ permutationArray permutation ++ FullTermSize.labels (view term)
      exact List.mem_append_right _ hj
    change Represents (evaluate context (.func (.rename (permutationArray permutation)) (fun _ => view term)))
      (WinnerSet.rename permutation (term.eval valuation))
    rw [evaluate_rename]
    exact represents_rename permutation (ih hchild)



def contextRole {K : ℕ} (positive : 0 < K) (context : Context)
    (bounded : ∀ role ∈ context.2, role < K) (index : ℕ) : Fin K :=
  ⟨context.2.getD index 0, by
    rcases getD_mem_or_zero context.2 index with he | hm
    · rw [he]; exact positive
    · exact bounded _ hm⟩

def contextValuation {K : ℕ} (positive : 0 < K) (context : Context)
    (bounded : ∀ role ∈ context.2, role < K) (name : ℕ) : WinnerSet (Fin K) :=
  (WinnerSet.singleton (contextRole positive context bounded (2 * context.1.idxOf name))).union
    (WinnerSet.singleton (contextRole positive context bounded (2 * context.1.idxOf name + 1)))

theorem leaf_represents_contextValuation {K : ℕ} (positive : 0 < K) (context : Context)
    (bounded : ∀ role ∈ context.2, role < K) (name : ℕ) :
    Represents (leaf context name) (contextValuation positive context bounded name) :=
  represents_union
    (represents_singleton (contextRole positive context bounded (2 * context.1.idxOf name)))
    (represents_singleton (contextRole positive context bounded (2 * context.1.idxOf name + 1)))

theorem evaluate_view_contextValuation {K : ℕ} (positive : 0 < K) (context : Context)
    (bounded : ∀ role ∈ context.2, role < K) (term : KFOL.Term (Fin K) ℕ) :
    Represents (evaluate context (view term)) (term.eval (contextValuation positive context bounded)) :=
  evaluate_view_represents context term _ (fun j _ => leaf_represents_contextValuation positive context bounded j)

/-- A canonical flat pair assignment supports ordinary sparse names and
retains the first occurrence lookup convention of the actual machine. -/
def pairValues {K : ℕ} (names : List ℕ) (pairs : ℕ → Fin K × Fin K) : List ℕ :=
  names.flatMap (fun name => [(pairs name).1.val,(pairs name).2.val])

theorem pairValues_bounded {K : ℕ} (names : List ℕ) (pairs : ℕ → Fin K × Fin K) :
    ∀ role ∈ pairValues names pairs, role < K := by
  intro role hm
  obtain ⟨name, _, hm⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact (pairs name).1.isLt
  · exact (pairs name).2.isLt

theorem leaf_pairValues {K : ℕ} (names : List ℕ) (pairs : ℕ → Fin K × Fin K) (name : ℕ) (hm : name ∈ names) :
    leaf (names,pairValues names pairs) name = [(pairs name).1.val,(pairs name).2.val] := by
  induction names with
  | nil => cases hm
  | cons head rest ih =>
    by_cases he : head = name
    · subst head
      simp [leaf,pairValues]
    · have hrest : name ∈ rest := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
      have hr := ih hrest
      simp only [leaf, pairValues, List.flatMap_cons,
        List.idxOf_cons_ne rest he]
      change [(_ :: _ :: pairValues rest pairs).getD (2*(List.idxOf name rest+1)) 0,
        (_ :: _ :: pairValues rest pairs).getD (2*(List.idxOf name rest+1)+1) 0] = _
      rw [show 2*(List.idxOf name rest+1) = 2*List.idxOf name rest+2 by omega,
        show 2*List.idxOf name rest+2+1 = (2*List.idxOf name rest+1)+2 by omega]
      simpa only [leaf, List.getD_cons_succ] using hr

end KFOL.Complexity.FullSparseEvaluation
