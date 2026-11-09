module

public import KFOL.Algorithms.FullTermCode.View
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-! # Uniform explicit-array validation is exact original syntax recognition -/

@[expose] public section

namespace KFOL.FullTermCode

/-- The physical array check is exactly its length, range, and injectivity.
The length comparison is the first executable check. -/
theorem validArray_iff (K : ℕ) (forward : List ℕ) :
    validArray K forward = true ↔
      forward.length = K ∧ (∀ role ∈ forward, role < K) ∧ forward.Nodup := by
  simp only [validArray]
  by_cases hlen : forward.length = K
  · simp [hlen,List.all_eq_true]
  · simp [hlen]

/-- Every actual original permutation passes the complete stored-array check. -/
@[simp] theorem validArray_permutationArray {K : ℕ} (p : Equiv.Perm (Fin K)) :
    validArray K (permutationArray p) = true := by
  apply (validArray_iff K _).2
  refine ⟨permutationArray_length p,?_,?_⟩
  · intro role hrole
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrole
    exact (p i).isLt
  · rw [permutationArray,List.nodup_ofFn]
    intro i j he
    exact p.injective (Fin.ext he)

/-- A successful physical array check produces an actual role permutation,
with no assumed finite certificate or enumeration of the permutation group. -/
theorem exists_permutation_of_validArray {K : ℕ} {forward : List ℕ}
    (h : validArray K forward = true) :
    ∃ p : Equiv.Perm (Fin K), permutationArray p = forward := by
  obtain ⟨hlen,hrange,hnodup⟩ := (validArray_iff K forward).1 h
  let f : Fin K → Fin K := fun i =>
    ⟨forward[i.val]'(by simpa only [hlen] using i.isLt),
      hrange _ (List.getElem_mem (by simpa only [hlen] using i.isLt))⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hnodup.getElem_inj_iff.mp (congrArg Fin.val he)
  let p : Equiv.Perm (Fin K) := Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  refine ⟨p,?_⟩
  apply List.ext_getElem (by simp only [permutationArray_length,hlen])
  intro i hi hi'
  simp only [permutationArray,List.getElem_ofFn]
  rfl

/-- Every actual original tree passes validation uniformly in K. -/
@[simp] theorem valid_view {K : ℕ} (term : KFOL.Term (Fin K) ℕ) :
    valid K (view term) = true := by
  induction term with
  | var name => rfl
  | winner role => simp [view,valid]
  | choice owner left right hl hr => simp [view,valid,hl,hr]
  | rename p term ih => simp [view,valid,ih]

/-- The independent raw validation accepts precisely the original full-term
syntax at its actual binary role count, including K=0,1,2. -/
theorem exists_original_of_valid {K : ℕ} {raw : Raw} (h : valid K raw = true) :
    ∃ original : KFOL.Term (Fin K) ℕ, view original = raw := by
  induction raw with
  | var name => exact ⟨.var name,rfl⟩
  | @func n operation children ih =>
    cases operation with
    | winner role =>
      have hr : role < K := by simpa only [valid,decide_eq_true_eq] using h
      refine ⟨.winner ⟨role,hr⟩,?_⟩
      simp only [view]
      congr 1
      funext i
      exact Fin.elim0 i
    | choice owner =>
      have hs : owner < K ∧ valid K (children 0) = true ∧ valid K (children 1) = true := by
        simpa only [valid,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
      obtain ⟨left,hl⟩ := ih 0 hs.2.1
      obtain ⟨right,hr⟩ := ih 1 hs.2.2
      refine ⟨.choice ⟨owner,hs.1⟩ left right,?_⟩
      simp only [view]
      congr 1
      funext i
      fin_cases i <;> simp [hl,hr]
    | rename forward =>
      have hs : validArray K forward = true ∧ valid K (children 0) = true := by
        simpa only [valid,Bool.and_eq_true] using h
      obtain ⟨p,hp⟩ := exists_permutation_of_validArray hs.1
      obtain ⟨original,ho⟩ := ih 0 hs.2
      refine ⟨.rename p original,?_⟩
      simp only [view,hp]
      congr 1
      funext i
      fin_cases i
      exact ho

theorem valid_iff (K : ℕ) (raw : Raw) :
    valid K raw = true ↔ ∃ original : KFOL.Term (Fin K) ℕ, view original = raw := by
  constructor
  · exact exists_original_of_valid
  · rintro ⟨original,rfl⟩
    exact valid_view original

end KFOL.FullTermCode
