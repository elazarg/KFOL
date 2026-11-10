module

public import KFOL.Query.Compilation
public import KFOL.Query.Relations

@[expose] public section
namespace KFOL.Tests.NavigationQueries
open Query

private def neutral : Term (Fin 3) (Fin 2) :=
  .choice 2 (.choice 0 (.var 0) (.var 1)) (.choice 1 (.var 0) (.var 1))

private theorem neutral_public : neutral.IsPublic := ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩

/-- All roles are present, but input zero is empty: the nonemptiness part
of the document schema is essential to the query equivalence claim. -/
private def emptyInput : Document (Fin 3) (Fin 2) (Fin 5) where
  child x y := (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3)) ∨ (x = 3 ∧ y = 4)
  role r x := x.val = r.val + 1
  mark j x := j = 1 ∧ x = 4

example : (Path.union (input 0) (input 1)).Holds emptyInput 0 3 := by
  simp [input,Path.Holds,Test.Holds,emptyInput]
example : ¬(compile neutral neutral_public).Holds emptyInput 0 3 := by
  simp [compile,neutral,nonOwner,input,Path.Holds,Test.Holds,emptyInput,Fin.exists_fin_succ]

/-- On every genuine valuation document the same compiled query is union,
including ambiguous inputs and cases where one of the inner choices absorbs. -/
example (valuation : Fin 2 → WinnerSet (Fin 3)) (r : Fin 3) :
    (compile neutral neutral_public).Holds (document valuation) .root (.role r) ↔
      r ∈ (valuation 0).val ∨ r ∈ (valuation 1).val := by
  have equal : neutral.eval valuation = (valuation 0).union (valuation 1) := by
    exact WinnerSet.three_owner_union (valuation 0) (valuation 1) 0 1 2 (by decide) (by decide) (by decide)
  simp [compile_holds, equal]

/-- The common context must be recovered through the parent axis, not by
testing for children of the candidate result role. -/
private def wrongContext : Path (Fin 3) (Fin 2) :=
  .filter (.union (input 0) (input 1))
    (.or (.role 0) (.exists (.filter .child
      (.and (nonOwner 0 (.var 0) trivial) (nonOwner 0 (.var 1) trivial)))))

private def bothInputs : Document (Fin 3) (Fin 2) (Fin 6) where
  child x y := (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3)) ∨
    (x = 2 ∧ y = 4) ∨ (x = 3 ∧ y = 5)
  role r x := x.val = r.val + 1
  mark j x := (j = 0 ∧ x = 4) ∨ (j = 1 ∧ x = 5)

example : (compile (.choice 0 (.var 0) (.var 1)) ⟨trivial,trivial⟩).Holds bothInputs 0 2 := by
  simp [compile,nonOwner,input,Path.Holds,Test.Holds,bothInputs,Fin.exists_fin_succ]
example : ¬wrongContext.Holds bothInputs 0 2 := by
  simp [wrongContext,nonOwner,input,Path.Holds,Test.Holds,bothInputs,Fin.exists_fin_succ]

end KFOL.Tests.NavigationQueries
