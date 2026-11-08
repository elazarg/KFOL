module

public import KFOL.Algebra

/-! Equal supports determine the ambiguous restriction, but can distinguish
public operations on atomic inputs. This guards the restriction in the clone
statement. Nonempty supports also exclude a nullary core expression. -/

@[expose] public section

namespace KFOLTest.SemilatticeTrace

open KFOL

private def s : Term (Fin 3) Bool := .choice 0 (.var false) (.var true)
private def t : Term (Fin 3) Bool := .choice 1 (.var false) (.var true)

example : s.vars = t.vars := rfl

example (v : Bool → WinnerSet (Fin 3)) (hv : ∀ x, WinnerSet.Ambiguous (v x)) :
    s.eval v = t.eval v := by
  apply ((show s.IsCore from ⟨trivial, trivial⟩).equal_on_ambiguous_iff_vars_eq
    (show t.IsCore from ⟨trivial, trivial⟩) (Function.Embedding.refl _)).mpr rfl v hv

example : s.eval (fun x => if x then WinnerSet.singleton 1 else WinnerSet.singleton 0) ≠
    t.eval (fun x => if x then WinnerSet.singleton 1 else WinnerSet.singleton 0) := by
  simp [s, t, Term.eval, WinnerSet.choice]

example (closed : Term (Fin 3) (Fin 0)) : ¬closed.IsCore := by
  intro h
  obtain ⟨x, _⟩ := h.vars_nonempty
  exact Fin.elim0 x

end KFOLTest.SemilatticeTrace
