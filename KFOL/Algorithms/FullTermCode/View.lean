module

public import KFOL.Algorithms.FullTermCode

/-! # Faithful explicit-array encoding of original public terms, uniformly in K -/

@[expose] public section

namespace KFOL.FullTermCode

@[simp] theorem permutationArray_length {K : ℕ} (p : Equiv.Perm (Fin K)) :
    (permutationArray p).length = K := by simp [permutationArray]

@[simp] theorem permutationArray_getD {K : ℕ} (p : Equiv.Perm (Fin K)) (i : Fin K) :
    (permutationArray p).getD i.val 0 = (p i).val := by simp [permutationArray]

theorem permutationArray_injective {K : ℕ} :
    Function.Injective (permutationArray (K := K)) := by
  intro p q he
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  have hi := congrArg (fun values : List ℕ => values.getD i.val 0) he
  simpa only [permutationArray_getD] using hi

/-- Retaining actual forward arrays rather than a finite operation number
preserves every original constructor and role permutation. -/
theorem view_injective {K : ℕ} : Function.Injective (view (K := K)) := by
  intro term
  induction term with
  | var name =>
    intro other he
    cases other with
    | var name' => simpa only [view,FirstOrder.Language.Term.var.injEq,KFOL.Term.var.injEq] using he
    | winner => cases he
    | choice => cases he
    | rename => cases he
  | winner role =>
    intro other he
    cases other with
    | var => cases he
    | winner role' =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hs : RawSymbol.winner role.val = RawSymbol.winner role'.val := eq_of_heq hf.2.1
      have hr : role = role' := Fin.ext (RawSymbol.winner.inj hs)
      exact congrArg KFOL.Term.winner hr
    | choice =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (0:ℕ) = 2 := hf.1
      omega
    | rename =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (0:ℕ) = 1 := hf.1
      omega
  | choice owner left right hl hr =>
    intro other he
    cases other with
    | var => cases he
    | winner =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (2:ℕ) = 0 := hf.1
      omega
    | rename =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (2:ℕ) = 1 := hf.1
      omega
    | choice owner' left' right' =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hs : RawSymbol.choice owner.val = RawSymbol.choice owner'.val := eq_of_heq hf.2.1
      have ho : owner = owner' := Fin.ext (RawSymbol.choice.inj hs)
      have ha : (fun i : Fin 2 => if i=0 then view left else view right) =
          (fun i : Fin 2 => if i=0 then view left' else view right') := eq_of_heq hf.2.2
      have hleft : left = left' := hl (by simpa using congrFun ha 0)
      have hright : right = right' := hr (by simpa using congrFun ha 1)
      rw [ho,hleft,hright]
  | rename p term ih =>
    intro other he
    cases other with
    | var => cases he
    | winner =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (1:ℕ) = 0 := hf.1
      omega
    | choice =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hh : (1:ℕ) = 2 := hf.1
      omega
    | rename q other =>
      have hf := FirstOrder.Language.Term.func.inj he
      have hs : RawSymbol.rename (permutationArray p) = RawSymbol.rename (permutationArray q) :=
        eq_of_heq hf.2.1
      have hp : p = q := permutationArray_injective (RawSymbol.rename.inj hs)
      have ha : (fun _ : Fin 1 => view term) = (fun _ : Fin 1 => view other) := eq_of_heq hf.2.2
      have ht : term = other := ih (congrFun ha 0)
      rw [hp,ht]

/-- The complete original uniform input embedding is faithful, including K
itself. Binary K is data, rather than a hidden fixed-signature parameter. -/
theorem encodeInput_injective : Function.Injective encodeInput := by
  rintro ⟨K,term⟩ ⟨L,other⟩ he
  have hh := congrArg Words.unpair? he
  simp only [encodeInput,Words.unpair?_pair,Option.some.injEq,Prod.mk.injEq] at hh
  have hK := congrArg Words.BinaryNatCode.decode? hh.1
  simp only [Words.BinaryNatCode.decode?_encode,Option.some.injEq] at hK
  subst L
  have ht := view_injective (encode_injective hh.2)
  cases ht
  rfl

/-- Uniform equation codes are faithful without numbering the operation
alphabet or the ambient permutation group. -/
theorem encodeEquationInput_injective : Function.Injective encodeEquationInput := by
  rintro ⟨K,left,right⟩ ⟨L,left',right'⟩ he
  have hh := congrArg Words.unpair? he
  simp only [encodeEquationInput,Words.unpair?_pair,Option.some.injEq,Prod.mk.injEq] at hh
  have hK := congrArg Words.BinaryNatCode.decode? hh.1
  simp only [Words.BinaryNatCode.decode?_encode,Option.some.injEq] at hK
  subst L
  have hp := congrArg Words.unpair? hh.2
  simp only [Words.unpair?_pair,Option.some.injEq,Prod.mk.injEq] at hp
  have hl := view_injective (encode_injective hp.1)
  have hr := view_injective (encode_injective hp.2)
  cases hl; cases hr
  rfl

end KFOL.FullTermCode
