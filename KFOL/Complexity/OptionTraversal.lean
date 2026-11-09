module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-! # Native polynomial-time traversal of partial list callbacks -/

@[expose] public section

namespace KFOL.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

private theorem mapM_eq_all_getD {α β : Type} (f : α → Option β) (fallback : β) (xs : List α) :
    xs.mapM f = if xs.all (fun x => (f x).isSome) then
      some (xs.map (fun x => (f x).getD fallback)) else none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf]
    | some y =>
      simp only [List.mapM_cons, hf, List.all_cons, Option.isSome_some, Bool.true_and,
        List.map_cons, Option.getD_some]
      rw [ih]
      cases xs.all _ <;> rfl

/-- A complete traversal of a certified partial callback is polynomial-time.
The input list and every callback output are charged by the native machine
calculus. The fallback is used only by the implementation when testing a
failing callback, and cannot appear in a successful result. -/
theorem mapMWithInput_polyTime
    {Input Element Value : Type} {input : Input ↪ List Bool}
    {elementEncoding : Element ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {list : Input → List Element} {f : Input → Element → Option Value}
    (hlist : ComputableInPolyTime list input (encList elementEncoding))
    (hf : ComputableInPolyTime (fun p : Input × Element => f p.1 p.2)
      (encPair input elementEncoding) (encOption valueEncoding))
    (fallback : Value) :
    ComputableInPolyTime (fun x => (list x).mapM (f x)) input
      (encOption (encList valueEncoding)) := by
  have hflag := hf.optionIsSome
  have hall := allWithInput (test := fun x value => (f x value).isSome) hlist hflag
  have hvalue := hf.optionGetDWithInput (const fallback)
  have hmap := mapWithInput (f := fun x value => (f x value).getD fallback) hlist hvalue
  have h := hall.ite ((optionSome (encList valueEncoding)).comp hmap) (const none)
  convert h using 1
  funext x
  exact mapM_eq_all_getD (f x) fallback (list x)

/-- Combine two complete partial computations over one captured input. Both
outputs and their shared input are charged by the native calculus. -/
theorem optionPairWithInput_polyTime {Input Left Right : Type}
    {input : Input ↪ List Bool} {leftEncoding : Left ↪ List Bool} {rightEncoding : Right ↪ List Bool}
    {left : Input → Option Left} {right : Input → Option Right}
    (hleft : ComputableInPolyTime left input (encOption leftEncoding))
    (hright : ComputableInPolyTime right input (encOption rightEncoding)) :
    ComputableInPolyTime (fun x => (left x).bind (fun a => (right x).map (fun b => (a, b))))
      input (encOption (encPair leftEncoding rightEncoding)) := by
  have hr := hright.comp (fst input leftEncoding)
  have ha : ComputableInPolyTime (fun p : (Input × Left) × Right => p.1.2)
      (encPair (encPair input leftEncoding) rightEncoding) leftEncoding := by fun_prop
  have hb := snd (encPair input leftEncoding) rightEncoding
  have hpair := hr.optionMapWithInput (f := fun (p : Input × Left) b => (p.2, b)) (ha.prod hb)
  have h := hleft.optionElimWithInput
    (body := fun x a => (right x).map (fun b => (a, b))) (const none) hpair
  convert h using 1
  funext x
  cases left x <;> rfl

end KFOL.Complexity
