module

public import KFOL.Definitions.Circuits

/-! Acyclic native circuits over arbitrary finitary mathlib signatures.
Gate references are ordinal cache indices; variable labels remain sparse. -/

@[expose] public section

namespace KFOL.Circuit

universe u v w

/- Nodes contain either an original input name or one original operation
with its correctly typed finite vector of prior-node references. -/
namespace Gate

variable {σ : ℕ → Type u} {Var : Type v} {M : Type w}

@[simp] theorem references_input (j : Var) : references (.input j : Gate σ Var) = [] := rfl
@[simp] theorem references_func {n : ℕ} (f : σ n) (refs : Fin n → ℕ) :
    references (.func f refs : Gate σ Var) = List.ofFn refs := rfl
@[simp] theorem length_references_func {n : ℕ} (f : σ n) (refs : Fin n → ℕ) :
    (references (.func f refs : Gate σ Var)).length = n := by simp [references]

@[simp] theorem eval_input [(Equational.language σ).Structure M] (valuation : Var → M)
    (cache : List M) (j : Var) : eval valuation cache (.input j : Gate σ Var) = some (valuation j) := rfl

/- Finite acyclic validation guarantees an actual value at a gate. -/
theorem eval_some_of_valid [(Equational.language σ).Structure M] (valuation : Var → M)
    (cache : List M) (gate : Gate σ Var) (hgate : gate.ValidAt cache.length) :
    ∃ value : M, gate.eval valuation cache = some value := by
  cases gate with
  | input j => exact ⟨valuation j, rfl⟩
  | func f refs =>
    exact ⟨_, dite_eq_left hgate⟩

end Gate

/- Topological validation from a current prefix length. This definition
inspects the finite graph and does not mention valuations or evaluation. -/
namespace Equation

variable {σ : ℕ → Type u} {Var : Type v} {M : Type w}

end Equation

/- The fixed argument order of the external vector view is numeric Fin
order, inherited from List.ofFn, rather than any Fintype numbering. -/
theorem getElem_references {σ : ℕ → Type u} {Var : Type v} {n : ℕ}
    (f : σ n) (refs : Fin n → ℕ) (i : Fin n) :
    (Gate.references (.func f refs : Gate σ Var))[i.val]'(by simp) = refs i := by
  simp [Gate.references]

/- Cache evaluation appends exactly one value per original gate. This also
proves that all earlier cache indices retain their values. -/
theorem runFrom_total {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (valuation : Var → M)
    (gates : List (Gate σ Var)) (cache : List M) (hvalid : ValidFrom cache.length gates) :
    ∃ suffix : List M, runFrom valuation gates cache = some (cache ++ suffix) ∧ suffix.length = gates.length := by
  induction gates generalizing cache with
  | nil => exact ⟨[], by simp [runFrom], rfl⟩
  | cons gate gates ih =>
    obtain ⟨value, he⟩ := gate.eval_some_of_valid valuation cache hvalid.1
    have hrest : ValidFrom (cache ++ [value]).length gates := by
      simpa only [List.length_append, List.length_singleton] using hvalid.2
    obtain ⟨suffix, hs, hl⟩ := ih (cache ++ [value]) hrest
    refine ⟨value :: suffix, ?_, by simp only [List.length_cons, hl]⟩
    rw [runFrom, he]
    change runFrom valuation gates (cache ++ [value]) = some (cache ++ value :: suffix)
    simpa only [List.append_assoc, List.singleton_append] using hs

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w

theorem validFrom_append {σ : ℕ → Type u} {Var : Type v} (position : ℕ)
    (first second : List (Gate σ Var)) :
    ValidFrom position (first ++ second) ↔
      ValidFrom position first ∧ ValidFrom (position + first.length) second := by
  induction first generalizing position with
  | nil => simp [ValidFrom]
  | cons gate first ih =>
    simp only [List.cons_append, ValidFrom, ih, List.length_cons]
    have he : position + 1 + first.length = position + (first.length + 1) := by omega
    rw [he]
    tauto

theorem runFrom_append {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (valuation : Var → M)
    (first second : List (Gate σ Var)) (cache : List M) :
    runFrom valuation (first ++ second) cache =
      (runFrom valuation first cache).bind (fun cachedValues => runFrom valuation second cachedValues) := by
  induction first generalizing cache with
  | nil => rfl
  | cons gate first ih =>
    simp only [List.cons_append, runFrom]
    cases he : gate.eval valuation cache with
    | none => rfl
    | some value => exact ih (cache ++ [value])

/- A well-formed circuit equation has two actual cached output values for
all valuations; none is never used to certify equality. -/
theorem Equation.eval_some_of_wellFormed {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (equation : Equation σ Var)
    (hwf : equation.WellFormed) (valuation : Var → M) :
    ∃ left right : M, equation.eval valuation = some (left, right) := by
  obtain ⟨suffix, hr, hl⟩ := runFrom_total valuation equation.gates [] hwf.1
  simp only [List.nil_append] at hr
  have hleft : equation.left < suffix.length := hl ▸ hwf.2.1
  have hright : equation.right < suffix.length := hl ▸ hwf.2.2
  refine ⟨suffix[equation.left]'hleft, suffix[equation.right]'hright, ?_⟩
  rw [Equation.eval, hr]
  change (do
    let left ← suffix[equation.left]?
    let right ← suffix[equation.right]?
    pure (left, right)) = _
  rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright]
  rfl

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w w'

/- A structure homomorphism acts on the actual cache, preserving all refs. -/
theorem Gate.eval_map {σ : ℕ → Type u} {Var : Type v} {M : Type w} {N : Type w'}
    [(Equational.language σ).Structure M] [(Equational.language σ).Structure N]
    (f : M → N)
    (hmap : ∀ {n} (symbol : σ n) (args : Fin n → M),
      f (FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol args) =
        FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol (fun i => f (args i)))
    (valuation : Var → M) (cache : List M) (gate : Gate σ Var) :
    gate.eval (fun j => f (valuation j)) (cache.map f) = (gate.eval valuation cache).map f := by
  cases gate with
  | input j => rfl
  | func symbol refs =>
    simp only [Gate.eval, List.length_map]
    split_ifs with h
    · simp only [Option.map_some, List.getElem_map]
      exact congrArg some (hmap symbol (fun i => cache[refs i]'(h i))).symm
    · rfl

theorem runFrom_map {σ : ℕ → Type u} {Var : Type v} {M : Type w} {N : Type w'}
    [(Equational.language σ).Structure M] [(Equational.language σ).Structure N]
    (f : M → N)
    (hmap : ∀ {n} (symbol : σ n) (args : Fin n → M),
      f (FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol args) =
        FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol (fun i => f (args i)))
    (valuation : Var → M) (gates : List (Gate σ Var)) (cache : List M) :
    runFrom (fun j => f (valuation j)) gates (cache.map f) =
      (runFrom valuation gates cache).map (List.map f) := by
  induction gates generalizing cache with
  | nil => rfl
  | cons gate gates ih =>
    rw [runFrom, Gate.eval_map f hmap]
    cases he : gate.eval valuation cache with
    | none => simp [runFrom, he]
    | some value =>
      change runFrom (fun j => f (valuation j)) gates (cache.map f ++ [f value]) = _
      rw [show cache.map f ++ [f value] = (cache ++ [value]).map f from by simp only [List.map_append, List.map_singleton],
        ih]
      rw [runFrom, he]
      rfl

theorem Equation.eval_map {σ : ℕ → Type u} {Var : Type v} {M : Type w} {N : Type w'}
    [(Equational.language σ).Structure M] [(Equational.language σ).Structure N]
    (f : M → N)
    (hmap : ∀ {n} (symbol : σ n) (args : Fin n → M),
      f (FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol args) =
        FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol (fun i => f (args i)))
    (valuation : Var → M) (equation : Equation σ Var) :
    equation.eval (fun j => f (valuation j)) =
      (equation.eval valuation).map (fun p => (f p.1, f p.2)) := by
  have hrun := runFrom_map f hmap valuation equation.gates []
  simp only [List.map_nil] at hrun
  unfold eval
  rw [hrun]
  cases he : runFrom valuation equation.gates [] with
  | none => rfl
  | some cache =>
    simp only [Option.map_some]
    change (do
      let left ← (cache.map f)[equation.left]?
      let right ← (cache.map f)[equation.right]?
      pure (left, right)) =
      Option.map (fun p => (f p.1, f p.2)) (do
        let left ← cache[equation.left]?
        let right ← cache[equation.right]?
        pure (left, right))
    simp only [List.getElem?_map]
    cases hl : cache[equation.left]? <;> cases hr : cache[equation.right]? <;> rfl

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w

variable {σ : ℕ → Type u} {Var : Type v} {M : Type w}
variable [(Equational.language σ).Structure M]

theorem Gate.validAt_of_eval_eq_some (valuation : Var → M) (cache : List M)
    (gate : Gate σ Var) {value : M} (h : gate.eval valuation cache = some value) :
    gate.ValidAt cache.length := by
  cases gate with
  | input j => trivial
  | func symbol refs =>
    change ∀ i, refs i < cache.length
    by_contra hv
    have hn : (Gate.func symbol refs : Gate σ Var).eval valuation cache = none := dite_eq_right hv
    cases hn.symm.trans h

theorem runFrom_spec_of_eq_some (valuation : Var → M) (gates : List (Gate σ Var)) (cache : List M)
    {result : List M} (h : runFrom valuation gates cache = some result) :
    ValidFrom cache.length gates ∧ result.length = cache.length + gates.length := by
  induction gates generalizing cache with
  | nil =>
    cases Option.some.inj h
    exact ⟨trivial, by simp⟩
  | cons gate gates ih =>
    obtain ⟨value, hg, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hvalid, hlength⟩ := ih (cache ++ [value]) hr
    refine ⟨⟨gate.validAt_of_eval_eq_some valuation cache hg, ?_⟩, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using hvalid
    · simp only [List.length_append, List.length_singleton] at hlength
      simp only [List.length_cons]
      omega

theorem Equation.wellFormed_of_eval_eq_some (equation : Equation σ Var) (valuation : Var → M)
    {result : M × M} (h : equation.eval valuation = some result) : equation.WellFormed := by
  unfold eval at h
  obtain ⟨cache, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨left, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨right, hr, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hvalid, hlen⟩ := runFrom_spec_of_eq_some valuation equation.gates [] hc
  simp only [List.length_nil, Nat.zero_add] at hvalid hlen
  refine ⟨hvalid, ?_, ?_⟩
  · rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hl).1
  · rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hr).1

theorem Equation.eval_eq_none_of_not_wellFormed (equation : Equation σ Var)
    (h : ¬equation.WellFormed) (valuation : Var → M) : equation.eval valuation = none := by
  cases he : equation.eval valuation with
  | none => rfl
  | some result => exact (h (equation.wellFormed_of_eval_eq_some valuation he)).elim

end KFOL.Circuit
