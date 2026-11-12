module

public import KFOL.Core.Bichain

/-! # Exact recovery of the pure Boolean-projection fiber

The neutral section of a pure term with Boolean restriction a projection
recovers a full three-operation term, or the zero trace. -/

@[expose] public section
namespace KFOL.Bichain
namespace Value

private theorem lower_inf : ∀ x y, lower (inf x y) = (lower x && lower y) := by
  decide +kernel
private theorem lower_sup : ∀ x y, lower (sup x y) = (lower x || lower y) := by
  decide +kernel
private theorem upper_inf : ∀ x y, upper (inf x y) = (upper x && upper y) := by
  decide +kernel
private theorem upper_sup : ∀ x y, upper (sup x y) = (upper x || upper y) := by
  decide +kernel
private theorem ofBool_inf : ∀ x y, ofBool (x && y) = inf (ofBool x) (ofBool y) := by
  decide +kernel
private theorem ofBool_sup : ∀ x y, ofBool (x || y) = sup (ofBool x) (ofBool y) := by
  decide +kernel

private theorem resolves_inf : ∀ w x y z,
    Resolves w x → Resolves y z → Resolves (inf w y) (inf x z) := by
  unfold Resolves
  decide +kernel
private theorem resolves_sup : ∀ w x y z,
    Resolves w x → Resolves y z → Resolves (sup w y) (sup x z) := by
  unfold Resolves
  decide +kernel

private theorem resolveNeutral_resolves : ∀ x, Resolves (resolveNeutral x) x := by
  unfold Resolves
  decide +kernel
private theorem resolveNeutral_ne : ∀ x, resolveNeutral x ≠ .neutral := by
  decide +kernel
private theorem inf_ne_neutral : ∀ x y,
    x ≠ .neutral → y ≠ .neutral → inf x y ≠ .neutral := by
  decide +kernel
private theorem sup_ne_neutral : ∀ x y,
    x ≠ .neutral → y ≠ .neutral → sup x y ≠ .neutral := by
  decide +kernel

private theorem inf_union_left : ∀ x y z,
    inf (union x y) z = union (inf x z) (inf y z) := by
  decide +kernel
private theorem inf_union_right : ∀ x y z,
    inf x (union y z) = union (inf x y) (inf x z) := by
  decide +kernel
private theorem sup_union_left : ∀ x y z,
    sup (union x y) z = union (sup x z) (sup y z) := by
  decide +kernel
private theorem sup_union_right : ∀ x y z,
    sup x (union y z) = union (sup x y) (sup x z) := by
  decide +kernel
private theorem union_possible_iff : ∀ x y,
    union x y = .possible ↔ x = .possible ∨ y = .possible := by
  decide +kernel

private theorem endpoint_inf : ∀ x,
    inf .b x = .b ∧ inf x .b = .b ∧ inf .c x = x ∧ inf x .c = x := by
  decide +kernel
private theorem endpoint_sup : ∀ x,
    sup .c x = .c ∧ sup x .c = .c ∧ sup .b x = x ∧ sup x .b = x := by
  decide +kernel

end Value
namespace Term

variable {Var : Type*}

private theorem pure_eval_lower (t : Term Var) (ht : t.IsPure) (v : Var → Value) :
    t.eval (fun j => Value.ofBool (Value.lower (v j))) =
      Value.ofBool (Value.lower (t.eval v)) := by
  induction t with
  | var => rfl
  | inf s t hs ht' =>
    simp only [IsPure] at ht
    simp only [eval, hs ht.1, ht' ht.2, Value.lower_inf, Value.ofBool_inf]
  | sup s t hs ht' =>
    simp only [IsPure] at ht
    simp only [eval, hs ht.1, ht' ht.2, Value.lower_sup, Value.ofBool_sup]
  | union => exact False.elim ht

private theorem pure_eval_upper (t : Term Var) (ht : t.IsPure) (v : Var → Value) :
    t.eval (fun j => Value.ofBool (Value.upper (v j))) =
      Value.ofBool (Value.upper (t.eval v)) := by
  induction t with
  | var => rfl
  | inf s t hs ht' =>
    simp only [IsPure] at ht
    simp only [eval, hs ht.1, ht' ht.2, Value.upper_inf, Value.ofBool_inf]
  | sup s t hs ht' =>
    simp only [IsPure] at ht
    simp only [eval, hs ht.1, ht' ht.2, Value.upper_sup, Value.ofBool_sup]
  | union => exact False.elim ht

private theorem pure_eval_resolves (t : Term Var) (ht : t.IsPure)
    (v w : Var → Value) (h : ∀ j, Value.Resolves (v j) (w j)) :
    Value.Resolves (t.eval v) (t.eval w) := by
  induction t with
  | var j => exact h j
  | inf s t hs ht' => exact Value.resolves_inf _ _ _ _ (hs ht.1) (ht' ht.2)
  | sup s t hs ht' => exact Value.resolves_sup _ _ _ _ (hs ht.1) (ht' ht.2)
  | union => exact False.elim ht

private theorem pure_eval_ne_neutral (t : Term Var) (ht : t.IsPure)
    (v : Var → Value) (h : ∀ j, v j ≠ .neutral) : t.eval v ≠ .neutral := by
  induction t with
  | var j => exact h j
  | inf s t hs ht' => exact Value.inf_ne_neutral _ _ (hs ht.1) (ht' ht.2)
  | sup s t hs ht' => exact Value.sup_ne_neutral _ _ (hs ht.1) (ht' ht.2)
  | union => exact False.elim ht

private theorem projection_thresholds (t : Term (Option Var)) (ht : t.IsPure)
    (hp : t.IsBooleanProjection) (v : Option Var → Value) :
    Value.lower (t.eval v) = Value.lower (v none) ∧
      Value.upper (t.eval v) = Value.upper (v none) := by
  have hl := (pure_eval_lower t ht v).symm.trans (hp (fun j => Value.lower (v j)))
  have hu := (pure_eval_upper t ht v).symm.trans (hp (fun j => Value.upper (v j)))
  constructor
  · cases h : Value.lower (t.eval v) <;> cases h' : Value.lower (v none) <;>
      simp_all [Value.ofBool]
  · cases h : Value.upper (t.eval v) <;> cases h' : Value.upper (v none) <;>
      simp_all [Value.ofBool]

/-- A pure Boolean-projection term fixes each nonneutral distinguished value. -/
theorem eval_projection_non_neutral (t : Term (Option Var)) (ht : t.IsPure)
    (hp : t.IsBooleanProjection) (v : Option Var → Value) (hv : v none ≠ .neutral) :
    t.eval v = v none := by
  obtain ⟨hl, hu⟩ := projection_thresholds t ht hp v
  cases hx : v none with
  | b => cases he : t.eval v <;> simp_all [Value.lower, Value.upper]
  | c => cases he : t.eval v <;> simp_all [Value.lower, Value.upper]
  | neutral => exact False.elim (hv hx)
  | possible =>
    let w := fun j => Value.resolveNeutral (v j)
    have hw : w none = .possible := by simp [w, hx, Value.resolveNeutral]
    obtain ⟨hlw, huw⟩ := projection_thresholds t ht hp w
    have hn := pure_eval_ne_neutral t ht w (fun j => Value.resolveNeutral_ne (v j))
    have he : t.eval w = .possible := by
      cases he : t.eval w <;> simp_all [Value.lower, Value.upper]
    have hm := pure_eval_resolves t ht w v (fun j => Value.resolveNeutral_resolves (v j))
    rw [he] at hm
    cases he' : t.eval v <;> simp_all [Value.Resolves, Value.union]

/-- At the neutral input a projection term has only the two middle values. -/
theorem eval_projection_neutral (t : Term (Option Var)) (ht : t.IsPure)
    (hp : t.IsBooleanProjection) (v : Option Var → Value) (hv : v none = .neutral) :
    t.eval v = .possible ∨ t.eval v = .neutral := by
  obtain ⟨hl, hu⟩ := projection_thresholds t ht hp v
  cases he : t.eval v <;> simp_all [Value.lower, Value.upper]


/-- Endpoint constants or a constant-free full term. -/
private inductive Reduced (Var : Type*) where
  | b | c | term (t : Term Var)

private def Reduced.eval (v : Var → Value) : Reduced Var → Value
  | .b => .b | .c => .c | .term t => t.eval v

private def Reduced.inf : Reduced Var → Reduced Var → Reduced Var
  | .b, _ | _, .b => .b
  | .c, x | x, .c => x
  | .term s, .term t => .term (.inf s t)

private def Reduced.sup : Reduced Var → Reduced Var → Reduced Var
  | .c, _ | _, .c => .c
  | .b, x | x, .b => x
  | .term s, .term t => .term (.sup s t)

private theorem Reduced.eval_inf (s t : Reduced Var) (v : Var → Value) :
    (s.inf t).eval v = Value.inf (s.eval v) (t.eval v) := by
  cases s <;> cases t <;> simp [Reduced.inf, Reduced.eval, Term.eval, (Value.endpoint_inf _).1,
    (Value.endpoint_inf _).2.1, (Value.endpoint_inf _).2.2.1, (Value.endpoint_inf _).2.2.2]

private theorem Reduced.eval_sup (s t : Reduced Var) (v : Var → Value) :
    (s.sup t).eval v = Value.sup (s.eval v) (t.eval v) := by
  cases s <;> cases t <;> simp [Reduced.sup, Reduced.eval, Term.eval, (Value.endpoint_sup _).1,
    (Value.endpoint_sup _).2.1, (Value.endpoint_sup _).2.2.1, (Value.endpoint_sup _).2.2.2]

/-- A nonempty union of endpoint polynomials after endpoint simplification. -/
private inductive Expansion (Var : Type*) where
  | leaf (r : Reduced Var)
  | union (s t : Expansion Var)

private def Expansion.eval (v : Var → Value) : Expansion Var → Value
  | .leaf r => r.eval v
  | .union s t => Value.union (s.eval v) (t.eval v)

private def Expansion.inf : Expansion Var → Expansion Var → Expansion Var
  | .union s t, u => .union (s.inf u) (t.inf u)
  | .leaf r, .union s t => .union ((Expansion.leaf r).inf s) ((Expansion.leaf r).inf t)
  | .leaf r, .leaf q => .leaf (r.inf q)

private def Expansion.sup : Expansion Var → Expansion Var → Expansion Var
  | .union s t, u => .union (s.sup u) (t.sup u)
  | .leaf r, .union s t => .union ((Expansion.leaf r).sup s) ((Expansion.leaf r).sup t)
  | .leaf r, .leaf q => .leaf (r.sup q)

private theorem Expansion.eval_inf (s t : Expansion Var) (v : Var → Value) :
    (s.inf t).eval v = Value.inf (s.eval v) (t.eval v) := by
  induction s with
  | union s t hs ht =>
    simp only [Expansion.inf, Expansion.eval, hs, ht, Value.inf_union_left]
  | leaf r =>
    induction t with
    | leaf q => simpa only [Expansion.inf, Expansion.eval] using Reduced.eval_inf r q v
    | union s t hs ht =>
      simp only [Expansion.inf, Expansion.eval, hs, ht, Value.inf_union_right]

private theorem Expansion.eval_sup (s t : Expansion Var) (v : Var → Value) :
    (s.sup t).eval v = Value.sup (s.eval v) (t.eval v) := by
  induction s with
  | union s t hs ht =>
    simp only [Expansion.sup, Expansion.eval, hs, ht, Value.sup_union_left]
  | leaf r =>
    induction t with
    | leaf q => simpa only [Expansion.sup, Expansion.eval] using Reduced.eval_sup r q v
    | union s t hs ht =>
      simp only [Expansion.sup, Expansion.eval, hs, ht, Value.sup_union_right]

private def expandNeutral : Term (Option Var) → Expansion Var
  | .var none => .union (.leaf .b) (.leaf .c)
  | .var (some j) => .leaf (.term (.var j))
  | .inf s t => s.expandNeutral.inf t.expandNeutral
  | .sup s t => s.expandNeutral.sup t.expandNeutral
  | .union s t => .union s.expandNeutral t.expandNeutral

private theorem eval_expandNeutral (t : Term (Option Var)) (v : Var → Value) :
    t.expandNeutral.eval v = t.eval (fun j => j.elim .neutral v) := by
  induction t with
  | var j => cases j <;> rfl
  | inf s t hs ht => simp only [expandNeutral, Expansion.eval_inf, eval, hs, ht]
  | sup s t hs ht => simp only [expandNeutral, Expansion.eval_sup, eval, hs, ht]
  | union s t hs ht => simp only [expandNeutral, Expansion.eval, eval, hs, ht]

private def mergeRecovered : Option (Term Var) → Option (Term Var) → Option (Term Var)
  | none, t | t, none => t
  | some s, some t => some (.union s t)

private def Expansion.recover : Expansion Var → Option (Term Var)
  | .leaf .b | .leaf .c => none
  | .leaf (.term t) => some t
  | .union s t => mergeRecovered s.recover t.recover

private theorem possible_merge (s t : Option (Term Var)) (v : Var → Value) :
    hasPossible (mergeRecovered s t) v ↔ hasPossible s v ∨ hasPossible t v := by
  cases s <;> cases t <;>
    simp [mergeRecovered, hasPossible, eval, Value.union_possible_iff]

private theorem Expansion.possible_recover (t : Expansion Var) (v : Var → Value) :
    hasPossible t.recover v ↔ t.eval v = .possible := by
  induction t with
  | leaf r => cases r <;> simp [Expansion.recover, Expansion.eval, Reduced.eval, hasPossible]
  | union s t hs ht =>
    simp only [Expansion.recover, possible_merge, hs, ht, Expansion.eval,
      Value.union_possible_iff]

/-- Eliminating a neutral constant produces a full term trace, or zero. -/
theorem neutral_section_trace (t : Term (Option Var)) :
    ∃ g : Option (Term Var), ∀ v : Var → Value,
      (t.eval (fun j => j.elim .neutral v) = .possible ↔ hasPossible g v) := by
  refine ⟨t.expandNeutral.recover, ?_⟩
  intro v
  rw [← eval_expandNeutral]
  exact (Expansion.possible_recover _ _).symm


theorem optionalLift_isPure (g : Option (Term Var)) : (optionalLift g).IsPure := by
  cases g with
  | none => trivial
  | some t => exact t.fiberLift_isPure

private theorem eval_optionalLift_neutral (g : Option (Term Var))
    (v : Option Var → Value) (hv : v none = .neutral) :
    (optionalLift g).eval v = if hasPossible g (fun j => v (some j)) then .possible else .neutral := by
  cases g with
  | none => simp [optionalLift, eval, hasPossible, hv]
  | some t => simp [optionalLift, eval_fiberLift, Value.envelope_cases, hv, hasPossible]

private theorem eval_optionalLift_non_neutral (g : Option (Term Var))
    (v : Option Var → Value) (hv : v none ≠ .neutral) :
    (optionalLift g).eval v = v none := by
  cases g with
  | none => rfl
  | some t =>
    rw [optionalLift, eval_fiberLift, Value.envelope_cases]
    cases hx : v none <;> simp_all

/-- Exact converse: the pure projection fiber consists of full-term lifts and zero. -/
theorem projection_fiber_recovery (t : Term (Option Var)) (ht : t.IsPure)
    (hp : t.IsBooleanProjection) :
    ∃ g : Option (Term Var), ∀ v, t.eval v = (optionalLift g).eval v := by
  obtain ⟨g, hg⟩ := t.neutral_section_trace
  refine ⟨g, fun v => ?_⟩
  by_cases hv : v none = .neutral
  · have hsection : t.eval (fun j => j.elim .neutral (fun i => v (some i))) = t.eval v := by
      congr 1
      funext j
      cases j <;> simp_all
    have htrace := hg (fun j => v (some j))
    rw [hsection] at htrace
    rw [eval_optionalLift_neutral g v hv]
    obtain h | h := eval_projection_neutral t ht hp v hv
    · rw [h]
      simp [← htrace, h]
    · rw [h]
      simp [← htrace, h]
  · rw [eval_projection_non_neutral t ht hp v hv,
      eval_optionalLift_non_neutral g v hv]

/-- Every recovered lift has the required Boolean restriction. -/
theorem optionalLift_isBooleanProjection (g : Option (Term Var)) :
    (optionalLift g).IsBooleanProjection := by
  intro v
  apply eval_optionalLift_non_neutral
  cases v none <;> simp [Value.ofBool]

/-- Characterization as functions, allowing an arbitrary pure representative. -/
theorem isBooleanProjection_iff_recovery (t : Term (Option Var)) (ht : t.IsPure) :
    t.IsBooleanProjection ↔ ∃ g : Option (Term Var), ∀ v, t.eval v = (optionalLift g).eval v := by
  constructor
  · exact projection_fiber_recovery t ht
  · rintro ⟨g, hg⟩ v
    rw [hg]
    exact optionalLift_isBooleanProjection g v

@[simp] theorem eval_all_possible (t : Term Var) : t.eval (fun _ => .possible) = .possible := by
  induction t <;> simp_all [eval, Value.inf, Value.sup, Value.union]

/-- Equality in the fiber recovers equality of full functions, including the zero case. -/
theorem optionalLift_eq_iff (g h : Option (Term Var)) :
    (∀ v, (optionalLift g).eval v = (optionalLift h).eval v) ↔
      g.map (fun t => t.eval) = h.map (fun t => t.eval) := by
  cases g with
  | none =>
    cases h with
    | none => simp
    | some t =>
      constructor
      · intro he
        have hx := he (fun j => j.elim .neutral (fun _ => .possible))
        simp [optionalLift, eval, eval_fiberLift, Value.envelope_cases] at hx
      · simp
  | some s =>
    cases h with
    | none =>
      constructor
      · intro he
        have hx := he (fun j => j.elim .neutral (fun _ => .possible))
        simp [optionalLift, eval, eval_fiberLift, Value.envelope_cases] at hx
      · simp
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro he
        funext v
        apply eval_eq_of_possible_iff s t
        intro w
        have hx := he (fun j => j.elim .neutral w)
        simpa [optionalLift, eval_fiberLift, Value.envelope_cases] using
          congrArg (fun z => z = Value.possible) hx
      · intro he v
        simp only [optionalLift, eval_fiberLift, congrFun he]


/-- A nonzero full-trace obstruction yields a nonterm pure bichain envelope. -/
theorem no_pure_envelope_of_trace_obstruction (f : (Var → Value) → Value)
    (hnonzero : ∃ v, f v = .possible)
    (hobstruction : ∀ g : Term Var, ¬ ∀ v, g.eval v = .possible ↔ f v = .possible) :
    ¬ ∃ t : Term (Option Var), t.IsPure ∧
      ∀ v, t.eval v = Value.envelope (v none) (f (fun j => v (some j))) := by
  rintro ⟨t, ht, he⟩
  have hp : t.IsBooleanProjection := by
    intro v
    rw [he, Value.envelope_cases]
    cases v none <;> rfl
  obtain ⟨g, hg⟩ := projection_fiber_recovery t ht hp
  have htrace (v : Var → Value) : hasPossible g v ↔ f v = .possible := by
    let w : Option Var → Value := fun j => j.elim .neutral v
    have hw : w none = .neutral := rfl
    have hx := (hg w).symm.trans (he w)
    rw [eval_optionalLift_neutral g w hw, Value.envelope_cases, hw] at hx
    change (if hasPossible g v then Value.possible else Value.neutral) =
      (if f v = .possible then .possible else .neutral) at hx
    split_ifs at hx <;> simp_all
  cases g with
  | none =>
    obtain ⟨v, hv⟩ := hnonzero
    exact (htrace v).mpr hv
  | some g => exact hobstruction g htrace

end Term
end KFOL.Bichain
