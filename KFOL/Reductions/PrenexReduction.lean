module

public import KFOL.Reductions.QuantifiedLists

/-! # From prenex formulas to normal forms

An instance of the prenex truth problem lists rounds of quantifiers over
named variables and a matrix. Numbering the quantifiers in order, with every
variable read at its last quantifier, gives a formula with stages. The
reduction writes the normal form of its operation. An instance that is not
closed is sent to the normal form of a false formula.
-/

@[expose] public section

namespace KFOL.Recognition.Lists

open Cslib.Logic.PL Bichain.Quantified Problems

/-- The quantified variables in order. -/
def roundVars (ps : List (ℕ × ℕ)) : List ℕ := ps.flatMap fun p => [p.1, p.2]

/-- The position of the last quantifier over a variable. -/
def lastIdx (xs : List ℕ) (x : ℕ) : ℕ := xs.length - 1 - xs.reverse.idxOf x

/-- Every variable of the matrix is quantified. -/
def closedB (xs : List ℕ) (ψ : CNF ℕ) : Bool :=
  ψ.all fun c => c.all fun l => xs.any fun x => x == l.1

/-- The clauses over stages, with signs as numbers. -/
def clsOf (xs : List ℕ) (ψ : CNF ℕ) : List (List (ℕ × ℕ)) :=
  ψ.map fun c => c.map fun l => (lastIdx xs l.1 + 1, l.2.toNat)

/-- The reduction, with every number counted in the internal coding. -/
def reduce0 (K c0 c1 c2 : ℕ) (x : List (ℕ × ℕ) × CNF ℕ) : GuardList :=
  if closedB (roundVars x.1) x.2 then
    instanceOf K c0 c1 c2 (roundVars x.1).length (clsOf (roundVars x.1) x.2)
  else instanceOf K c0 c1 c2 0 [[]]

/-- The formula with stages of an instance. -/
def formulaOf (x : List (ℕ × ℕ) × CNF ℕ) : Formula :=
  if closedB (roundVars x.1) x.2 then
    ⟨(roundVars x.1).length, fun i => decide (i % 2 = 1),
      x.2.map fun c => c.map fun l => (lastIdx (roundVars x.1) l.1 + 1, l.2)⟩
  else ⟨0, fun i => decide (i % 2 = 1), [[]]⟩

theorem length_roundVars (ps : List (ℕ × ℕ)) : (roundVars ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [roundVars, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem roundVars_append (ps : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    roundVars (ps ++ [p]) = roundVars ps ++ [p.1, p.2] := by
  simp [roundVars]

theorem closedB_iff (xs : List ℕ) (ψ : CNF ℕ) :
    closedB xs ψ = true ↔ ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs := by
  simp only [closedB, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  exact forall₂_congr fun c _ => forall₂_congr fun l _ =>
    ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun h => ⟨_, h, rfl⟩⟩

/-! ### The position of the last quantifier -/

theorem lastIdx_lt {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : lastIdx xs x < xs.length := by
  have := List.length_pos_of_mem hx
  unfold lastIdx
  omega

theorem lastIdx_append_right (xs : List ℕ) (a b : ℕ) :
    lastIdx (xs ++ [a, b]) b = xs.length + 1 := by
  simp [lastIdx, List.idxOf_cons_self]

theorem lastIdx_append_left (xs : List ℕ) {a b : ℕ} (h : a ≠ b) :
    lastIdx (xs ++ [a, b]) a = xs.length := by
  simp [lastIdx, List.idxOf_cons_ne _ (Ne.symm h), List.idxOf_cons_self]

theorem lastIdx_append_of_ne (xs : List ℕ) {a b v : ℕ} (ha : v ≠ a) (hb : v ≠ b)
    (hv : v ∈ xs) : lastIdx (xs ++ [a, b]) v = lastIdx xs v := by
  have hlt := List.idxOf_lt_length_of_mem (List.mem_reverse.2 hv)
  rw [List.length_reverse] at hlt
  simp only [lastIdx, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.length_append, List.length_cons, List.length_nil,
    List.idxOf_cons_ne _ (Ne.symm hb), List.idxOf_cons_ne _ (Ne.symm ha)]
  omega

/-! ### Assignments of stages and of variables -/

/-- The assignment of the variables read from an assignment of the stages. -/
def asg (xs : List ℕ) (α σ₀ : ℕ → Bool) : ℕ → Bool :=
  fun v => if v ∈ xs then α (lastIdx xs v + 1) else σ₀ v

theorem asg_step (xs : List ℕ) (a b : ℕ) (s s' : Bool) (α σ₀ : ℕ → Bool) :
    Function.update (Function.update (asg xs α σ₀) a s) b s' =
      asg (xs ++ [a, b])
        (Function.update (Function.update α (xs.length + 1) s) (xs.length + 2) s') σ₀ := by
  funext v
  by_cases hb : v = b
  · subst hb
    simp [asg, lastIdx_append_right]
  · by_cases ha : v = a
    · subst ha
      simp [asg, hb, lastIdx_append_left xs hb]
    · rw [Function.update_of_ne hb, Function.update_of_ne ha]
      by_cases hv : v ∈ xs
      · have hlt := lastIdx_lt hv
        simp only [asg, hv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
          ↓reduceIte, lastIdx_append_of_ne xs ha hb hv]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp [asg, hv, ha, hb]

theorem prenexFormula_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) (ψ : CNF ℕ) :
    prenexFormula (p :: ps) ψ = .ex p.1 (.all p.2 (prenexFormula ps ψ)) := rfl

/-- The value of the quantifiers of the remaining rounds, read on stages. -/
theorem eval_prenex_iff (ps : List (ℕ × ℕ)) (ψ : CNF ℕ) (F : Formula)
    (hex : ∀ i, F.ex i = decide (i % 2 = 1)) (σ₀ : ℕ → Bool)
    (hbase : ∀ α : ℕ → Bool, CNF.eval (asg (roundVars ps) α σ₀) ψ = true ↔ Matrix F α) :
    ∀ (rest pre : List (ℕ × ℕ)), pre ++ rest = ps → ∀ α : ℕ → Bool,
      ((prenexFormula rest ψ).eval (asg (roundVars pre) α σ₀) = true ↔
        sat F (2 * rest.length) (2 * pre.length) α) := by
  intro rest
  induction rest with
  | nil =>
    intro pre hpre α
    rw [List.append_nil] at hpre
    subst hpre
    change (QBF.ofCNF ψ).eval _ = true ↔ Matrix F α
    rw [QBF.eval_ofCNF]
    exact hbase α
  | cons p rest ih =>
    intro pre hpre α
    have hlen : (roundVars pre).length = 2 * pre.length := length_roundVars pre
    have e1 : F.ex (2 * pre.length + 1) = true := by
      rw [hex]
      exact decide_eq_true (by omega)
    have e2 : F.ex (2 * pre.length + 1 + 1) = false := by
      rw [hex]
      exact decide_eq_false (by omega)
    rw [prenexFormula_cons, QBF.eval_ex_eq_true_iff,
      show 2 * (p :: rest).length = (2 * rest.length + 1) + 1 by simp; omega]
    simp only [sat, e1, e2, ↓reduceIte, Bool.false_eq_true]
    refine exists_congr fun s => ?_
    rw [QBF.eval_all_eq_true_iff]
    refine forall_congr' fun s' => ?_
    have h := ih (pre ++ [p]) (by simp [hpre])
      (Function.update (Function.update α (2 * pre.length + 1) s) (2 * pre.length + 1 + 1) s')
    rw [roundVars_append, ← hlen, ← asg_step, hlen] at h
    rw [h, show 2 * (pre ++ [p]).length = 2 * pre.length + 1 + 1 by simp; omega]

theorem mem_freeVars_prenex (ps : List (ℕ × ℕ)) (ψ : CNF ℕ) (v : ℕ) :
    v ∈ (prenexFormula ps ψ).freeVars ↔ v ∈ ψ.vars ∧ v ∉ roundVars ps := by
  induction ps with
  | nil => simp [prenexFormula, roundVars, QBF.mem_freeVars_ofCNF]
  | cons p ps ih =>
    rw [prenexFormula_cons, QBF.freeVars_ex, QBF.freeVars_all, Finset.mem_erase,
      Finset.mem_erase, ih]
    simp only [roundVars, List.flatMap_cons, List.cons_append, List.nil_append, List.mem_cons,
      not_or]
    tauto

theorem closed_prenex_iff (ps : List (ℕ × ℕ)) (ψ : CNF ℕ) :
    (prenexFormula ps ψ).Closed ↔ closedB (roundVars ps) ψ = true := by
  rw [closedB_iff, QBF.Closed, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_freeVars_prenex, CNF.mem_vars, not_and, not_not]
  constructor
  · intro h c hc l hl
    exact h _ ⟨c, hc, l.2, hl⟩
  · rintro h v ⟨c, hc, b, hl⟩
    exact h c hc (v, b) hl

/-! ### The reduction is correct -/

theorem formulaOf_wf (x : List (ℕ × ℕ) × CNF ℕ) : (formulaOf x).WF := by
  unfold formulaOf
  split_ifs with hc
  · intro C hC l hl
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hC
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    have hlt := lastIdx_lt ((closedB_iff _ _).1 hc c hc' l' hl')
    change 1 ≤ lastIdx (roundVars x.1) l'.1 + 1 ∧
      lastIdx (roundVars x.1) l'.1 + 1 ≤ (roundVars x.1).length
    omega
  · intro C hC l hl
    obtain rfl : C = [] := by simpa using hC
    cases hl

theorem formulaOf_ex (x : List (ℕ × ℕ) × CNF ℕ) (i : ℕ) :
    (formulaOf x).ex i = decide (i % 2 = 1) := by
  unfold formulaOf
  split_ifs <;> rfl

theorem reduce0_eq (K c0 c1 c2 : ℕ) (x : List (ℕ × ℕ) × CNF ℕ) :
    reduce0 K c0 c1 c2 x =
      instanceOf K c0 c1 c2 (formulaOf x).n (numCls (formulaOf x)) := by
  unfold reduce0 formulaOf
  split_ifs
  · simp [numCls, clsOf, Function.comp_def]
  · rfl

/-- An instance is a true closed formula exactly when its formula with
stages is true. -/
theorem mem_prenexTruth_iff (x : List (ℕ × ℕ) × CNF ℕ) :
    x ∈ prenexTruth ↔ sat (formulaOf x) (formulaOf x).n 0 (fun _ => false) := by
  obtain ⟨ps, ψ⟩ := x
  by_cases hc : closedB (roundVars ps) ψ = true
  · have hclosed := (closed_prenex_iff ps ψ).2 hc
    have hF : formulaOf (ps, ψ) = ⟨(roundVars ps).length, fun i => decide (i % 2 = 1),
        ψ.map fun c => c.map fun l => (lastIdx (roundVars ps) l.1 + 1, l.2)⟩ := by
      simp [formulaOf, hc]
    rw [hF]
    change prenexFormula ps ψ ∈ Cslib.Complexity.TQBF ↔ _
    rw [Cslib.Complexity.mem_TQBF_iff_of_closed hclosed (fun _ => false)]
    have hbase : ∀ α : ℕ → Bool,
        CNF.eval (asg (roundVars ps) α (fun _ => false)) ψ = true ↔
          Matrix ⟨(roundVars ps).length, fun i => decide (i % 2 = 1),
            ψ.map fun c => c.map fun l => (lastIdx (roundVars ps) l.1 + 1, l.2)⟩ α := by
      intro α
      rw [CNF.eval_eq_true_iff]
      constructor
      · intro h C hC
        obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hC
        obtain ⟨l, hl, hval⟩ := (Clause.eval_eq_true_iff _ _).1 (h c hc')
        refine ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
        have hv : asg (roundVars ps) α (fun _ => false) l.1 = l.2 := by simpa using hval
        simpa [asg, (closedB_iff _ _).1 hc c hc' l hl] using hv
      · intro h c hc'
        obtain ⟨l', hl', hval⟩ := h _ (List.mem_map.2 ⟨c, hc', rfl⟩)
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
        refine (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, ?_⟩
        have hv : asg (roundVars ps) α (fun _ => false) l.1 = l.2 := by
          simpa [asg, (closedB_iff _ _).1 hc c hc' l hl] using hval
        simpa using hv
    have h := eval_prenex_iff ps ψ _ (fun _ => rfl) (fun _ => false) hbase ps [] rfl
      (fun _ => false)
    have e : asg (roundVars []) (fun _ => false) (fun _ => false) = fun _ => false := by
      funext v
      simp [asg, roundVars]
    rw [e] at h
    rw [h, length_roundVars]
    rfl
  · have hF : formulaOf (ps, ψ) = ⟨0, fun i => decide (i % 2 = 1), [[]]⟩ := by
      simp [formulaOf, hc]
    rw [hF]
    constructor
    · intro h
      exact absurd ((closed_prenex_iff ps ψ).1 h.1) hc
    · intro h
      obtain ⟨l, hl, -⟩ := h [] List.mem_cons_self
      cases hl

/-- **The reduction is correct.** -/
theorem reduce0_mem_iff {K : ℕ} (three : Fin 3 ↪ Fin K) (x : List (ℕ × ℕ) × CNF ℕ) :
    reduce0 K (three 0).val (three 1).val (three 2).val x ∈ coreNormalForms three ↔
      x ∈ prenexTruth := by
  rw [reduce0_eq, mem_prenexTruth_iff]
  exact instanceOf_mem_iff three (formulaOf x) (formulaOf_wf x) fun i hi => by
    rw [formulaOf_ex, exB_iff _ _ hi]

end KFOL.Recognition.Lists
