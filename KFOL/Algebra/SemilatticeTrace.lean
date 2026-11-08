module

public import KFOL.Algebra.Idempotent
public import KFOL.Algebra.TestDomains
public import Mathlib.Data.Finset.Union

/-!
# Semilattice traces of core operations

Variable support is the concrete representation of a semilattice term
operation. Substitution composes supports by union, and single variables are
projections. All statements concern the existing syntax and evaluator.
-/

@[expose] public section

namespace KFOL.Term

universe u v w

variable {Role : Type u} {Var : Type v} {Var' : Type w}

/-- A core term contains no winner leaf. -/
theorem IsCore.not_hasWinner {t : Term Role Var} (ht : t.IsCore) : ¬t.HasWinner := by
  induction t with
  | winner => exact False.elim ht
  | var => exact id
  | choice r s t hs ht' => exact fun h => h.elim (hs ht.1) (ht' ht.2)
  | rename => exact False.elim ht

/-- There is at least one argument in every core expression. -/
theorem IsCore.vars_nonempty [DecidableEq Var] {t : Term Role Var} (ht : t.IsCore) :
    t.vars.Nonempty := by
  induction t with
  | winner => exact False.elim ht
  | var x => exact ⟨x, Finset.mem_singleton_self x⟩
  | choice r s t hs _ =>
    obtain ⟨x, hx⟩ := hs ht.1
    exact ⟨x, Finset.mem_union_left _ hx⟩
  | rename => exact False.elim ht

/-- The exact union trace on the all-ambiguous cell. -/
theorem IsCore.eval_mem_iff [DecidableEq Var] {t : Term Role Var} (ht : t.IsCore)
    (v : Var → WinnerSet Role) (hv : ∀ x, WinnerSet.Ambiguous (v x)) (r : Role) :
    r ∈ (t.eval v).val ↔ ∃ x ∈ t.vars, r ∈ (v x).val := by
  induction t with
  | winner => exact False.elim ht
  | var x => simp [eval, vars]
  | choice k s t hs ht' =>
    have hS := s.eval_ambiguous_of_no_winner ht.1.not_hasWinner v hv
    have hT := t.eval_ambiguous_of_no_winner ht.2.not_hasWinner v hv
    rw [eval, WinnerSet.choice_of_ambiguous k hS hT]
    simp only [WinnerSet.val_union, Set.mem_union, hs ht.1, ht' ht.2,
      vars, Finset.mem_union]
    constructor
    · rintro (⟨x, hx, hr⟩ | ⟨x, hx, hr⟩)
      · exact ⟨x, Or.inl hx, hr⟩
      · exact ⟨x, Or.inr hx, hr⟩
    · rintro ⟨x, hx | hx, hr⟩
      · exact Or.inl ⟨x, hx, hr⟩
      · exact Or.inr ⟨x, hx, hr⟩
  | rename => exact False.elim ht

@[simp] theorem vars_pushRenames [DecidableEq Var] (t : Term Role Var)
    (p : Equiv.Perm Role) : (t.pushRenames p).vars = t.vars := by
  induction t generalizing p with
  | winner => rfl
  | var => rfl
  | choice r s t hs ht => simp only [pushRenames, vars, hs, ht]
  | rename q t ih => exact ih (p * q)

/-- Idempotent operations are closed under substitution, at every arity. -/
theorem idempotent_subst (t : Term Role Var) (replacement : Var → Term Role Var')
    (ht : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A)
    (hr : ∀ x (A : WinnerSet Role), (replacement x).eval (fun _ => A) = A) :
    ∀ A : WinnerSet Role, (t.subst replacement).eval (fun _ => A) = A := by
  intro A
  rw [eval_subst]
  have hv : (fun x => (replacement x).eval (fun _ => A)) = fun _ => A :=
    funext (fun x => hr x A)
  rw [hv]
  exact ht A

/-- Full-language idempotent operations have the same trace on their original
syntactic supports, even before extraction. -/
theorem eval_mem_iff_of_idempotent [DecidableEq Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A)
    (v : Var → WinnerSet Role) (hv : ∀ x, WinnerSet.Ambiguous (v x)) (r : Role) :
    r ∈ (t.eval v).val ↔ ∃ x ∈ t.vars, r ∈ (v x).val := by
  obtain ⟨hc, he, _⟩ := t.idempotent_extraction three hd
  rw [← he v]
  simpa only [vars_pushRenames] using hc.eval_mem_iff v hv r

/-- Substitution is union of supports: the composition law for semilattice
term operations. This law also holds outside the core. -/
theorem vars_subst [DecidableEq Var] [DecidableEq Var']
    (t : Term Role Var) (replacement : Var → Term Role Var') :
    (t.subst replacement).vars = t.vars.biUnion (fun x => (replacement x).vars) := by
  induction t with
  | winner => simp [subst, vars]
  | var => simp [subst, vars]
  | choice r s t hs ht => simp only [subst, vars, hs, ht, Finset.union_biUnion]
  | rename p t ih => exact ih

/-- The core is closed under substitution of core expressions. -/
theorem IsCore.subst [DecidableEq Var] {t : Term Role Var} (ht : t.IsCore)
    (replacement : Var → Term Role Var')
    (hr : ∀ x ∈ t.vars, (replacement x).IsCore) : (t.subst replacement).IsCore := by
  induction t with
  | winner => exact False.elim ht
  | var x => exact hr x (Finset.mem_singleton_self x)
  | choice r s t hs ht' =>
    exact ⟨hs ht.1 (fun x hx => hr x (Finset.mem_union_left _ hx)),
      ht' ht.2 (fun x hx => hr x (Finset.mem_union_right _ hx))⟩
  | rename => exact False.elim ht

/-- Every nonempty finite support is realized, using derived union. -/
theorem exists_core_vars [DecidableEq Var] (three : Fin 3 ↪ Role)
    (S : Finset Var) (hS : S.Nonempty) :
    ∃ t : Term Role Var, t.IsCore ∧ t.vars = S := by
  induction S using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hS)
  | @insert a S ha ih =>
    by_cases h : S.Nonempty
    · obtain ⟨t, ht, hvars⟩ := ih h
      refine ⟨unionTerm three (.var a) t, ?_, ?_⟩
      · simp [unionTerm, IsCore, ht]
      · simp [unionTerm, vars, hvars]
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst S
      exact ⟨.var a, trivial, rfl⟩

/-- A two-value ambiguous valuation tests the presence of any specified input
in the support. The omitted role distinguishes a proper pair from the top. -/
theorem IsCore.mem_eval_support_test [DecidableEq Var] {t : Term Role Var}
    (ht : t.IsCore) (three : Fin 3 ↪ Role) (x : Var) :
    three 2 ∈ (t.eval (fun y => if y = x then
      (⟨Set.univ, three 0, trivial⟩ : WinnerSet Role)
      else WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1)))).val
      ↔ x ∈ t.vars := by
  classical
  let P := WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))
  let T : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  have hP : WinnerSet.Ambiguous P := WinnerSet.ambiguous_of_two_mem P
    (three 0) (three 1) (three.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
  have hT : WinnerSet.Ambiguous T := WinnerSet.ambiguous_of_two_mem T
    (three 0) (three 1) (three.injective.ne (by decide)) trivial trivial
  have hp : three 2 ∉ P.val := by
    rintro (h | h)
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 0) h
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 1) h
  have hv : ∀ y, WinnerSet.Ambiguous (if y = x then T else P) := by
    intro y; split_ifs <;> assumption
  change three 2 ∈ (t.eval (fun y => if y = x then T else P)).val ↔ _
  rw [ht.eval_mem_iff _ hv]
  constructor
  · rintro ⟨y, hy, hm⟩
    by_cases he : y = x
    · exact he ▸ hy
    · simp only [ite_eq_right he] at hm
      exact False.elim (hp hm)
  · intro hx
    exact ⟨x, hx, by simp [T]⟩

/-- Distinct supports are separated by ambiguous inputs. Thus support
represents exactly the restricted operation, not merely its syntax. -/
theorem IsCore.equal_on_ambiguous_iff_vars_eq [DecidableEq Var]
    {s t : Term Role Var} (hs : s.IsCore) (ht : t.IsCore) (three : Fin 3 ↪ Role) :
    (∀ v : Var → WinnerSet Role, (∀ x, WinnerSet.Ambiguous (v x)) → s.eval v = t.eval v) ↔
      s.vars = t.vars := by
  constructor
  · intro he
    apply Finset.ext
    intro x
    rw [← hs.mem_eval_support_test three x, ← ht.mem_eval_support_test three x]
    have hv : ∀ y, WinnerSet.Ambiguous
        (if y = x then (⟨Set.univ, three 0, trivial⟩ : WinnerSet Role)
         else WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))) := by
      intro y
      split_ifs
      · exact WinnerSet.ambiguous_of_two_mem _ (three 0) (three 1)
          (three.injective.ne (by decide)) trivial trivial
      · exact WinnerSet.ambiguous_of_two_mem _ (three 0) (three 1)
          (three.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
    rw [he _ hv]
  · intro he v hv
    apply Subtype.ext
    ext r
    rw [hs.eval_mem_iff v hv r, ht.eval_mem_iff v hv r, he]

/-- Every valid core identity is regular: both sides have the same variables. -/
theorem vars_eq_of_core_identity [DecidableEq Var] (three : Fin 3 ↪ Role)
    {s t : Term Role Var} (hs : s.IsCore) (ht : t.IsCore)
    (he : ∀ v : Var → WinnerSet Role, s.eval v = t.eval v) : s.vars = t.vars :=
  (hs.equal_on_ambiguous_iff_vars_eq ht three).mp (fun v _ => he v)

/-- Idempotent full terms have nonempty support. -/
theorem vars_nonempty_of_idempotent [DecidableEq Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    t.vars.Nonempty := by
  obtain ⟨hc, _, _⟩ := t.idempotent_extraction three hd
  simpa only [vars_pushRenames] using hc.vars_nonempty

/-- The semilattice representation depends exactly on the restricted operation,
including for full-language idempotent expressions before extraction. -/
theorem equal_on_ambiguous_iff_vars_eq_of_idempotent [DecidableEq Var]
    (three : Fin 3 ↪ Role) (s t : Term Role Var)
    (hs : ∀ A : WinnerSet Role, s.eval (fun _ => A) = A)
    (ht : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    (∀ v : Var → WinnerSet Role, (∀ x, WinnerSet.Ambiguous (v x)) → s.eval v = t.eval v) ↔
      s.vars = t.vars := by
  obtain ⟨hcS, heS, _⟩ := s.idempotent_extraction three hs
  obtain ⟨hcT, heT, _⟩ := t.idempotent_extraction three ht
  simpa only [heS, heT, vars_pushRenames] using
    hcS.equal_on_ambiguous_iff_vars_eq hcT three

/-- Every argument occurring in a core term is essential, witnessed with a
proper ambiguous pair and the top value differing only at that argument. -/
theorem IsCore.essential [DecidableEq Var] {t : Term Role Var} (ht : t.IsCore)
    (three : Fin 3 ↪ Role) (x : Var) (hx : x ∈ t.vars) :
    ∃ v w : Var → WinnerSet Role,
      (∀ y, y ≠ x → v y = w y) ∧ t.eval v ≠ t.eval w := by
  let P := WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))
  let T : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  refine ⟨fun _ => P, fun y => if y = x then T else P, ?_, ?_⟩
  · intro y hy
    exact (ite_eq_right hy).symm
  · intro he
    have hm := (ht.mem_eval_support_test three x).mpr hx
    change three 2 ∈ (t.eval (fun y => if y = x then T else P)).val at hm
    rw [← he, ht.eval_diagonal P] at hm
    rcases hm with h | h
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 0) h
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 1) h

/-- No full-language term is near-unanimity, in any conventional NU arity. -/
theorem not_nearUnanimity (three : Fin 3 ↪ Role) (n : ℕ) (hn : 0 < n)
    (t : Term Role (Fin n)) :
    ¬(∀ A B : WinnerSet Role, ∀ i : Fin n,
      t.eval (Function.update (fun _ => A) i B) = A) := by
  intro hnu
  have hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
    intro A
    simpa only [Function.update_eq_self] using hnu A A ⟨0, by omega⟩
  obtain ⟨hc, he, _⟩ := t.idempotent_extraction three hd
  obtain ⟨i, hi⟩ := hc.vars_nonempty
  let P := WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))
  let T : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  have hw : Function.update (fun _ : Fin n => P) i T =
      fun j => if j = i then T else P := by
    funext j
    simp only [Function.update_apply]
  have hm := (hc.mem_eval_support_test three i).mpr hi
  rw [vars_pushRenames] at hi
  change three 2 ∈ ((t.pushRenames 1).eval (fun j => if j = i then T else P)).val at hm
  rw [he, ← hw, hnu P T i] at hm
  rcases hm with h | h
  · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 0) h
  · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 1) h

/-- No full-language term satisfies the two Mal'cev identities. -/
theorem not_malcev (three : Fin 3 ↪ Role) (t : Term Role (Fin 3)) :
    ¬((∀ A B : WinnerSet Role, t.eval (fun i => if i = 0 then A else B) = A) ∧
      (∀ A B : WinnerSet Role, t.eval (fun i => if i = 2 then B else A) = B)) := by
  rintro ⟨h0, h2⟩
  have hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
    intro A
    simpa only [ite_self] using h0 A A
  obtain ⟨hc, he, _⟩ := t.idempotent_extraction three hd
  obtain ⟨i, hi⟩ := hc.vars_nonempty
  let P := WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))
  let T : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  have hP : WinnerSet.Ambiguous P := WinnerSet.ambiguous_of_two_mem _
    (three 0) (three 1) (three.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
  have hT : WinnerSet.Ambiguous T := WinnerSet.ambiguous_of_two_mem _
    (three 0) (three 1) (three.injective.ne (by decide)) trivial trivial
  have hp : three 2 ∉ P.val := by
    rintro (h | h)
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 0) h
    · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 1) h
  by_cases hi0 : i = 0
  · let v : Fin 3 → WinnerSet Role := fun j => if j = 2 then P else T
    have hv : ∀ j, WinnerSet.Ambiguous (v j) := by
      intro j; dsimp [v]; split_ifs <;> assumption
    have hm : three 2 ∈ ((t.pushRenames 1).eval v).val :=
      (hc.eval_mem_iff v hv _).mpr ⟨i, hi, by simp [v, hi0, T]⟩
    rw [he, show t.eval v = P from h2 T P] at hm
    exact hp hm
  · let v : Fin 3 → WinnerSet Role := fun j => if j = 0 then P else T
    have hv : ∀ j, WinnerSet.Ambiguous (v j) := by
      intro j; dsimp [v]; split_ifs <;> assumption
    have hm : three 2 ∈ ((t.pushRenames 1).eval v).val :=
      (hc.eval_mem_iff v hv _).mpr ⟨i, hi, by simp [v, hi0, T]⟩
    rw [he, show t.eval v = P from h0 P T] at hm
    exact hp hm

end KFOL.Term
