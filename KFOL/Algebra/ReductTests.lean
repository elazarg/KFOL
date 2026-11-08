module

public import KFOL.Algebra.Views
public import KFOL.Algebra.TestDomainCard

/-! # Complete input domains for the public reduct -/

@[expose] public section

namespace KFOL

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

theorem IsPublic.unionTerm {s t : Term Role Var} (hs : s.IsPublic) (ht : t.IsPublic)
    (three : Fin 3 ↪ Role) : (unionTerm three s t).IsPublic :=
  ⟨⟨hs, ht⟩, ⟨hs, ht⟩⟩

theorem IsPublic.suppress {s t : Term Role Var} (hs : s.IsPublic) (ht : t.IsPublic)
    (roles : List Role) : (suppress roles s t).IsPublic := by
  induction roles with
  | nil => exact hs
  | cons r rest ih => exact ⟨ih, ht⟩

/-- Add k on ambiguous inputs and fix every singleton, using genuine public
syntax. This is also the obstruction to certifying idempotency on atoms only. -/
theorem exists_public_ambiguity_adder [Fintype Role] (three : Fin 3 ↪ Role) (k : Role) :
    ∃ t : Term Role (Fin 1), t.IsPublic ∧
      (∀ r, t.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) ∧
      (∀ A : WinnerSet Role, WinnerSet.Ambiguous A →
        t.eval (fun _ => A) = WinnerSet.union A (WinnerSet.singleton k)) := by
  classical
  let base : Term Role (Fin 1) := .var 0
  let acc := unionTerm three base (.winner k)
  let roles : List Role := Finset.univ.toList
  have hb : base.IsPublic := trivial
  have ha : acc.IsPublic := by simp [acc, base, unionTerm, IsPublic]
  refine ⟨suppress roles acc base, ha.suppress hb roles, ?_, ?_⟩
  · intro r
    exact eval_suppress_atom roles acc base _ r (by simp [roles]) rfl
  · intro A hA
    simpa only [acc, eval_unionTerm, base, eval] using
      eval_suppress_ambiguous roles acc base (fun _ => A)
        (by simpa only [base, eval, WinnerSet.Ambiguous] using hA)
        (by simp only [acc, eval_unionTerm, base, eval]; exact Set.subset_union_left)

/-- A singleton is isolated by a public equation, without role switches. -/
theorem exists_public_singleton_separator (three : Fin 3 ↪ Role) (a k : Role) (hak : a ≠ k) :
    ∃ s t : Term Role (Fin 1), s.IsPublic ∧ t.IsPublic ∧
      (∀ A : WinnerSet Role, A ≠ WinnerSet.singleton a →
        s.eval (fun _ => A) = t.eval (fun _ => A)) ∧
      s.eval (fun _ => WinnerSet.singleton a) ≠ t.eval (fun _ => WinnerSet.singleton a) := by
  classical
  refine ⟨.choice a (.var 0) (.winner k), unionTerm three (.var 0) (.winner k),
    ⟨trivial, trivial⟩, by simp [unionTerm, IsPublic], ?_, ?_⟩
  · intro A hA
    simp [eval, WinnerSet.choice, hA, Ne.symm hak]
  · intro he
    have hp : WinnerSet.singleton a = WinnerSet.union (WinnerSet.singleton a)
        (WinnerSet.singleton k) := by simpa [eval, WinnerSet.choice] using he
    have hm : k ∈ (WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton k)).val := Or.inr rfl
    rw [← hp] at hm
    exact hak (Set.mem_singleton_iff.mp hm).symm

end Term

variable {Role : Type u}

/-- An arbitrary input can be represented inside D with its observer's view,
using only singleton values and one prescribed ambiguous fallback. -/
theorem exists_sameView_in_domain (D : Set (WinnerSet Role))
    (hatoms : ∀ r, WinnerSet.singleton r ∈ D) (k : Role) (F : WinnerSet Role)
    (hF : F ∈ D) (hamb : WinnerSet.Ambiguous F) (hk : k ∉ F.val) (A : WinnerSet Role) :
    ∃ B ∈ D, WinnerSet.SameView k A B := by
  cases hA : WinnerSet.view k A with
  | possible =>
    refine ⟨WinnerSet.singleton k, hatoms k, (WinnerSet.view_eq_view_iff _ _ _).mp ?_⟩
    exact hA.trans ((WinnerSet.view_eq_possible_iff _ _).mpr rfl).symm
  | other r =>
    refine ⟨WinnerSet.singleton r.val, hatoms r.val, (WinnerSet.view_eq_view_iff _ _ _).mp ?_⟩
    exact hA.trans ((WinnerSet.view_eq_other_iff _ _ r).mpr rfl).symm
  | impossible =>
    refine ⟨F, hF, (WinnerSet.view_eq_view_iff _ _ _).mp ?_⟩
    exact hA.trans ((WinnerSet.view_eq_impossible_iff _ _).mpr ⟨hk, hamb⟩).symm

/-- The exact criterion at every finite arity in the public reduct. -/
theorem completePublicTestDomain_iff [Fintype Role] (three : Fin 3 ↪ Role)
    (D : Set (WinnerSet Role)) :
    CompletePublicTestDomain D ↔
      (∀ r, WinnerSet.singleton r ∈ D) ∧
      (∀ k, ∃ F ∈ D, WinnerSet.Ambiguous F ∧ k ∉ F.val) := by
  classical
  constructor
  · intro hc
    have unary (s t : Term Role (Fin 1)) (hs : s.IsPublic) (ht : t.IsPublic)
        (he : ∀ A ∈ D, s.eval (fun _ => A) = t.eval (fun _ => A)) :
        ∀ A, s.eval (fun _ => A) = t.eval (fun _ => A) := by
      intro A
      apply hc 1 s t hs ht ?_ (fun _ => A)
      intro v hv
      have heq : v = fun _ : Fin 1 => v 0 := funext (fun x => congrArg v (Subsingleton.elim _ _))
      rw [heq]
      exact he (v 0) (hv 0)
    constructor
    · intro a
      obtain ⟨k, hka, _⟩ := exists_role_outside_pair three a a
      obtain ⟨s, t, hs, ht, he, hne⟩ := Term.exists_public_singleton_separator three a k hka.symm
      by_contra hn
      exact hne (unary s t hs ht (fun A hD => he A (fun h => hn (h ▸ hD))) _)
    · intro k
      obtain ⟨t, ht, hat, hamb⟩ := Term.exists_public_ambiguity_adder three k
      by_contra hn
      have he : ∀ A, t.eval (fun _ => A) = A := by
        apply unary t (.var 0) ht trivial
        intro A hD
        change t.eval (fun _ => A) = A
        by_cases ha : ∃ r, A = WinnerSet.singleton r
        · obtain ⟨r, rfl⟩ := ha
          exact hat r
        · have hA : WinnerSet.Ambiguous A := fun r he => ha ⟨r, he⟩
          have hk : k ∈ A.val := by
            by_contra hk
            exact hn ⟨A, hD, hA, hk⟩
          rw [hamb A hA, WinnerSet.union_comm, WinnerSet.singleton_union_of_mem A k hk]
      obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
      obtain ⟨b, hba, hbk⟩ := exists_role_outside_pair three a k
      let A := WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)
      have hA : WinnerSet.Ambiguous A := WinnerSet.ambiguous_of_two_mem A a b hba.symm
        (Or.inl rfl) (Or.inr rfl)
      have hm : k ∈ (t.eval (fun _ => A)).val := by rw [hamb A hA]; exact Or.inr rfl
      rw [he A] at hm
      exact hm.elim (fun h => hak h.symm) (fun h => hbk h.symm)
  · rintro ⟨hatoms, hcover⟩ n s t hs ht he v
    apply Subtype.ext
    ext k
    obtain ⟨F, hF, hamb, hk⟩ := hcover k
    have hrep : ∀ x, ∃ B ∈ D, WinnerSet.SameView k (v x) B :=
      fun x => exists_sameView_in_domain D hatoms k F hF hamb hk (v x)
    choose w hwD hw using hrep
    have hl := (hs.eval_sameView k v w hw).1
    have hr := (ht.eval_sameView k v w hw).1
    rw [he w hwD] at hl
    exact hl.trans hr.symm

end KFOL
