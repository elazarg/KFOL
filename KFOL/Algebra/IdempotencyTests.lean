module

public import KFOL.Algebra.ReductTests
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Pi

/-! # Domains certifying idempotency by diagonal evaluations -/

@[expose] public section

namespace KFOL

universe u

namespace WinnerSet

variable {Role : Type u}

/-- A permutation fixing membership of its two swapped roles fixes the set. -/
theorem rename_swap_eq_of_mem_iff [DecidableEq Role] (A : WinnerSet Role) (a b : Role)
    (h : a ∈ A.val ↔ b ∈ A.val) : rename (Equiv.swap a b) A = A := by
  classical
  have hm : ∀ x, Equiv.swap a b x ∈ A.val ↔ x ∈ A.val := by
    intro x
    by_cases ha : x = a
    · subst x
      simpa only [Equiv.swap_apply_left] using h.symm
    · by_cases hb : x = b
      · subst x
        simpa only [Equiv.swap_apply_right] using h
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  apply Subtype.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y).mpr hy
  · intro hx
    exact ⟨Equiv.swap a b x, (hm x).mpr hx, Equiv.swap_apply_self a b x⟩

/-- On a finite carrier, a permutation image contained in a set equals it. -/
theorem rename_eq_of_subset [Finite Role] (A : WinnerSet Role) (p : Equiv.Perm Role)
    (h : (rename p A).val ⊆ A.val) : rename p A = A := by
  have hm : Set.MapsTo p A.val A.val := fun x hx => h ⟨x, hx, rfl⟩
  have hb := ((Set.toFinite A.val).injOn_iff_bijOn_of_mapsTo hm).mp p.injective.injOn
  exact Subtype.ext hb.image_eq

end WinnerSet

variable {Role : Type u} [Fintype Role]

/-- Necessary even when the testing domain contains singletons. -/
theorem certifiesIdempotency_necessary (three : Fin 3 ↪ Role) (D : Set (WinnerSet Role))
    (hD : CertifiesIdempotency D) :
    (∀ k, ∃ A ∈ D, k ∉ A.val) ∧
    (∀ a b, (∀ A ∈ D, a ∈ A.val ↔ b ∈ A.val) → a = b) := by
  classical
  constructor
  · intro k
    by_contra hn
    let t : Term Role (Fin 1) := Term.unionTerm three (.var 0) (.winner k)
    have he : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
      apply hD 1 t
      intro A hA
      have hk : k ∈ A.val := by by_contra hk; exact hn ⟨A, hA, hk⟩
      simpa only [t, Term.eval_unionTerm, Term.eval] using
        (WinnerSet.union_comm A (WinnerSet.singleton k)).trans
          (WinnerSet.singleton_union_of_mem A k hk)
    obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
    have hm : k ∈ (t.eval (fun _ => WinnerSet.singleton a)).val := by
      simp only [t, Term.eval_unionTerm, Term.eval, WinnerSet.val_union]
      exact Or.inr rfl
    rw [he] at hm
    exact hak (Set.mem_singleton_iff.mp hm).symm
  · intro a b hab
    let t : Term Role (Fin 1) := .rename (Equiv.swap a b) (.var 0)
    have he : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
      apply hD 1 t
      intro A hA
      exact A.rename_swap_eq_of_mem_iff a b (hab A hA)
    have hp := he (WinnerSet.singleton a)
    simpa [t, Term.eval, eq_comm] using hp

/-- For an ambiguous domain, empty intersection and distinct incidence vectors
are sufficient at every finite arity. -/
theorem certifiesIdempotency_iff (three : Fin 3 ↪ Role) (D : Set (WinnerSet Role))
    (hamb : ∀ A ∈ D, WinnerSet.Ambiguous A) :
    CertifiesIdempotency D ↔
      (∀ k, ∃ A ∈ D, k ∉ A.val) ∧
      (∀ a b, (∀ A ∈ D, a ∈ A.val ↔ b ∈ A.val) → a = b) := by
  constructor
  · exact certifiesIdempotency_necessary three D
  · rintro ⟨homit, hsep⟩ n t he
    have hn : ¬t.HasWinner := by
      intro ht
      let top : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
      have htop : top.Ambiguous := WinnerSet.ambiguous_of_two_mem top
        (three 0) (three 1) (three.injective.ne (by decide)) trivial trivial
      obtain ⟨k, hk⟩ := t.exists_constant_on_cell (fun _ => top) ht
      obtain ⟨A, hA, hnot⟩ := homit k
      have hm := hk (fun _ => A) (fun _ => htop.sameStatus (hamb A hA))
      rw [he A hA] at hm
      exact hnot hm
    apply (t.idempotent_iff_clean three).mpr
    refine ⟨hn, ?_⟩
    intro x p hp
    apply Equiv.ext
    intro a
    change p a = a
    apply hsep
    intro A hA
    have hsub := t.input_subset_eval hn (fun _ => A) (fun _ => hamb A hA) x p hp
    rw [he A hA] at hsub
    have hfix : WinnerSet.rename p A = A := A.rename_eq_of_subset p hsub
    constructor
    · intro ha
      have hm : p a ∈ (WinnerSet.rename p A).val := by rw [hfix]; exact ha
      obtain ⟨b, hb, hba⟩ := hm
      exact p.injective hba ▸ hb
    · intro ha
      have hm : p a ∈ (WinnerSet.rename p A).val := ⟨a, ha, rfl⟩
      rwa [hfix] at hm

/-- Each role determines a distinct non-all-one Boolean incidence word.
This lower bound allows arbitrary, including singleton, test values. -/
theorem card_idempotency_domain_lower (three : Fin 3 ↪ Role) (D : Finset (WinnerSet Role))
    (hD : CertifiesIdempotency (D : Set (WinnerSet Role))) :
    Nat.clog 2 (Fintype.card Role + 1) ≤ D.card := by
  classical
  obtain ⟨homit, hsep⟩ := certifiesIdempotency_necessary three _ hD
  let f : Role → {word : D → Bool // word ≠ fun _ => true} := fun r =>
    ⟨fun A => decide (r ∈ A.val.val), by
      intro he
      obtain ⟨A, hA, hr⟩ := homit r
      have hh := congrFun he ⟨A, hA⟩
      simp [hr] at hh⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hsep
    intro A hA
    have he := congrArg (fun word => word.val ⟨A, hA⟩) hab
    exact decide_eq_decide.mp (by simpa only [f] using he)
  have hc := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card {word : D → Bool // word ≠ fun _ => true} = 2 ^ D.card - 1 := by
    rw [Fintype.card_subtype_compl (fun word : D → Bool => word = fun _ => true),
      Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rw [hcard] at hc
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  have hp : 0 < 2 ^ D.card := Nat.pow_pos (by decide)
  omega

end KFOL
