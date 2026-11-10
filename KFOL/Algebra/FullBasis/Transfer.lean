module

public import KFOL.Algebra.FullBasis.Envelope
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.EquivFin

/-! # Bounded-arity identities lift from the core to both expansions -/

@[expose] public section
namespace KFOL.Envelope
universe u v w
variable {Role : Type u} {M : Type v} {Var : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

theorem equation_of_nonabsorbing (three : Fin 3 ↪ Role) (fallback : M)
    (s t : KFOL.Term Role Var)
    (valid : ∀ v : Var → WinnerSet Role, s.eval v = t.eval v)
    (small : ∀ a b : Equational.Term (Equational.CoreSymbol Role) (Option Var),
      (let _ := Equational.coreStructure Role
       ∀ v : Option Var → WinnerSet Role, a.realize v = b.realize v) →
      ∀ v : Option Var → M, a.realize v = b.realize v)
    (valuation : Var → Carrier Role M) (g : Equiv.Perm Role) (x : M)
    (hs : eval valuation s = some (g,x)) : eval valuation s = eval valuation t := by
  have ds := diagonal_of_eval (three 0) valuation s g x hs
  have dt (A : WinnerSet Role) :
      (t.subst (decoration (three 0) valuation)).eval (fun _ => A) = WinnerSet.rename g A := by
    rw [KFOL.Term.eval_subst, ← valid, ← KFOL.Term.eval_subst]
    exact ds A
  have cs := clean_of_diagonal three _ g ds
  have ct := clean_of_diagonal three _ g dt
  have agree : let _ := Equational.coreStructure Role
      ∀ v : Option Var → WinnerSet Role,
      (shadow g⁻¹ s).realize v = (shadow g⁻¹ t).realize v := by
    let _ := Equational.coreStructure Role
    dsimp only
    intro v
    rw [shadow_correct (three 0) valuation s g⁻¹ cs,
      shadow_correct (three 0) valuation t g⁻¹ ct]
    simp only [KFOL.Term.eval_subst, valid]
  rw [eval_of_clean (three 0) valuation fallback s g⁻¹ cs,
    eval_of_clean (three 0) valuation fallback t g⁻¹ ct,
    small _ _ agree (values fallback valuation)]

theorem equation_of_core_identities (three : Fin 3 ↪ Role) (fallback : M)
    (s t : KFOL.Term Role Var)
    (valid : ∀ v : Var → WinnerSet Role, s.eval v = t.eval v)
    (small : ∀ a b : Equational.Term (Equational.CoreSymbol Role) (Option Var),
      (let _ := Equational.coreStructure Role
       ∀ v : Option Var → WinnerSet Role, a.realize v = b.realize v) →
      ∀ v : Option Var → M, a.realize v = b.realize v)
    (valuation : Var → Carrier Role M) : eval valuation s = eval valuation t := by
  cases hs : eval valuation s with
  | some pair =>
    obtain ⟨g,x⟩ := pair
    simpa only [hs] using equation_of_nonabsorbing three fallback s t valid small valuation g x hs
  | none =>
    cases ht : eval valuation t with
    | none => rfl
    | some pair =>
      obtain ⟨g,x⟩ := pair
      simpa only [hs, ht] using
        (equation_of_nonabsorbing three fallback t s (fun v => (valid v).symm)
          small valuation g x ht).symm

/-- Finite variable types are relabelled bijectively, rather than counted by
their declaration's syntactic representation. -/
theorem core_equation_fintype [Fintype Var] (n : ℕ)
    (small : ∀ e : Equational.Identity (Equational.CoreSymbol Role), e.arity ≤ n →
      (let _ := Equational.coreStructure Role; e.Holds (WinnerSet Role)) → e.Holds M)
    (card : Fintype.card Var ≤ n)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var)
    (valid : let _ := Equational.coreStructure Role
      ∀ v : Var → WinnerSet Role, s.realize v = t.realize v)
    (valuation : Var → M) : s.realize valuation = t.realize valuation := by
  classical
  let e : Equational.Identity (Equational.CoreSymbol Role) :=
    ⟨Fintype.card Var, s.relabel (Fintype.equivFin Var), t.relabel (Fintype.equivFin Var)⟩
  have he : let _ := Equational.coreStructure Role; e.Holds (WinnerSet Role) := by
    let _ := Equational.coreStructure Role
    dsimp only
    intro v
    simpa only [e, FirstOrder.Language.Term.realize_relabel, Function.comp_def] using
      valid (v ∘ Fintype.equivFin Var)
  have h := small e card he (valuation ∘ (Fintype.equivFin Var).symm)
  simpa only [e, FirstOrder.Language.Term.realize_relabel, Function.comp_def,
    Equiv.symm_apply_apply] using h

theorem full_small_identities (three : Fin 3 ↪ Role) (fallback : M) (n : ℕ)
    (small : ∀ e : Equational.Identity (Equational.CoreSymbol Role), e.arity ≤ n + 1 →
      (let _ := Equational.coreStructure Role; e.Holds (WinnerSet Role)) → e.Holds M)
    (e : Equational.Identity (Equational.FullSymbol Role)) (arity : e.arity ≤ n)
    (valid : let _ := Equational.fullStructure Role; e.Holds (WinnerSet Role)) :
    let _ := structureOf (Role := Role) (M := M); e.Holds (Carrier Role M) := by
  let _ := structureOf (Role := Role) (M := M)
  change ∀ valuation : Fin e.arity → Carrier Role M,
    e.lhs.realize valuation = e.rhs.realize valuation
  intro valuation
  rw [← eval_decode, ← eval_decode]
  apply equation_of_core_identities three fallback
  · intro v
    simpa only [Equational.Full.eval_decode] using valid v
  · intro s t h v
    apply core_equation_fintype (n + 1) small _ s t h v
    simpa only [Fintype.card_option, Fintype.card_fin] using Nat.add_le_add_right arity 1

end KFOL.Envelope
