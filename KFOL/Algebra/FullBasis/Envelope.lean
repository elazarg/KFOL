module

public import KFOL.Definitions.Envelope
public import KFOL.Algebra.Idempotent
public import KFOL.Core.ModelLaws
public import KFOL.Equational.Native

/-! # Purity and evaluation in the flat permutation envelope -/

@[expose] public section
namespace KFOL.Envelope
universe u v w
variable {Role : Type u} {M : Type v} {Var : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

/-- Any nonabsorbing value gives a diagonal renaming in the actual winner
algebra. No law of the payload algebra is needed. -/
theorem diagonal_of_eval (r : Role) (valuation : Var → Carrier Role M)
    (t : KFOL.Term Role Var) (g : Equiv.Perm Role) (x : M)
    (h : eval valuation t = some (g, x)) (A : WinnerSet Role) :
    (t.subst (decoration r valuation)).eval (fun _ => A) = WinnerSet.rename g A := by
  classical
  induction t generalizing g x with
  | winner => simp [eval] at h
  | var j =>
    simp only [eval] at h
    simp [KFOL.Term.subst, decoration, h, KFOL.Term.eval]
  | choice owner s t hs ht =>
    simp only [eval] at h
    cases hS : eval valuation s with
    | none => simp [hS, choice] at h
    | some sx =>
      obtain ⟨sg, sx⟩ := sx
      cases hT : eval valuation t with
      | none => simp [hS, hT, choice] at h
      | some tx =>
        obtain ⟨tg, tx⟩ := tx
        by_cases equal : sg = tg
        · subst tg
          have hg : sg = g := by simpa [hS, hT, choice] using congrArg (Option.map Prod.fst) h
          subst g
          simp only [KFOL.Term.subst, KFOL.Term.eval, hs _ _ hS, ht _ _ hT,
            WinnerSet.choice_self]
        · simp [hS, hT, choice, equal] at h
  | rename p t ih =>
    simp only [eval] at h
    cases hT : eval valuation t with
    | none => simp [hT, rename] at h
    | some tx =>
      obtain ⟨tg, tx⟩ := tx
      have hg : p * tg = g := by simpa [hT, rename] using congrArg (Option.map Prod.fst) h
      subst g
      simp only [KFOL.Term.subst, KFOL.Term.eval, ih _ _ hT, WinnerSet.rename_mul]

/-- Diagonal renaming forces exact accumulated permutation purity. -/
theorem clean_of_diagonal (three : Fin 3 ↪ Role) (t : KFOL.Term Role Var)
    (g : Equiv.Perm Role)
    (diagonal : ∀ A : WinnerSet Role, t.eval (fun _ => A) = WinnerSet.rename g A) :
    KFOL.Term.CleanUnder g⁻¹ t := by
  have hd (A : WinnerSet Role) :
      (KFOL.Term.rename g⁻¹ t).eval (fun _ => A) = A := by
    simp [KFOL.Term.eval, diagonal, ← WinnerSet.rename_mul]
  have hc := ((KFOL.Term.rename g⁻¹ t).idempotent_iff_clean three).mp hd
  have hclean : KFOL.Term.CleanUnder 1 (.rename g⁻¹ t) := by
    simpa only [KFOL.Term.CleanUnder, one_mul] using hc
  simpa only [one_mul] using KFOL.Term.cleanUnder_rename_iff.mp hclean

omit [(Equational.language (Equational.CoreSymbol Role)).Structure M] in
/-- A winner-free decorated term has exactly the indicated core shadow.
Only the final correctness lemma needs the accumulated permutations to agree. -/
theorem shadow_eq_push (r : Role) (valuation : Var → Carrier Role M)
    (t : KFOL.Term Role Var) (p : Equiv.Perm Role)
    (hn : ¬(t.subst (decoration r valuation)).HasWinner)
    (v : Option Var → WinnerSet Role) :
    let _ := Equational.coreStructure Role
    (shadow p t).realize v =
      ((t.subst (decoration r valuation)).pushRenames p).eval (fun j => v (some j)) := by
  let _ := Equational.coreStructure Role
  induction t generalizing p with
  | winner => exact False.elim (hn trivial)
  | var j =>
    cases hj : valuation j with
    | none => simp [KFOL.Term.subst, decoration, hj, KFOL.Term.HasWinner] at hn
    | some pair =>
      obtain ⟨g,x⟩ := pair
      simp [shadow, KFOL.Term.subst, decoration, hj, KFOL.Term.pushRenames, KFOL.Term.eval]
  | choice owner s t hs ht =>
    have hS : ¬(s.subst (decoration r valuation)).HasWinner := fun h => hn (Or.inl h)
    have hT : ¬(t.subst (decoration r valuation)).HasWinner := fun h => hn (Or.inr h)
    simp only [shadow, Core.realize_choice, Core.operation_winner, hs _ hS, ht _ hT,
      KFOL.Term.subst, KFOL.Term.pushRenames, KFOL.Term.eval]
  | rename q t ih =>
    exact ih (p * q) hn

omit [(Equational.language (Equational.CoreSymbol Role)).Structure M] in
theorem shadow_correct (r : Role) (valuation : Var → Carrier Role M)
    (t : KFOL.Term Role Var) (p : Equiv.Perm Role)
    (clean : KFOL.Term.CleanUnder p (t.subst (decoration r valuation)))
    (v : Option Var → WinnerSet Role) :
    let _ := Equational.coreStructure Role
    (shadow p t).realize v =
      WinnerSet.rename p ((t.subst (decoration r valuation)).eval (fun j => v (some j))) := by
  let _ := Equational.coreStructure Role
  change (shadow p t).realize v = _
  rw [shadow_eq_push r valuation t p clean.1]
  exact KFOL.Term.pushRenames_correct _ p clean _

/-- Conversely purity forces an actual value in one copy of the payload.
The payload is obtained by evaluating the core shadow. -/
theorem eval_of_clean (r : Role) (valuation : Var → Carrier Role M) (fallback : M)
    (t : KFOL.Term Role Var) (p : Equiv.Perm Role)
    (clean : KFOL.Term.CleanUnder p (t.subst (decoration r valuation))) :
    eval valuation t = some (p⁻¹, (shadow p t).realize (values fallback valuation)) := by
  classical
  induction t generalizing p with
  | winner => exact False.elim (clean.1 trivial)
  | var j =>
    cases hj : valuation j with
    | none => simp [KFOL.Term.subst, decoration, hj, KFOL.Term.CleanUnder,
        KFOL.Term.HasWinner] at clean
    | some pair =>
      obtain ⟨g,x⟩ := pair
      have hg : p * g = 1 := by
        have h := clean.2 j g (by simp [KFOL.Term.subst, decoration, hj,
          KFOL.Term.inputOccurrences])
        exact h
      have hgp : g = p⁻¹ := by
        calc g = p⁻¹ * (p * g) := by simp
             _ = p⁻¹ := by rw [hg, mul_one]
      simp [eval, shadow, values, hj, hgp]
  | choice owner s t hs ht =>
    obtain ⟨hS,hT⟩ := KFOL.Term.cleanUnder_choice_iff.mp clean
    rw [eval, hs p hS, ht p hT]
    simp only [choice, ite_true, inv_inv, shadow, Core.realize_choice]
  | rename q t ih =>
    have ht := KFOL.Term.cleanUnder_rename_iff.mp clean
    rw [eval, ih (p * q) ht]
    simp [rename, shadow]

theorem eval_decode (t : Equational.Term (Equational.FullSymbol Role) Var)
    (valuation : Var → Carrier Role M) :
    let _ := structureOf (Role := Role) (M := M)
    eval valuation (Equational.Full.decode t) = t.realize valuation := by
  let _ := structureOf (Role := Role) (M := M)
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f with
    | winner => rfl
    | choice r => exact congrArg₂ (choice r) (ih 0) (ih 1)
    | rename p => exact congrArg (rename p) (ih 0)

end KFOL.Envelope
