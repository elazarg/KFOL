module

public import KFOL.Core.Native

/-! # All proper native omissions are core quotients -/

@[expose] public section

namespace KFOL.Core.Native

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] structureOf Equational.coreStructure

theorem choice_ne_omitted (drop : Option Role) (r : Role) (x y : Native Role)
    (hx : x ≠ omitted drop) (hy : y ≠ omitted drop) : choice r x y ≠ omitted drop := by
  cases drop with
  | none =>
    simp only [omitted] at hx hy ⊢
    simp [hx, hy]
  | some i =>
    change x ≠ .atom i at hx
    change y ≠ .atom i at hy
    change choice r x y ≠ .atom i
    by_cases hri : r = i
    · subst r
      simp [hx, hy]
    · intro he
      exact hx ((choice_eq_atom_other r i hri x y).mp he).1

/-- Removing one atom or the upper marker gives a genuine subalgebra. -/
def omission (drop : Option Role) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (Native Role) where
  carrier := {x | x ≠ omitted drop}
  fun_mem := by
    intro n f args hargs
    cases f with
    | choice r => exact choice_ne_omitted drop r _ _ (hargs 0) (hargs 1)

/-- The explicit quotient lands in its claimed omission subalgebra. -/
noncomputable def quotientHom (drop : Option Role) :
    WinnerSet Role →[Equational.language (Equational.CoreSymbol Role)] (omission drop) where
  toFun A := ⟨quotient drop A, quotient_ne_omitted drop A⟩
  map_fun' := by
    intro n f args
    cases f with
    | choice r =>
      apply Subtype.ext
      exact quotient_choice drop r (args 0) (args 1)
  map_rel' := by intro n r; exact nomatch r

omit [DecidableEq Role] in
theorem atomicQuotient_eq_lower (A : WinnerSet Role) (hA : A.Ambiguous) :
    atomicQuotient A = .lower := by
  classical
  simp only [atomicQuotient]
  split
  next h => exact False.elim (hA h.choose h.choose_spec)
  next => rfl

/-- Surjectivity includes the two distinct ambiguity markers and uses three
roles only to realize ambiguity omitting a specified observer. -/
theorem quotientHom_surjective (three : Fin 3 ↪ Role) (drop : Option Role) :
    Function.Surjective (quotientHom drop) := by
  classical
  intro x
  obtain ⟨x, hx⟩ := x
  cases drop with
  | none =>
    cases x with
    | atom r =>
      refine ⟨WinnerSet.singleton r, ?_⟩
      apply Subtype.ext
      exact (quotient_eq_atom none (WinnerSet.singleton r) r).mpr ⟨rfl, by simp⟩
    | upper => exact False.elim (hx rfl)
    | lower =>
      let A := (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))
      have hA : A.Ambiguous := WinnerSet.ambiguous_of_two_mem _ _ _
        (three.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
      refine ⟨A, ?_⟩
      apply Subtype.ext
      exact atomicQuotient_eq_lower A hA
  | some k =>
    cases x with
    | atom r =>
      refine ⟨WinnerSet.singleton r, ?_⟩
      apply Subtype.ext
      exact (quotient_eq_atom (some k) (WinnerSet.singleton r) r).mpr
        ⟨rfl, by intro he; exact hx (congrArg Native.atom (Option.some.inj he).symm)⟩
    | upper =>
      refine ⟨WinnerSet.singleton k, ?_⟩
      apply Subtype.ext
      exact (quotient_eq_upper (some k) (WinnerSet.singleton k)).mpr ⟨k, rfl, rfl⟩
    | lower =>
      let A := PlayerView.representative three k .impossible
      have hview := PlayerView.view_representative three k PlayerView.impossible
      obtain ⟨hk, ha⟩ := (WinnerSet.view_eq_impossible_iff k A).mp hview
      refine ⟨A, ?_⟩
      apply Subtype.ext
      change (if k ∈ A.val then .upper else atomicQuotient A) = .lower
      rw [ite_eq_right hk]
      exact atomicQuotient_eq_lower A ha

/-- Every proper omission belongs to the core variety by an explicit
surjective homomorphism, rather than an assumed published result. -/
theorem omission_inVariety (three : Fin 3 ↪ Role) (drop : Option Role) :
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (omission drop) := by
  have : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton (three 0)⟩
  exact Equational.InVariety.of_surjective Equational.InVariety.refl
    (quotientHom drop) (quotientHom_surjective three drop)

/-- A native restriction keeps precisely the atoms of R and both ambiguity
markers. All role operations stay in the original full signature. -/
def restriction (R : Set Role) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (Native Role) where
  carrier := {x | ∀ r, x = .atom r → r ∈ R}
  fun_mem := by
    intro n f args hargs
    cases f with
    | choice owner =>
      intro r hr
      by_cases hor : owner = r
      · subst owner
        rcases (choice_eq_atom_owner r _ _).mp hr with h | h
        · exact hargs 0 r h
        · exact hargs 1 r h
      · exact hargs 0 r ((choice_eq_atom_other owner r hor _ _).mp hr).1

/-- Every proper native D_R is in the core variety, even when the role type
is infinite and R itself is not supplied as an enumerated finite set. -/
theorem restriction_inVariety (three : Fin 3 ↪ Role) (R : Set Role) (hR : R ≠ Set.univ) :
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (restriction R) := by
  have hex : ∃ k, k ∉ R := by
    classical
    by_contra hn
    push Not at hn
    exact hR (Set.eq_univ_iff_forall.mpr hn)
  obtain ⟨k, hk⟩ := hex
  have hsub : restriction R ≤ omission (some k) := by
    intro x hx
    change x ≠ Native.atom k
    intro he
    exact hk (hx k he)
  let f : restriction R →[Equational.language (Equational.CoreSymbol Role)] omission (some k) :=
    { toFun x := ⟨x.val, hsub x.property⟩
      map_fun' := by intro n f args; rfl
      map_rel' := by intro n r; exact nomatch r }
  have : Nonempty (restriction R) := ⟨⟨.lower, by intro r he; cases he⟩⟩
  exact Equational.InVariety.of_injective (omission_inVariety three (some k)) f (by
    intro x y he
    have hv : x.val = y.val := congrArg (fun z : omission (some k) => z.val) he
    exact Subtype.ext hv)

end KFOL.Core.Native
