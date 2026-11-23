module

public import KFOL.Core.BichainQuantified
public import KFOL.Core.BichainFiber
public import KFOL.Core.ProfilePruning
public import KFOL.Equational.Native
public import KFOL.Algebra.TestDomains
public import KFOL.Algebra.Views
public import KFOL.Algebra.ViewOrders.Monotone
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-! # Recognition of core term operations from marked rows

A finite family of marked rows with two Boolean endpoints gives an explicit
operation on selector inputs and row inputs. It is a core term operation
exactly when a pure bichain term omits every mark and separates the endpoints.
The operation is a baseline term capped at one owner: the baseline isolates
each row on its own selector code, and the cap forces one word for all rows.
-/

@[expose] public section
namespace KFOL.Recognition

universe u v w

variable {Role : Type u} {Var : Type v}

open WinnerSet

/-! ## Owned choice -/

theorem mem_choice_left {r k : Role} {A B : WinnerSet Role} (hk : k ∈ A.val)
    (hB : B ≠ singleton r) : k ∈ (choice r A B).val := by
  by_cases hkr : k = r
  · subst hkr
    exact (mem_choice_owner k A B).2 (Or.inl hk)
  · refine (mem_choice_other r k (Ne.symm hkr) A B).2 ⟨Or.inl hk, fun hA => ?_, hB⟩
    rw [hA] at hk
    exact hkr hk

theorem mem_choice_right {r k : Role} {A B : WinnerSet Role} (hk : k ∈ B.val)
    (hA : A ≠ singleton r) : k ∈ (choice r A B).val := by
  by_cases hkr : k = r
  · subst hkr
    exact (mem_choice_owner k A B).2 (Or.inr hk)
  · refine (mem_choice_other r k (Ne.symm hkr) A B).2 ⟨Or.inr hk, hA, fun hB => ?_⟩
    rw [hB] at hk
    exact hkr hk

theorem choice_sub {r : Role} {A B : WinnerSet Role} {S : Set Role} (hA : A.val ⊆ S)
    (hB : B.val ⊆ S) : (choice r A B).val ⊆ S :=
  (choice_subset_union r A B).trans (Set.union_subset hA hB)

theorem choice_right_owner {r : Role} (A : WinnerSet Role) :
    choice r A (singleton r) = singleton r :=
  (choice_eq_owner_iff A (singleton r) r).2 (Or.inr rfl)

theorem choice_left_owner {r : Role} (B : WinnerSet Role) :
    choice r (singleton r) B = singleton r :=
  (choice_eq_owner_iff (singleton r) B r).2 (Or.inl rfl)

theorem choice_self (r : Role) (A : WinnerSet Role) : choice r A A = A := by
  by_cases h : A = singleton r
  · rw [h]; exact choice_left_owner _
  · apply Subtype.ext
    apply Set.Subset.antisymm
    · exact choice_sub Set.Subset.rfl Set.Subset.rfl
    · intro k hk
      exact mem_choice_left hk h

/-! ## Folds of one owner over a list of inputs -/

theorem foldSel_isCore {S : Type w} (r : Role) (ι : S → Var) (L : List S) :
    ∀ y : Term Role Var, y.IsCore → (foldSel r ι y L).IsCore := by
  induction L with
  | nil => intro y hy; exact hy
  | cons u L ih => intro y hy; exact ih _ ⟨hy, trivial⟩

theorem foldSel_owner {S : Type w} (r : Role) (ι : S → Var) (v : Var → WinnerSet Role)
    (L : List S) : ∀ y : Term Role Var, y.eval v = singleton r →
      (foldSel r ι y L).eval v = singleton r := by
  induction L with
  | nil => intro y hy; exact hy
  | cons u L ih =>
    intro y hy
    refine ih _ ?_
    change choice r (y.eval v) (v (ι u)) = singleton r
    rw [hy]
    exact choice_left_owner _

theorem foldSel_absorb {S : Type w} (r : Role) (ι : S → Var) (v : Var → WinnerSet Role)
    (L : List S) : ∀ y : Term Role Var, (∃ u ∈ L, v (ι u) = singleton r) →
      (foldSel r ι y L).eval v = singleton r := by
  induction L with
  | nil => rintro y ⟨u, hu, -⟩; cases hu
  | cons u L ih =>
    rintro y ⟨u', hu', hv⟩
    rcases List.mem_cons.1 hu' with rfl | hmem
    · refine foldSel_owner r ι v L _ ?_
      change choice r (y.eval v) (v (ι u')) = singleton r
      rw [hv]
      exact choice_right_owner _
    · exact ih _ ⟨u', hmem, hv⟩

theorem foldSel_supply {S : Type w} (r : Role) (ι : S → Var) (v : Var → WinnerSet Role)
    {k : Role} (L : List S) : ∀ y : Term Role Var, k ∈ (y.eval v).val →
      (∀ u ∈ L, v (ι u) ≠ singleton r) → k ∈ ((foldSel r ι y L).eval v).val := by
  induction L with
  | nil => intro y hy _; exact hy
  | cons u L ih =>
    intro y hy hL
    refine ih _ ?_ fun u' hu' => hL u' (List.mem_cons_of_mem _ hu')
    exact mem_choice_left hy (hL u List.mem_cons_self)

theorem foldSel_sub {S : Type w} (r : Role) (ι : S → Var) (v : Var → WinnerSet Role)
    {T : Set Role} (L : List S) : ∀ y : Term Role Var, (y.eval v).val ⊆ T →
      (∀ u ∈ L, (v (ι u)).val ⊆ T) → ((foldSel r ι y L).eval v).val ⊆ T := by
  induction L with
  | nil => intro y hy _; exact hy
  | cons u L ih =>
    intro y hy hL
    refine ih _ ?_ fun u' hu' => hL u' (List.mem_cons_of_mem _ hu')
    exact choice_sub hy (hL u List.mem_cons_self)

theorem foldSel_eq_other {S : Type w} {r a : Role} (hra : r ≠ a) (ι : S → Var)
    (v : Var → WinnerSet Role) (L : List S) : ∀ y : Term Role Var,
      (foldSel r ι y L).eval v = singleton a ↔
        y.eval v = singleton a ∧ ∀ u ∈ L, v (ι u) = singleton a := by
  induction L with
  | nil => intro y; simp [foldSel]
  | cons u L ih =>
    intro y
    change (foldSel r ι (.choice r y (.var (ι u))) L).eval v = singleton a ↔ _
    rw [ih]
    change choice r (y.eval v) (v (ι u)) = singleton a ∧ _ ↔ _
    rw [choice_eq_other_iff _ _ _ hra]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-! ## Finite unions -/

theorem bigUnion_isCore {ι : Type w} (three : Fin 3 ↪ Role) (L : List ι)
    (f : ι → Term Role Var) (base : Term Role Var) (hf : ∀ i, (f i).IsCore)
    (hb : base.IsCore) : (bigUnion three L f base).IsCore := by
  induction L with
  | nil => exact hb
  | cons i L ih => exact ⟨⟨hf i, ih⟩, hf i, ih⟩

theorem mem_bigUnion {ι : Type w} (three : Fin 3 ↪ Role) (L : List ι)
    (f : ι → Term Role Var) (base : Term Role Var) (v : Var → WinnerSet Role) (k : Role) :
    k ∈ ((bigUnion three L f base).eval v).val ↔
      (∃ i ∈ L, k ∈ ((f i).eval v).val) ∨ k ∈ (base.eval v).val := by
  induction L with
  | nil => simp [bigUnion]
  | cons i L ih =>
    change k ∈ ((Term.unionTerm three (f i) (bigUnion three L f base)).eval v).val ↔ _
    rw [Term.eval_unionTerm, val_union, Set.mem_union, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc.symm

/-! ## Bichain values -/

open Bichain in
theorem inf_facts : ∀ X Y : Value,
    (Value.inf X Y = .b ↔ X = .b ∨ Y = .b) ∧ (Value.inf X Y = .c ↔ X = .c ∧ Y = .c) ∧
    (X ≠ .possible → Y ≠ .possible → Value.inf X Y ≠ .possible) ∧
    (Value.inf X Y ≠ .possible → (X = .b ∨ Y = .b) ∨ (X ≠ .possible ∧ Y ≠ .possible)) := by
  decide +kernel

open Bichain in
theorem sup_facts : ∀ X Y : Value,
    (Value.sup X Y = .c ↔ X = .c ∨ Y = .c) ∧ (Value.sup X Y = .b ↔ X = .b ∧ Y = .b) ∧
    (X ≠ .possible → Y ≠ .possible → Value.sup X Y ≠ .possible) ∧
    (Value.sup X Y ≠ .possible → (X = .c ∨ Y = .c) ∨ (X ≠ .possible ∧ Y ≠ .possible)) := by
  decide +kernel

open Bichain in
theorem resolves_facts : ∀ X Y : Value,
    (Value.Resolves X .possible) ∧ (X ≠ .possible → Value.Resolves X .neutral) ∧
    (Value.Resolves X Y → Y ≠ .possible → X ≠ .possible) ∧ Value.Resolves X X ∧
    Value.sup X .b = X := by
  unfold Value.Resolves
  decide +kernel

namespace PureTerm

open Bichain

variable {V V' : Type*}

theorem eval_map (f : V → V') (ν : V' → Value) : ∀ q : Bichain.Term V,
    (q.map f).eval ν = q.eval (fun j => ν (f j)) := by
  intro q
  induction q with
  | var j => rfl
  | inf x y hx hy => simp [Bichain.Term.map, Bichain.Term.eval, hx, hy]
  | sup x y hx hy => simp [Bichain.Term.map, Bichain.Term.eval, hx, hy]
  | union x y hx hy => simp [Bichain.Term.map, Bichain.Term.eval, hx, hy]

theorem map_isPure (f : V → V') : ∀ q : Bichain.Term V, q.IsPure → (q.map f).IsPure := by
  intro q
  induction q with
  | var j => intro _; trivial
  | inf x y hx hy => intro h; exact ⟨hx h.1, hy h.2⟩
  | sup x y hx hy => intro h; exact ⟨hx h.1, hy h.2⟩
  | union x y hx hy => intro h; exact h

theorem resolves_eval (ν ν' : V → Value) (h : ∀ j, Value.Resolves (ν j) (ν' j)) :
    ∀ q : Bichain.Term V, q.IsPure → Value.Resolves (q.eval ν) (q.eval ν') := by
  intro q
  induction q with
  | var j => intro _; exact h j
  | inf x y hx hy => intro hq; exact Value.resolves_inf _ _ _ _ (hx hq.1) (hy hq.2)
  | sup x y hx hy => intro hq; exact Value.resolves_sup _ _ _ _ (hx hq.1) (hy hq.2)
  | union x y hx hy => intro hq; exact hq.elim

theorem eval_c_mono (ν ν' : V → Value) (h : ∀ j, ν j = .c → ν' j = .c) :
    ∀ q : Bichain.Term V, q.IsPure → q.eval ν = .c → q.eval ν' = .c := by
  intro q
  induction q with
  | var j => intro _; exact h j
  | inf x y hx hy =>
    intro hq he
    have h2 := ((inf_facts _ _).2.1).1 he
    exact ((inf_facts _ _).2.1).2 ⟨hx hq.1 h2.1, hy hq.2 h2.2⟩
  | sup x y hx hy =>
    intro hq he
    exact ((sup_facts _ _).1).2 ((((sup_facts _ _).1).1 he).imp (hx hq.1) (hy hq.2))
  | union x y hx hy => intro hq; exact hq.elim

theorem eval_b_mono (ν ν' : V → Value) (h : ∀ j, ν j = .b → ν' j = .b) :
    ∀ q : Bichain.Term V, q.IsPure → q.eval ν = .b → q.eval ν' = .b := by
  intro q
  induction q with
  | var j => intro _; exact h j
  | inf x y hx hy =>
    intro hq he
    exact ((inf_facts _ _).1).2 ((((inf_facts _ _).1).1 he).imp (hx hq.1) (hy hq.2))
  | sup x y hx hy =>
    intro hq he
    have h2 := ((sup_facts _ _).2.1).1 he
    exact ((sup_facts _ _).2.1).2 ⟨hx hq.1 h2.1, hy hq.2 h2.2⟩
  | union x y hx hy => intro hq; exact hq.elim

/-- Remove an input that is false on every valuation considered. -/
def dropNone : Bichain.Term (Option V) → Option (Bichain.Term V)
  | .var none => none
  | .var (some j) => some (.var j)
  | .inf x y =>
    match dropNone x, dropNone y with
    | some a, some b => some (.inf a b)
    | _, _ => none
  | .sup x y =>
    match dropNone x, dropNone y with
    | some a, some b => some (.sup a b)
    | some a, none => some a
    | none, some b => some b
    | none, none => none
  | .union _ _ => none

theorem dropNone_spec (ν : Option V → Value) (hν : ν none = .b) :
    ∀ q : Bichain.Term (Option V), q.IsPure →
      (dropNone q = none → q.eval ν = .b) ∧
      ∀ q', dropNone q = some q' → q'.IsPure ∧ q'.eval (fun j => ν (some j)) = q.eval ν := by
  have hb : ∀ X : Value, Value.inf .b X = .b ∧ Value.inf X .b = .b ∧
      Value.sup .b X = X ∧ Value.sup X .b = X := by decide +kernel
  intro q
  induction q with
  | var j =>
    intro _
    cases j with
    | none => exact ⟨fun _ => hν, fun q' h => by simp [dropNone] at h⟩
    | some j =>
      refine ⟨fun h => by simp [dropNone] at h, fun q' h => ?_⟩
      simp only [dropNone, Option.some.injEq] at h
      subst h
      exact ⟨trivial, rfl⟩
  | inf x y hx hy =>
    intro hq
    obtain ⟨hxn, hxs⟩ := hx hq.1
    obtain ⟨hyn, hys⟩ := hy hq.2
    cases hx' : dropNone x with
    | none =>
      refine ⟨fun _ => ?_, fun q' h => by simp [dropNone, hx'] at h⟩
      change Value.inf (x.eval ν) (y.eval ν) = .b
      rw [hxn hx']
      exact (hb _).1
    | some a =>
      cases hy' : dropNone y with
      | none =>
        refine ⟨fun _ => ?_, fun q' h => by simp [dropNone, hx', hy'] at h⟩
        change Value.inf (x.eval ν) (y.eval ν) = .b
        rw [hyn hy']
        exact (hb _).2.1
      | some b =>
        refine ⟨fun h => by simp [dropNone, hx', hy'] at h, fun q' h => ?_⟩
        simp only [dropNone, hx', hy', Option.some.injEq] at h
        subst h
        refine ⟨⟨(hxs a hx').1, (hys b hy').1⟩, ?_⟩
        change Value.inf _ _ = Value.inf _ _
        rw [(hxs a hx').2, (hys b hy').2]
  | sup x y hx hy =>
    intro hq
    obtain ⟨hxn, hxs⟩ := hx hq.1
    obtain ⟨hyn, hys⟩ := hy hq.2
    cases hx' : dropNone x with
    | none =>
      cases hy' : dropNone y with
      | none =>
        refine ⟨fun _ => ?_, fun q' h => by simp [dropNone, hx', hy'] at h⟩
        change Value.sup (x.eval ν) (y.eval ν) = .b
        rw [hxn hx', hyn hy']
        exact (hb _).2.2.1
      | some b =>
        refine ⟨fun h => by simp [dropNone, hx', hy'] at h, fun q' h => ?_⟩
        simp only [dropNone, hx', hy', Option.some.injEq] at h
        subst h
        refine ⟨(hys b hy').1, ?_⟩
        change _ = Value.sup (x.eval ν) (y.eval ν)
        rw [hxn hx', (hys b hy').2]
        exact ((hb _).2.2.1).symm
    | some a =>
      cases hy' : dropNone y with
      | none =>
        refine ⟨fun h => by simp [dropNone, hx', hy'] at h, fun q' h => ?_⟩
        simp only [dropNone, hx', hy', Option.some.injEq] at h
        subst h
        refine ⟨(hxs a hx').1, ?_⟩
        change _ = Value.sup (x.eval ν) (y.eval ν)
        rw [hyn hy', (hxs a hx').2]
        exact ((hb _).2.2.2).symm
      | some b =>
        refine ⟨fun h => by simp [dropNone, hx', hy'] at h, fun q' h => ?_⟩
        simp only [dropNone, hx', hy', Option.some.injEq] at h
        subst h
        refine ⟨⟨(hxs a hx').1, (hys b hy').1⟩, ?_⟩
        change Value.sup _ _ = Value.sup _ _
        rw [(hxs a hx').2, (hys b hy').2]
  | union x y hx hy => intro hq; exact hq.elim

/-- Use every input, without changing the term where the extra input is false. -/
noncomputable def padTerm [Fintype V] (p : Bichain.Term V) : Bichain.Term (Option V) :=
  .sup (p.map some)
    ((Finset.univ : Finset (Option V)).toList.foldl (fun acc x => .inf acc (.var x)) (.var none))

theorem foldl_inf_isPure (L : List V) : ∀ q : Bichain.Term V, q.IsPure →
    (L.foldl (fun acc x => Bichain.Term.inf acc (.var x)) q).IsPure := by
  induction L with
  | nil => intro q hq; exact hq
  | cons x L ih => intro q hq; exact ih _ ⟨hq, trivial⟩

theorem foldl_inf_b (ν : V → Value) (L : List V) : ∀ q : Bichain.Term V, q.eval ν = .b →
    (L.foldl (fun acc x => Bichain.Term.inf acc (.var x)) q).eval ν = .b := by
  induction L with
  | nil => intro q hq; exact hq
  | cons x L ih =>
    intro q hq
    refine ih _ ?_
    change Value.inf (q.eval ν) (ν x) = .b
    exact ((inf_facts _ _).1).2 (Or.inl hq)

theorem padTerm_isPure [Fintype V] (p : Bichain.Term V) (hp : p.IsPure) : (padTerm p).IsPure :=
  ⟨map_isPure _ p hp, foldl_inf_isPure _ _ trivial⟩

theorem eval_padTerm [Fintype V] (p : Bichain.Term V) (ν : Option V → Value)
    (hν : ν none = .b) : (padTerm p).eval ν = p.eval (fun j => ν (some j)) := by
  change Value.sup ((p.map some).eval ν) _ = _
  rw [foldl_inf_b ν _ (.var none) (show (Bichain.Term.var none).eval ν = .b from hν), eval_map]
  exact (resolves_facts _ .b).2.2.2.2

end PureTerm

/-! ## Between pure bichain terms and core terms -/

section Bridge

variable (three : Fin 3 ↪ Role)

open Classical in
/-- What an observer other than the two endpoint owners sees in a value. -/
noncomputable def see (k : Role) (A : WinnerSet Role) : Bichain.Value :=
  if k ∈ A.val then .possible else if A = singleton (three 1) then .b
  else if A = singleton (three 2) then .c else .neutral

theorem see_possible_iff (k : Role) (A : WinnerSet Role) :
    see three k A = .possible ↔ k ∈ A.val := by
  unfold see
  split_ifs <;> simp_all

theorem see_b (k : Role) (hk : k ≠ three 1) : see three k (singleton (three 1)) = .b := by
  unfold see
  simp [hk]

theorem see_c (k : Role) (hk : k ≠ three 2) : see three k (singleton (three 2)) = .c := by
  have h12 : three 2 ≠ three 1 := three.injective.ne (by decide)
  unfold see
  simp [hk, h12]

theorem see_eq_b {k : Role} {A : WinnerSet Role} (h : see three k A = .b) :
    A = singleton (three 1) := by
  unfold see at h
  split_ifs at h with h1 h2 h3
  exact h2

theorem see_eq_c {k : Role} {A : WinnerSet Role} (h : see three k A = .c) :
    A = singleton (three 2) := by
  unfold see at h
  split_ifs at h with h1 h2 h3
  exact h3

/-- Read meet and join as the choices of the two endpoint owners. -/
def fromPure {V : Type*} (f : V → Var) : Bichain.Term V → Term Role Var
  | .var j => .var (f j)
  | .inf x y => .choice (three 1) (fromPure f x) (fromPure f y)
  | .sup x y => .choice (three 2) (fromPure f x) (fromPure f y)
  | .union x y => .choice (three 0) (fromPure f x) (fromPure f y)

theorem fromPure_isCore {V : Type*} (f : V → Var) (q : Bichain.Term V) :
    (fromPure three f q).IsCore := by
  induction q <;> simp_all [fromPure, Term.IsCore]

theorem fromPure_const {V : Type*} (f : V → Var) (v : Var → WinnerSet Role)
    (A : WinnerSet Role) (h : ∀ j, v (f j) = A) (q : Bichain.Term V) :
    (fromPure three f q).eval v = A := by
  induction q with
  | var j => exact h j
  | inf x y hx hy =>
    change choice _ ((fromPure three f x).eval v) ((fromPure three f y).eval v) = A
    rw [hx, hy, choice_self]
  | sup x y hx hy =>
    change choice _ ((fromPure three f x).eval v) ((fromPure three f y).eval v) = A
    rw [hx, hy, choice_self]
  | union x y hx hy =>
    change choice _ ((fromPure three f x).eval v) ((fromPure three f y).eval v) = A
    rw [hx, hy, choice_self]

theorem mem_fromPure {V : Type*} (f : V → Var) (v : Var → WinnerSet Role) {k : Role}
    (q : Bichain.Term V) (hk : k ∈ ((fromPure three f q).eval v).val) :
    ∃ j, k ∈ (v (f j)).val := by
  induction q with
  | var j => exact ⟨j, hk⟩
  | inf x y hx hy => exact (choice_subset_union _ _ _ hk).elim hx hy
  | sup x y hx hy => exact (choice_subset_union _ _ _ hk).elim hx hy
  | union x y hx hy => exact (choice_subset_union _ _ _ hk).elim hx hy

theorem fromPure_foldl {V : Type*} (f : V → Var) (L : List V) : ∀ q : Bichain.Term V,
    fromPure three f (L.foldl (fun acc x => Bichain.Term.inf acc (.var x)) q) =
      foldSel (three 1) f (fromPure three f q) L := by
  induction L with
  | nil => intro q; rfl
  | cons x L ih => intro q; exact ih _

/-- A pure term controls the core word read from it, for every observer other
than the two endpoint owners. -/
theorem fromPure_spec {V : Type*} (f : V → Var) {k : Role} (hkb : k ≠ three 1)
    (hkc : k ≠ three 2) (v : Var → WinnerSet Role) : ∀ q : Bichain.Term V, q.IsPure →
    (q.eval (fun j => see three k (v (f j))) = .b →
      (fromPure three f q).eval v = singleton (three 1)) ∧
    (q.eval (fun j => see three k (v (f j))) = .c →
      (fromPure three f q).eval v = singleton (three 2)) ∧
    (q.eval (fun j => see three k (v (f j))) ≠ .possible →
      k ∉ ((fromPure three f q).eval v).val) := by
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  intro q
  induction q with
  | var j =>
    intro _
    exact ⟨see_eq_b three, see_eq_c three, fun h hk => h ((see_possible_iff three k _).2 hk)⟩
  | inf x y hx hy =>
    intro hq
    obtain ⟨hxb, hxc, hxp⟩ := hx hq.1
    obtain ⟨hyb, hyc, hyp⟩ := hy hq.2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact (choice_eq_owner_iff _ _ _).2 ((((inf_facts _ _).1).1 h).imp hxb hyb)
    · have h2 := ((inf_facts _ _).2.1).1 h
      exact (choice_eq_other_iff _ _ _ h12).2 ⟨hxc h2.1, hyc h2.2⟩
    · rcases (inf_facts _ _).2.2.2 h with h2 | ⟨h2, h3⟩
      · have he : (fromPure three f (.inf x y)).eval v = singleton (three 1) :=
          (choice_eq_owner_iff _ _ _).2 (h2.imp hxb hyb)
        rw [he]
        exact hkb
      · intro hk
        exact (choice_subset_union _ _ _ hk).elim (hxp h2) (hyp h3)
  | sup x y hx hy =>
    intro hq
    obtain ⟨hxb, hxc, hxp⟩ := hx hq.1
    obtain ⟨hyb, hyc, hyp⟩ := hy hq.2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h2 := ((sup_facts _ _).2.1).1 h
      exact (choice_eq_other_iff _ _ _ h12.symm).2 ⟨hxb h2.1, hyb h2.2⟩
    · exact (choice_eq_owner_iff _ _ _).2 ((((sup_facts _ _).1).1 h).imp hxc hyc)
    · rcases (sup_facts _ _).2.2.2 h with h2 | ⟨h2, h3⟩
      · have he : (fromPure three f (.sup x y)).eval v = singleton (three 2) :=
          (choice_eq_owner_iff _ _ _).2 (h2.imp hxc hyc)
        rw [he]
        exact hkc
      · intro hk
        exact (choice_subset_union _ _ _ hk).elim (hxp h2) (hyp h3)
  | union x y hx hy => intro hq; exact hq.elim

open Classical in
/-- Keep the two endpoint owners and one branch of every other choice. -/
noncomputable def toPure : (t : Term Role Var) → t.IsCore → Bichain.Term Var
  | .var j, _ => .var j
  | .choice r x y, h =>
    if r = three 1 then .inf (toPure x h.1) (toPure y h.2)
    else if r = three 2 then .sup (toPure x h.1) (toPure y h.2) else toPure x h.1
  | .winner _, h => h.elim
  | .rename _ _, h => h.elim

theorem toPure_isPure : ∀ (t : Term Role Var) (ht : t.IsCore), (toPure three t ht).IsPure := by
  intro t
  induction t with
  | winner r => intro ht; exact ht.elim
  | rename p t ih => intro ht; exact ht.elim
  | var j => intro _; trivial
  | choice r x y hx hy =>
    intro ht
    unfold toPure
    split_ifs
    · exact ⟨hx ht.1, hy ht.2⟩
    · exact ⟨hx ht.1, hy ht.2⟩
    · exact hx ht.1

/-- On valuations without foreign atoms, the pure term keeps the endpoint
values and the omissions of the first owner. -/
theorem toPure_spec (v : Var → WinnerSet Role)
    (hv : ∀ j d, d ≠ three 0 → d ≠ three 1 → d ≠ three 2 → v j ≠ singleton d) :
    ∀ (t : Term Role Var) (ht : t.IsCore),
    (t.eval v = singleton (three 1) →
      (toPure three t ht).eval (fun j => see three (three 0) (v j)) = .b) ∧
    (t.eval v = singleton (three 2) →
      (toPure three t ht).eval (fun j => see three (three 0) (v j)) = .c) ∧
    (three 0 ∉ (t.eval v).val →
      (toPure three t ht).eval (fun j => see three (three 0) (v j)) ≠ .possible) ∧
    ∀ d, d ≠ three 0 → d ≠ three 1 → d ≠ three 2 → t.eval v ≠ singleton d := by
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  intro t
  induction t with
  | winner r => intro ht; exact ht.elim
  | rename p t ih => intro ht; exact ht.elim
  | var j =>
    intro _
    refine ⟨fun h => ?_, fun h => ?_, fun h hp => h ((see_possible_iff three _ _).1 hp), hv j⟩
    · change see three (three 0) (v j) = .b
      rw [show v j = WinnerSet.singleton (three 1) from h]
      exact see_b three _ h01
    · change see three (three 0) (v j) = .c
      rw [show v j = WinnerSet.singleton (three 2) from h]
      exact see_c three _ h02
  | choice r x y hx hy =>
    intro ht
    obtain ⟨hxb, hxc, hxp, hxd⟩ := hx ht.1
    obtain ⟨hyb, hyc, hyp, hyd⟩ := hy ht.2
    change (choice r (x.eval v) (y.eval v) = _ → _) ∧ (choice r (x.eval v) (y.eval v) = _ → _) ∧
      (_ ∉ (choice r (x.eval v) (y.eval v)).val → _) ∧
      ∀ d, _ → _ → _ → choice r (x.eval v) (y.eval v) ≠ _
    have hforeign : ∀ d, d ≠ three 0 → d ≠ three 1 → d ≠ three 2 →
        choice r (x.eval v) (y.eval v) ≠ WinnerSet.singleton d := by
      intro d d0 d1 d2 h
      by_cases hrd : r = d
      · subst hrd
        rcases (choice_eq_owner_iff _ _ _).1 h with h | h
        · exact hxd r d0 d1 d2 h
        · exact hyd r d0 d1 d2 h
      · exact hxd d d0 d1 d2 ((choice_eq_other_iff _ _ _ hrd).1 h).1
    by_cases h1 : r = three 1
    · subst h1
      have e : toPure three (.choice (three 1) x y) ht =
          .inf (toPure three x ht.1) (toPure three y ht.2) := by simp [toPure]
      rw [e]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, hforeign⟩
      · exact ((inf_facts _ _).1).2 (((choice_eq_owner_iff _ _ _).1 h).imp hxb hyb)
      · have h2 := (choice_eq_other_iff _ _ _ h12).1 h
        exact ((inf_facts _ _).2.1).2 ⟨hxc h2.1, hyc h2.2⟩
      · by_cases habs : x.eval v = WinnerSet.singleton (three 1) ∨
            y.eval v = WinnerSet.singleton (three 1)
        · have hb : Bichain.Value.inf _ _ = .b := ((inf_facts _ _).1).2 (habs.imp hxb hyb)
          change Bichain.Value.inf _ _ ≠ .possible
          rw [hb]
          decide
        · refine (inf_facts _ _).2.2.1 (hxp fun hk => h ?_) (hyp fun hk => h ?_)
          · exact mem_choice_left hk fun hy' => habs (Or.inr hy')
          · exact mem_choice_right hk fun hx' => habs (Or.inl hx')
    · by_cases h2 : r = three 2
      · subst h2
        have e : toPure three (.choice (three 2) x y) ht =
            .sup (toPure three x ht.1) (toPure three y ht.2) := by simp [toPure, h12.symm]
        rw [e]
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, hforeign⟩
        · have h3 := (choice_eq_other_iff _ _ _ h12.symm).1 h
          exact ((sup_facts _ _).2.1).2 ⟨hxb h3.1, hyb h3.2⟩
        · exact ((sup_facts _ _).1).2 (((choice_eq_owner_iff _ _ _).1 h).imp hxc hyc)
        · by_cases habs : x.eval v = WinnerSet.singleton (three 2) ∨
              y.eval v = WinnerSet.singleton (three 2)
          · have hc : Bichain.Value.sup _ _ = .c := ((sup_facts _ _).1).2 (habs.imp hxc hyc)
            change Bichain.Value.sup _ _ ≠ .possible
            rw [hc]
            decide
          · refine (sup_facts _ _).2.2.1 (hxp fun hk => h ?_) (hyp fun hk => h ?_)
            · exact mem_choice_left hk fun hy' => habs (Or.inr hy')
            · exact mem_choice_right hk fun hx' => habs (Or.inl hx')
      · have e : toPure three (.choice r x y) ht = toPure three x ht.1 := by simp [toPure, h1, h2]
        rw [e]
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, hforeign⟩
        · exact hxb ((choice_eq_other_iff _ _ _ h1).1 h).1
        · exact hxc ((choice_eq_other_iff _ _ _ h2).1 h).1
        · refine hxp fun hk => h ?_
          by_cases hr0 : r = three 0
          · subst hr0
            exact (mem_choice_owner _ _ _).2 (Or.inl hk)
          · exact mem_choice_left hk (hyd r hr0 h1 h2)

end Bridge

/-! ## The baseline and the capped operation -/

section Instance

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)

theorem baseline_isCore : (baseline three rows X Y z₀).IsCore := by
  refine bigUnion_isCore _ _ _ _ (fun _ => trivial) <|
    bigUnion_isCore _ _ _ _ (fun _ => ⟨⟨trivial, trivial⟩, trivial⟩) <|
    bigUnion_isCore _ _ _ _ (fun p => ?_) <|
    bigUnion_isCore _ _ _ _ (fun p => ?_) <|
    bigUnion_isCore _ _ _ _ (fun p => ?_) <|
    bigUnion_isCore _ _ _ _ (fun p => ?_) trivial
  · unfold u2T
    split_ifs
    · trivial
    · exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩
  · unfold kxT
    split_ifs
    · exact foldSel_isCore _ _ _ _ trivial
    · exact foldSel_isCore _ _ _ _ ⟨trivial, trivial⟩
    · trivial
  · unfold kyT
    split_ifs
    · exact foldSel_isCore _ _ _ _ trivial
    · exact foldSel_isCore _ _ _ _ ⟨trivial, trivial⟩
    · trivial
  · unfold kzT
    split_ifs
    · exact foldSel_isCore _ _ _ _ ⟨trivial, trivial⟩
    · exact foldSel_isCore _ _ _ _ ⟨⟨trivial, trivial⟩, trivial⟩
    · exact foldSel_isCore _ _ _ _ ⟨⟨trivial, trivial⟩, trivial⟩
    · trivial

theorem mem_baseline (v : Inp Z W → WinnerSet Role) (k : Role) :
    k ∈ ((baseline three rows X Y z₀).eval v).val ↔
      (∃ u : Z, k ∈ (v (.inl u)).val) ∨ (∃ p, k ∈ ((qT three p).eval v).val) ∨
      (∃ p, k ∈ ((u2T three p).eval v).val) ∨ (∃ p, k ∈ ((kxT three X z₀ p).eval v).val) ∨
      (∃ p, k ∈ ((kyT three Y z₀ p).eval v).val) ∨
      (∃ p, k ∈ ((kzT three rows z₀ p).eval v).val) ∨ k ∈ (v (.inl z₀)).val := by
  simp only [baseline, mem_bigUnion, Finset.mem_toList, Finset.mem_univ, true_and]
  rfl

/-- The core word read from a pure term, using every row input. -/
noncomputable def word (p : Bichain.Term W) : Term Role (Inp Z W) :=
  fromPure three Sum.inr (PureTerm.padTerm p)

end Instance

/-! ## The baseline on the coded valuations -/

section Coded

variable (three : Fin 3 ↪ Role)

theorem sing_sub {r : Role} {T : Set Role} (h : r ∈ T) : (singleton r).val ⊆ T :=
  Set.singleton_subset_iff.2 h

/-- The winner set standing for a bichain value. -/
def conv : Bichain.Value → WinnerSet Role
  | .b => singleton (three 1)
  | .c => singleton (three 2)
  | .possible => singleton (three 0)
  | .neutral => union (singleton (three 1)) (singleton (three 2))

theorem see_conv (x : Bichain.Value) : see three (three 0) (conv three x) = x := by
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  cases x with
  | b => exact see_b three _ h01
  | c => exact see_c three _ h02
  | possible => exact (see_possible_iff three _ _).2 rfl
  | neutral =>
    unfold see conv
    have e1 : three 0 ∉ (union (singleton (three 1)) (singleton (three 2))).val := by
      simp [h01, h02]
    have e2 : union (singleton (three 1)) (singleton (three 2)) ≠ singleton (three 1) :=
      fun h => h12 (singleton_inj.1 ((union_eq_singleton_iff _ _ _).1 h).2).symm
    have e3 : union (singleton (three 1)) (singleton (three 2)) ≠ singleton (three 2) :=
      fun h => h12 (singleton_inj.1 ((union_eq_singleton_iff _ _ _).1 h).1)
    simp [e2, e3]

theorem conv_ne_foreign (x : Bichain.Value) (d : Role) (d0 : d ≠ three 0) (d1 : d ≠ three 1)
    (d2 : d ≠ three 2) : conv three x ≠ singleton d := by
  cases x with
  | b => exact fun h => d1 (singleton_inj.1 h).symm
  | c => exact fun h => d2 (singleton_inj.1 h).symm
  | possible => exact fun h => d0 (singleton_inj.1 h).symm
  | neutral => exact fun h => d1 (singleton_inj.1 ((union_eq_singleton_iff _ _ _).1 h).1).symm

theorem conv_omits {x : Bichain.Value} (hx : x ≠ .possible) : three 0 ∉ (conv three x).val := by
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  cases x <;> simp_all [conv]

variable {Z : Type w} {W : Type w}

/-- A row on its own selector code. -/
def vRow [DecidableEq Z] (rows : Z → W → Bichain.Value) (z : Z) : Inp Z W → WinnerSet Role
  | .inl u => if u = z then singleton (three 1) else singleton (three 2)
  | .inr x => conv three (rowP rows z x)

/-- An endpoint with all selectors at one owner. -/
def vEnd (r : Role) (X : W → Bool) : Inp Z W → WinnerSet Role
  | .inl _ => singleton r
  | .inr x => if endP X x = true then singleton (three 2) else singleton (three 1)

theorem qT_sub (v : Inp Z W → WinnerSet Role) (T : Set Role) (p : Z × Option W)
    (h : (v (.inl p.1) = singleton (three 2) ∧ three 2 ∈ T) ∨
      (v (.inl p.1) = singleton (three 1) ∧ three 1 ∈ T)) :
    ((qT three p).eval v).val ⊆ T := by
  change (choice (three 2) (choice (three 1) (v (.inr p.2)) (v (.inl p.1))) (v (.inl p.1))).val ⊆ T
  rcases h with ⟨h, hT⟩ | ⟨h, hT⟩
  · rw [h, choice_right_owner]
    exact sing_sub hT
  · rw [h, choice_right_owner, choice_self]
    exact sing_sub hT

theorem u2T_sub [DecidableEq Z] (v : Inp Z W → WinnerSet Role) (T : Set Role)
    (p : Z × Z × Z × Option W) (hsel : ∀ u : Z, (v (.inl u)).val ⊆ T)
    (h : p.1 ≠ p.2.1 → ((v (.inl p.1) = singleton (three 2) ∨
        v (.inl p.2.1) = singleton (three 2)) ∧ three 2 ∈ T) ∨
      (v (.inl p.2.2.1) = singleton (three 1) ∧ three 1 ∈ T)) :
    ((u2T three p).eval v).val ⊆ T := by
  unfold u2T
  split_ifs with hp
  · exact hsel _
  · change (choice (three 1) (choice (three 2) (choice (three 2) (v (.inr p.2.2.2))
      (v (.inl p.1))) (v (.inl p.2.1))) (v (.inl p.2.2.1))).val ⊆ T
    rcases h hp with ⟨h, hT⟩ | ⟨h, hT⟩
    · refine choice_sub ?_ (hsel _)
      rcases h with h | h
      · rw [h, choice_right_owner, choice_left_owner]
        exact sing_sub hT
      · rw [h, choice_right_owner]
        exact sing_sub hT
    · rw [h, choice_right_owner]
      exact sing_sub hT

theorem KX_absorb [Fintype Z] (v : Inp Z W → WinnerSet Role) (y : Term Role (Inp Z W))
    (h : ∃ u : Z, v (.inl u) = singleton (three 1)) :
    (KX three y).eval v = singleton (three 1) :=
  foldSel_absorb _ _ _ _ _ (h.imp fun u hu => ⟨Finset.mem_toList.2 (Finset.mem_univ u), hu⟩)

theorem KX_sub [Fintype Z] (v : Inp Z W → WinnerSet Role) (T : Set Role)
    (y : Term Role (Inp Z W)) (hy : (y.eval v).val ⊆ T) (hsel : ∀ u : Z, (v (.inl u)).val ⊆ T) :
    ((KX three y).eval v).val ⊆ T :=
  foldSel_sub _ _ _ _ _ hy fun u _ => hsel u

theorem KY_absorb [Fintype Z] (v : Inp Z W → WinnerSet Role) (y : Term Role (Inp Z W))
    (h : ∃ u : Z, v (.inl u) = singleton (three 2)) :
    (KY three y).eval v = singleton (three 2) :=
  foldSel_absorb _ _ _ _ _ (h.imp fun u hu => ⟨Finset.mem_toList.2 (Finset.mem_univ u), hu⟩)

theorem KY_sub [Fintype Z] (v : Inp Z W → WinnerSet Role) (T : Set Role)
    (y : Term Role (Inp Z W)) (hy : (y.eval v).val ⊆ T) (hsel : ∀ u : Z, (v (.inl u)).val ⊆ T) :
    ((KY three y).eval v).val ⊆ T :=
  foldSel_sub _ _ _ _ _ hy fun u _ => hsel u

theorem Kz_absorb [Fintype Z] [DecidableEq Z] (v : Inp Z W → WinnerSet Role) (z : Z)
    (y : Term Role (Inp Z W)) (h : ∃ u : Z, u ≠ z ∧ v (.inl u) = singleton (three 1)) :
    (Kz three z y).eval v = singleton (three 1) := by
  obtain ⟨u, hu, hv⟩ := h
  exact foldSel_absorb _ _ _ _ _
    ⟨u, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hu, Finset.mem_univ u⟩), hv⟩

theorem Kz_sub [Fintype Z] [DecidableEq Z] (v : Inp Z W → WinnerSet Role) (T : Set Role) (z : Z)
    (y : Term Role (Inp Z W))
    (hy : (choice (three 2) (y.eval v) (v (.inl z))).val ⊆ T)
    (hsel : ∀ u : Z, (v (.inl u)).val ⊆ T) : ((Kz three z y).eval v).val ⊆ T :=
  foldSel_sub _ _ _ _ _ hy fun u _ => hsel u

variable [Fintype Z] [DecidableEq Z] [Nontrivial Z] [Fintype W]
  (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)

/-- On the code of a row, the baseline omits the first owner. -/
theorem baseline_row (z : Z) :
    three 0 ∉ ((baseline three rows X Y z₀).eval (vRow three rows z)).val := by
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  let T : Set Role := {k | k ≠ three 0}
  have hb : three 1 ∈ T := h01.symm
  have hc : three 2 ∈ T := h02.symm
  have hz : vRow three rows z (.inl z) = singleton (three 1) := by simp [vRow]
  have hnz : ∀ u : Z, u ≠ z → vRow three rows z (.inl u) = singleton (three 2) :=
    fun u hu => by simp [vRow, hu]
  have hsel : ∀ u : Z, (vRow three rows z (.inl u)).val ⊆ T := by
    intro u
    by_cases hu : u = z
    · rw [hu, hz]; exact sing_sub hb
    · rw [hnz u hu]; exact sing_sub hc
  obtain ⟨u', hu'⟩ := exists_ne z
  suffices h : ((baseline three rows X Y z₀).eval (vRow three rows z)).val ⊆ T from
    fun hk => h hk rfl
  intro k hk
  rcases (mem_baseline three rows X Y z₀ _ k).1 hk with
    ⟨u, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | h
  · exact hsel u h
  · refine qT_sub three _ T p ?_ h
    by_cases hp : p.1 = z
    · exact Or.inr ⟨by rw [hp, hz], hb⟩
    · exact Or.inl ⟨hnz _ hp, hc⟩
  · refine u2T_sub three _ T p hsel (fun hne => Or.inl ⟨?_, hc⟩) h
    by_cases hp : p.1 = z
    · exact Or.inr (hnz _ fun h2 => hne (hp.trans h2.symm))
    · exact Or.inl (hnz _ hp)
  · have key : ∀ y, ((KX three y).eval (vRow three rows z)).val ⊆ T := fun y => by
      rw [KX_absorb three _ y ⟨z, hz⟩]; exact sing_sub hb
    revert h
    unfold kxT
    split_ifs <;> intro h
    · exact key _ h
    · exact key _ h
    · exact hsel z₀ h
  · have key : ∀ y, ((KY three y).eval (vRow three rows z)).val ⊆ T := fun y => by
      rw [KY_absorb three _ y ⟨u', hnz u' hu'⟩]; exact sing_sub hc
    revert h
    unfold kyT
    split_ifs <;> intro h
    · exact key _ h
    · exact key _ h
    · exact hsel z₀ h
  · obtain ⟨z', x, i⟩ := p
    have habs : ∀ y, z' ≠ z → ((Kz three z' y).eval (vRow three rows z)).val ⊆ T :=
      fun y hne => by
        rw [Kz_absorb three _ z' y ⟨z, Ne.symm hne, hz⟩]; exact sing_sub hb
    have hown : ∀ y : Term Role (Inp Z W), (y.eval (vRow three rows z)).val ⊆ T →
        ((Kz three z y).eval (vRow three rows z)).val ⊆ T :=
      fun y hy => Kz_sub three _ T z y (choice_sub hy (hsel z)) hsel
    simp only [kzT] at h
    split_ifs at h with h1 h2 h3
    · by_cases hz' : z' = z
      · subst hz'
        refine hown (.var (.inr x)) (fun k' hk' hk0 => conv_omits three h1 ?_) h
        rw [← hk0]
        exact hk'
      · exact habs _ hz' h
    · by_cases hz' : z' = z
      · subst hz'
        refine hown _ ?_ h
        change (choice (three 1) _ (conv three (rowP rows z' i))).val ⊆ T
        rw [h2]
        change (choice (three 1) _ (singleton (three 1))).val ⊆ T
        rw [choice_right_owner]
        exact sing_sub hb
      · exact habs _ hz' h
    · by_cases hz' : z' = z
      · subst hz'
        refine hown _ ?_ h
        change (choice (three 2) _ (conv three (rowP rows z' i))).val ⊆ T
        rw [h3]
        change (choice (three 2) _ (singleton (three 2))).val ⊆ T
        rw [choice_right_owner]
        exact sing_sub hc
      · exact habs _ hz' h
    · exact hsel z₀ h
  · exact hsel z₀ h

omit [Nontrivial Z] in
/-- On the code of the first endpoint, the baseline is the third owner alone. -/
theorem baseline_X :
    (baseline three rows X Y z₀).eval (vEnd three (three 2) X) = singleton (three 2) := by
  apply eq_singleton_of_subset
  have hsel : ∀ u : Z, (vEnd three (three 2) X (.inl u : Inp Z W)).val ⊆ {three 2} :=
    fun _ => Set.Subset.rfl
  intro k hk
  rcases (mem_baseline three rows X Y z₀ _ k).1 hk with
    ⟨u, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | h
  · exact h
  · exact qT_sub three _ {three 2} p (Or.inl ⟨rfl, Set.mem_singleton _⟩) h
  · exact u2T_sub three _ {three 2} p hsel
      (fun _ => Or.inl ⟨Or.inl rfl, Set.mem_singleton _⟩) h
  · obtain ⟨x, i⟩ := p
    simp only [kxT] at h
    split_ifs at h with h1 h2
    · refine KX_sub three _ _ _ ?_ hsel h
      change (vEnd three (three 2) X (.inr x : Inp Z W)).val ⊆ _
      simp [vEnd, h1]
    · refine KX_sub three _ _ _ ?_ hsel h
      have hi : vEnd three (three 2) X (.inr i : Inp Z W) = WinnerSet.singleton (three 2) := by
        simp [vEnd, h2]
      change (choice (three 2) _ (vEnd three (three 2) X (.inr i : Inp Z W))).val ⊆ _
      rw [hi, choice_right_owner]
      exact Set.Subset.rfl
    · exact h
  · have key : ∀ y, ((KY three y).eval (vEnd three (three 2) X : Inp Z W → _)).val ⊆
        {three 2} := fun y => by
      rw [KY_absorb three _ y ⟨z₀, rfl⟩]
      exact Set.Subset.rfl
    revert h
    unfold kyT
    split_ifs <;> intro h
    · exact key _ h
    · exact key _ h
    · exact h
  · obtain ⟨z', x, i⟩ := p
    have key : ∀ y, ((Kz three z' y).eval (vEnd three (three 2) X : Inp Z W → _)).val ⊆
        {three 2} := fun y => by
      refine Kz_sub three _ _ z' y ?_ hsel
      change (choice (three 2) _ (WinnerSet.singleton (three 2))).val ⊆ _
      rw [choice_right_owner]
      exact Set.Subset.rfl
    simp only [kzT] at h
    split_ifs at h
    · exact key _ h
    · exact key _ h
    · exact key _ h
    · exact h
  · exact h

/-- On the code of the second endpoint, the baseline is the second owner alone. -/
theorem baseline_Y :
    (baseline three rows X Y z₀).eval (vEnd three (three 1) Y) = singleton (three 1) := by
  apply eq_singleton_of_subset
  have hsel : ∀ u : Z, (vEnd three (three 1) Y (.inl u : Inp Z W)).val ⊆ {three 1} :=
    fun _ => Set.Subset.rfl
  intro k hk
  rcases (mem_baseline three rows X Y z₀ _ k).1 hk with
    ⟨u, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | h
  · exact h
  · exact qT_sub three _ {three 1} p (Or.inr ⟨rfl, Set.mem_singleton _⟩) h
  · exact u2T_sub three _ {three 1} p hsel
      (fun _ => Or.inr ⟨rfl, Set.mem_singleton _⟩) h
  · have key : ∀ y, ((KX three y).eval (vEnd three (three 1) Y : Inp Z W → _)).val ⊆
        {three 1} := fun y => by
      rw [KX_absorb three _ y ⟨z₀, rfl⟩]
      exact Set.Subset.rfl
    revert h
    unfold kxT
    split_ifs <;> intro h
    · exact key _ h
    · exact key _ h
    · exact h
  · obtain ⟨x, i⟩ := p
    simp only [kyT] at h
    split_ifs at h with h1 h2
    · refine KY_sub three _ _ _ ?_ hsel h
      change (vEnd three (three 1) Y (.inr x : Inp Z W)).val ⊆ _
      simp [vEnd, h1]
    · refine KY_sub three _ _ _ ?_ hsel h
      have hi : vEnd three (three 1) Y (.inr i : Inp Z W) = WinnerSet.singleton (three 1) := by
        simp [vEnd, h2]
      change (choice (three 1) _ (vEnd three (three 1) Y (.inr i : Inp Z W))).val ⊆ _
      rw [hi, choice_right_owner]
      exact Set.Subset.rfl
    · exact h
  · obtain ⟨z', x, i⟩ := p
    obtain ⟨u', hu'⟩ := exists_ne z'
    have key : ∀ y, ((Kz three z' y).eval (vEnd three (three 1) Y : Inp Z W → _)).val ⊆
        {three 1} := fun y => by
      rw [Kz_absorb three _ z' y ⟨u', hu', rfl⟩]
      exact Set.Subset.rfl
    simp only [kzT] at h
    split_ifs at h
    · exact key _ h
    · exact key _ h
    · exact key _ h
    · exact h
  · exact h

end Coded

/-! ## The word lies below the baseline -/

section Main

attribute [local instance] Equational.coreStructure

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Nontrivial Z] [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)

omit [Fintype Z] [DecidableEq Z] [Nontrivial Z] in
/-- The word is the first owner's atom exactly when every row input is. -/
theorem word_cap (p : Bichain.Term W) (v : Inp Z W → WinnerSet Role) :
    (word three p : Term Role (Inp Z W)).eval v = singleton (three 0) ↔
      ∀ x : Option W, v (.inr x) = singleton (three 0) := by
  have h10 : three 1 ≠ three 0 := three.injective.ne (by decide)
  have h20 : three 2 ≠ three 0 := three.injective.ne (by decide)
  constructor
  · intro h
    change choice (three 2) _ _ = _ at h
    have h2 := ((choice_eq_other_iff _ _ _ h20).1 h).2
    rw [fromPure_foldl] at h2
    have h3 := (foldSel_eq_other h10 Sum.inr v _ _).1 h2
    exact fun x => h3.2 x (Finset.mem_toList.2 (Finset.mem_univ x))
  · intro h
    exact fromPure_const three Sum.inr v _ h _

/-- A separating word never exceeds the baseline. -/
theorem word_le_baseline (p : Bichain.Term W) (hp : p.IsPure)
    (hrow : ∀ z, p.eval (rows z) ≠ .possible)
    (hX : p.eval (fun j => Bichain.Value.ofBool (X j)) = .c)
    (hY : p.eval (fun j => Bichain.Value.ofBool (Y j)) = .b)
    (v : Inp Z W → WinnerSet Role) (k : Role)
    (hk : k ∈ ((word three p : Term Role (Inp Z W)).eval v).val) :
    k ∈ ((baseline three rows X Y z₀).eval v).val := by
  classical
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hp' := PureTerm.padTerm_isPure p hp
  have hrow' : ∀ z, (PureTerm.padTerm p).eval (rowP rows z) ≠ .possible := fun z => by
    rw [PureTerm.eval_padTerm p _ rfl]
    exact hrow z
  have hX' : (PureTerm.padTerm p).eval (fun x => Bichain.Value.ofBool (endP X x)) = .c := by
    rw [PureTerm.eval_padTerm p _ rfl]
    exact hX
  have hY' : (PureTerm.padTerm p).eval (fun x => Bichain.Value.ofBool (endP Y x)) = .b := by
    rw [PureTerm.eval_padTerm p _ rfl]
    exact hY
  obtain ⟨x, hx⟩ := mem_fromPure three Sum.inr v _ hk
  have mem := mem_baseline three rows X Y z₀ v k
  have hbc : (WinnerSet.singleton (three 1) : WinnerSet Role) ≠ WinnerSet.singleton (three 2) :=
    fun h => h12 (singleton_inj.1 h)
  by_cases hjunk : ∃ u : Z, v (.inl u) ≠ WinnerSet.singleton (three 1) ∧
      v (.inl u) ≠ WinnerSet.singleton (three 2)
  · obtain ⟨u, hu1, hu2⟩ := hjunk
    exact mem.2 (Or.inr (Or.inl ⟨(u, x), mem_choice_left (mem_choice_left hx hu1) hu2⟩))
  have hatom : ∀ u : Z, v (.inl u) = WinnerSet.singleton (three 1) ∨
      v (.inl u) = WinnerSet.singleton (three 2) := by
    intro u
    by_contra h
    exact hjunk ⟨u, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  by_cases hsomeb : ∃ z : Z, v (.inl z) = WinnerSet.singleton (three 1)
  · obtain ⟨z, hz⟩ := hsomeb
    by_cases hsecond : ∃ u : Z, u ≠ z ∧ v (.inl u) = WinnerSet.singleton (three 1)
    · obtain ⟨u2, hu2, hv2⟩ := hsecond
      by_cases hsomec : ∃ u3 : Z, v (.inl u3) = WinnerSet.singleton (three 2)
      · obtain ⟨u3, hv3⟩ := hsomec
        refine mem.2 (Or.inr (Or.inr (Or.inl ⟨(z, u2, u3, x), ?_⟩)))
        have e : u2T three (z, u2, u3, x) = (.choice (three 1) (.choice (three 2)
            (.choice (three 2) (.var (.inr x)) (.var (.inl z))) (.var (.inl u2)))
            (.var (.inl u3)) : Term Role (Inp Z W)) := by
          simp [u2T, Ne.symm hu2]
        rw [e]
        refine mem_choice_left (mem_choice_left (mem_choice_left hx ?_) ?_) ?_
        · exact fun h => hbc (hz.symm.trans h)
        · exact fun h => hbc (hv2.symm.trans h)
        · exact fun h => hbc.symm (hv3.symm.trans h)
      · have hall : ∀ u : Z, v (.inl u) = WinnerSet.singleton (three 1) :=
          fun u => (hatom u).resolve_right fun h => hsomec ⟨u, h⟩
        by_cases hYm : ∀ i : Option W, endP Y i = false →
            v (.inr i) = WinnerSet.singleton (three 1)
        · have hb := PureTerm.eval_b_mono (fun i => Bichain.Value.ofBool (endP Y i))
            (fun i => see three (three 0) (v (.inr i))) (fun i hi => by
              have hi' : endP Y i = false := by
                cases h : endP Y i
                · rfl
                · rw [h] at hi; cases hi
              rw [hYm i hi']
              exact see_b three _ h01) _ hp' hY'
          have hw := (fromPure_spec three Sum.inr h01 h02 v _ hp').1 hb
          have hkb : k = three 1 := by
            rw [show (word three p : Term Role (Inp Z W)).eval v = _ from hw] at hk
            exact hk
          exact mem.2 (Or.inl ⟨z, by rw [hz, hkb]; rfl⟩)
        · push Not at hYm
          obtain ⟨i₀, hi₀, hne⟩ := hYm
          refine mem.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(x, i₀), ?_⟩)))))
          have hnc : ∀ u ∈ (Finset.univ : Finset Z).toList,
              v (.inl u) ≠ WinnerSet.singleton (three 2) := fun u _ => by
            rw [hall u]; exact hbc
          by_cases hx' : endP Y x = false
          · have e : kyT three Y z₀ (x, i₀) = KY three (.var (.inr x)) := by simp [kyT, hx']
            rw [e]
            exact foldSel_supply _ _ _ _ _ hx hnc
          · have e : kyT three Y z₀ (x, i₀) =
                KY three (.choice (three 1) (.var (.inr x)) (.var (.inr i₀))) := by
              simp [kyT, hx', hi₀]
            rw [e]
            exact foldSel_supply _ _ _ _ _ (mem_choice_left hx hne) hnc
    · have hoth : ∀ u : Z, u ≠ z → v (.inl u) = WinnerSet.singleton (three 2) :=
        fun u hu => (hatom u).resolve_left fun h => hsecond ⟨u, hu, h⟩
      by_cases hkb : k = three 1
      · exact mem.2 (Or.inl ⟨z, by rw [hz, hkb]; rfl⟩)
      by_cases hkc : k = three 2
      · obtain ⟨u', hu'⟩ := exists_ne z
        exact mem.2 (Or.inl ⟨u', by rw [hoth u' hu', hkc]; rfl⟩)
      have supply : ∀ y : Term Role (Inp Z W), k ∈ (y.eval v).val →
          k ∈ ((Kz three z y).eval v).val := fun y hy =>
        foldSel_supply _ _ _ _ _ (mem_choice_left hy fun h => hbc (hz.symm.trans h))
          (fun u hu => by
            rw [hoth u (Finset.ne_of_mem_erase (Finset.mem_toList.1 hu))]
            exact hbc.symm)
      have kz : ∀ q, k ∈ ((kzT three rows z₀ q).eval v).val →
          k ∈ ((baseline three rows X Y z₀).eval v).val := fun q h =>
        mem.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h⟩))))))
      by_cases hx' : rowP rows z x = .possible
      · by_cases hfix : ∃ i : Option W,
            (rowP rows z i = .b ∧ v (.inr i) ≠ WinnerSet.singleton (three 1)) ∨
            (rowP rows z i = .c ∧ v (.inr i) ≠ WinnerSet.singleton (three 2))
        · obtain ⟨i, hi | hi⟩ := hfix
          · refine kz (z, x, i) ?_
            have e : kzT three rows z₀ (z, x, i) =
                Kz three z (.choice (three 1) (.var (.inr x)) (.var (.inr i))) := by
              simp [kzT, hx', hi.1]
            rw [e]
            exact supply _ (mem_choice_left hx hi.2)
          · refine kz (z, x, i) ?_
            have e : kzT three rows z₀ (z, x, i) =
                Kz three z (.choice (three 2) (.var (.inr x)) (.var (.inr i))) := by
              simp [kzT, hx', hi.1]
            rw [e]
            exact supply _ (mem_choice_left hx hi.2)
        · by_cases hfree : ∃ i : Option W, rowP rows z i = .neutral ∧ k ∈ (v (.inr i)).val
          · obtain ⟨i, hi1, hi2⟩ := hfree
            refine kz (z, i, i) ?_
            have e : kzT three rows z₀ (z, i, i) = Kz three z (.var (.inr i)) := by
              simp [kzT, hi1]
            rw [e]
            exact supply _ hi2
          · exfalso
            have hres : ∀ i : Option W,
                Bichain.Value.Resolves (see three k (v (.inr i))) (rowP rows z i) := by
              intro i
              cases hr : rowP rows z i with
              | possible => exact (resolves_facts _ .b).1
              | b =>
                have hvi : v (.inr i) = WinnerSet.singleton (three 1) := by
                  by_contra h
                  exact hfix ⟨i, Or.inl ⟨hr, h⟩⟩
                rw [hvi, see_b three k hkb]
                exact (resolves_facts _ .b).2.2.2.1
              | c =>
                have hvi : v (.inr i) = WinnerSet.singleton (three 2) := by
                  by_contra h
                  exact hfix ⟨i, Or.inr ⟨hr, h⟩⟩
                rw [hvi, see_c three k hkc]
                exact (resolves_facts _ .b).2.2.2.1
              | neutral =>
                refine (resolves_facts _ .b).2.1 fun hpos => ?_
                exact hfree ⟨i, hr, (see_possible_iff three k _).1 hpos⟩
            have hmono := PureTerm.resolves_eval _ _ hres _ hp'
            have hnp := (resolves_facts _ _).2.2.1 hmono (hrow' z)
            exact (fromPure_spec three Sum.inr hkb hkc v _ hp').2.2 hnp hk
      · refine kz (z, x, x) ?_
        have e : kzT three rows z₀ (z, x, x) = Kz three z (.var (.inr x)) := by
          simp [kzT, hx']
        rw [e]
        exact supply _ hx
  · have hall : ∀ u : Z, v (.inl u) = WinnerSet.singleton (three 2) :=
      fun u => (hatom u).resolve_left fun h => hsomeb ⟨u, h⟩
    by_cases hXm : ∀ i : Option W, endP X i = true →
        v (.inr i) = WinnerSet.singleton (three 2)
    · have hc := PureTerm.eval_c_mono (fun i => Bichain.Value.ofBool (endP X i))
        (fun i => see three (three 0) (v (.inr i))) (fun i hi => by
          have hi' : endP X i = true := by
            cases h : endP X i
            · rw [h] at hi; cases hi
            · rfl
          rw [hXm i hi']
          exact see_c three _ h02) _ hp' hX'
      have hw := (fromPure_spec three Sum.inr h01 h02 v _ hp').2.1 hc
      have hkc : k = three 2 := by
        rw [show (word three p : Term Role (Inp Z W)).eval v = _ from hw] at hk
        exact hk
      exact mem.2 (Or.inl ⟨z₀, by rw [hall z₀, hkc]; rfl⟩)
    · push Not at hXm
      obtain ⟨i₀, hi₀, hne⟩ := hXm
      refine mem.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨(x, i₀), ?_⟩))))
      have hnb : ∀ u ∈ (Finset.univ : Finset Z).toList,
          v (.inl u) ≠ WinnerSet.singleton (three 1) := fun u _ => by
        rw [hall u]; exact hbc.symm
      by_cases hx' : endP X x = true
      · have e : kxT three X z₀ (x, i₀) = KX three (.var (.inr x)) := by simp [kxT, hx']
        rw [e]
        exact foldSel_supply _ _ _ _ _ hx hnb
      · have e : kxT three X z₀ (x, i₀) =
            KX three (.choice (three 2) (.var (.inr x)) (.var (.inr i₀))) := by
          simp [kxT, hx', hi₀]
        rw [e]
        exact foldSel_supply _ _ _ _ _ (mem_choice_left hx hne) hnb

/-- The capped baseline is a core term operation exactly when a pure term
omits every mark of the rows and separates the two endpoints. -/
theorem recognition_iff :
    (∃ t : Term Role (Inp Z W), t.IsCore ∧ ∀ v, t.eval v = target three rows X Y z₀ v) ↔
      ∃ p : Bichain.Term W, p.IsPure ∧ (∀ z, p.eval (rows z) ≠ .possible) ∧
        p.eval (fun j => Bichain.Value.ofBool (X j)) = .c ∧
        p.eval (fun j => Bichain.Value.ofBool (Y j)) = .b := by
  classical
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  constructor
  · rintro ⟨t, ht, heq⟩
    let t' := Equational.Core.encode t ht
    have hreal : ∀ v : Inp Z W → WinnerSet Role, t'.realize v = t.eval v := fun v => by
      have h := Equational.Core.eval_decode t' v
      rw [Equational.Core.decode_encode] at h
      exact h.symm
    let v₀ : Inp Z W → WinnerSet Role := fun x =>
      match x with
      | .inl _ => WinnerSet.singleton (three 1)
      | .inr _ => WinnerSet.singleton (three 0)
    let A : Inp Z W → Bool := fun x => decide (v₀ x = WinnerSet.singleton (three 0))
    have h0 : t'.realize v₀ = WinnerSet.singleton (three 0) := by
      rw [hreal, heq]
      unfold target
      split_ifs with h
      · rfl
      · exact absurd (fun _ => rfl) h
    have hprof : Core.profile (three 0) A t' = true :=
      (Core.winnerSet_eq_singleton_iff_profile t' (three 0) v₀).1 h0
    obtain ⟨u, -, hu⟩ := Core.exists_view_below_of_profile (three 0) A t' hprof
    have hA : ∀ x : {x // A x = true}, ∃ y, x.val = Sum.inr y := by
      rintro ⟨x | y, hx⟩
      · exfalso
        have hx' : v₀ (Sum.inl x) = WinnerSet.singleton (three 0) := of_decide_eq_true hx
        exact h01 (singleton_inj.1 hx').symm
      · exact ⟨y, rfl⟩
    let proj : {x // A x = true} → Option W := fun x =>
      match x.val with
      | .inl _ => none
      | .inr y => y
    have hproj : ∀ x : {x // A x = true}, Sum.inr (proj x) = x.val := by
      intro x
      obtain ⟨y, hy⟩ := hA x
      simp only [proj, hy]
    let u₁ := Equational.Core.decode u
    have hu₁ : u₁.IsCore := Equational.Core.isCore_decode u
    let q : Bichain.Term (Option W) := (toPure three u₁ hu₁).map proj
    have hq : q.IsPure := PureTerm.map_isPure _ _ (toPure_isPure three u₁ hu₁)
    have key : ∀ v : Inp Z W → WinnerSet Role,
        (∀ y d, d ≠ three 0 → d ≠ three 1 → d ≠ three 2 → v (.inr y) ≠ WinnerSet.singleton d) →
        (∃ y : Option W, v (.inr y) ≠ WinnerSet.singleton (three 0)) →
        ((baseline three rows X Y z₀).eval v = WinnerSet.singleton (three 1) →
          q.eval (fun y => see three (three 0) (v (.inr y))) = .b) ∧
        ((baseline three rows X Y z₀).eval v = WinnerSet.singleton (three 2) →
          q.eval (fun y => see three (three 0) (v (.inr y))) = .c) ∧
        (three 0 ∉ ((baseline three rows X Y z₀).eval v).val →
          q.eval (fun y => see three (three 0) (v (.inr y))) ≠ .possible) := by
      intro v hfor hnotcap
      have htv : t.eval v = (baseline three rows X Y z₀).eval v := by
        rw [heq]
        unfold target
        split_ifs with h
        · obtain ⟨y, hy⟩ := hnotcap
          exact absurd (h y) hy
        · rfl
      have hb := (view_below_iff (three 0) _ _).1 (hu v)
      rw [hreal, htv] at hb
      have hspec := toPure_spec three (fun x : {x // A x = true} => v x.val)
        (fun x d d0 d1 d2 => by
          obtain ⟨y, hy⟩ := hA x
          rw [hy]
          exact hfor y d d0 d1 d2) u₁ hu₁
      have hue : u₁.eval (fun x => v x.val) = u.realize (fun x => v x.val) :=
        Equational.Core.eval_decode u _
      have hqe : q.eval (fun y => see three (three 0) (v (.inr y))) =
          (toPure three u₁ hu₁).eval (fun x => see three (three 0) (v x.val)) := by
        rw [PureTerm.eval_map]
        congr 1
        funext x
        rw [hproj x]
      rw [hqe]
      refine ⟨fun h => hspec.1 ?_, fun h => hspec.2.1 ?_, fun h => hspec.2.2.1 ?_⟩
      · rw [hue]
        exact hb.2 _ h01.symm h
      · rw [hue]
        exact hb.2 _ h02.symm h
      · rw [hue]
        exact fun hk => h (hb.1 hk)
    have krow : ∀ z, q.eval (rowP rows z) ≠ .possible := by
      intro z
      have h := (key (vRow three rows z) (fun y d d0 d1 d2 => conv_ne_foreign three _ d d0 d1 d2)
        ⟨none, fun h => h01 (singleton_inj.1 h).symm⟩).2.2 (baseline_row three rows X Y z₀ z)
      have e : (fun y => see three (three 0) (vRow three rows z (.inr y))) = rowP rows z := by
        funext y
        exact see_conv three _
      rwa [e] at h
    have hsee : ∀ (r : Role) (E : W → Bool) (y : Option W),
        see three (three 0) (vEnd three r E (.inr y : Inp Z W)) =
          Bichain.Value.ofBool (endP E y) := by
      intro r E y
      cases h : endP E y
      · simp only [vEnd, h]
        exact see_b three _ h01
      · simp only [vEnd, h]
        exact see_c three _ h02
    have hforE : ∀ (r : Role) (E : W → Bool) (y : Option W) (d : Role), d ≠ three 0 →
        d ≠ three 1 → d ≠ three 2 →
        vEnd three r E (.inr y : Inp Z W) ≠ WinnerSet.singleton d := by
      intro r E y d d0 d1 d2 h
      cases hy : endP E y
      · simp only [vEnd, hy] at h
        exact d1 (singleton_inj.1 h).symm
      · simp only [vEnd, hy] at h
        exact d2 (singleton_inj.1 h).symm
    have hcapE : ∀ (r : Role) (E : W → Bool),
        ∃ y : Option W, vEnd three r E (.inr y : Inp Z W) ≠ WinnerSet.singleton (three 0) :=
      fun r E => ⟨none, fun h => h01 (singleton_inj.1 h).symm⟩
    have kX : q.eval (fun y => Bichain.Value.ofBool (endP X y)) = .c := by
      have h := (key (vEnd three (three 2) X) (hforE _ X) (hcapE _ X)).2.1
        (baseline_X three rows X Y z₀)
      have e : (fun y => see three (three 0) (vEnd three (three 2) X (.inr y : Inp Z W))) =
          fun y => Bichain.Value.ofBool (endP X y) := funext (hsee _ X)
      rwa [e] at h
    have kY : q.eval (fun y => Bichain.Value.ofBool (endP Y y)) = .b := by
      have h := (key (vEnd three (three 1) Y) (hforE _ Y) (hcapE _ Y)).1
        (baseline_Y three rows X Y z₀)
      have e : (fun y => see three (three 0) (vEnd three (three 1) Y (.inr y : Inp Z W))) =
          fun y => Bichain.Value.ofBool (endP Y y) := funext (hsee _ Y)
      rwa [e] at h
    cases hd : PureTerm.dropNone q with
    | none =>
      have h := (PureTerm.dropNone_spec (fun y => Bichain.Value.ofBool (endP X y)) rfl q hq).1 hd
      rw [kX] at h
      cases h
    | some p =>
      have hp := fun ν hν => (PureTerm.dropNone_spec ν hν q hq).2 p hd
      refine ⟨p, (hp _ (rfl : rowP rows z₀ none = .b)).1, fun z => ?_, ?_, ?_⟩
      · have h := (hp (rowP rows z) rfl).2
        change p.eval (rows z) = _ at h
        rw [h]
        exact krow z
      · have h := (hp (fun y => Bichain.Value.ofBool (endP X y)) rfl).2
        change p.eval (fun j => Bichain.Value.ofBool (X j)) = _ at h
        rw [h]
        exact kX
      · have h := (hp (fun y => Bichain.Value.ofBool (endP Y y)) rfl).2
        change p.eval (fun j => Bichain.Value.ofBool (Y j)) = _ at h
        rw [h]
        exact kY
  · rintro ⟨p, hp, hrow, hX, hY⟩
    refine ⟨.choice (three 0) (baseline three rows X Y z₀) (word three p),
      ⟨baseline_isCore three rows X Y z₀, fromPure_isCore three _ _⟩, fun v => ?_⟩
    have hcap := word_cap three (Z := Z) p v
    change choice (three 0) ((baseline three rows X Y z₀).eval v) ((word three p).eval v) = _
    unfold target
    split_ifs with hall
    · rw [hcap.2 hall]
      exact choice_right_owner _
    · by_cases hB : (baseline three rows X Y z₀).eval v = WinnerSet.singleton (three 0)
      · rw [hB]
        exact choice_left_owner _
      · have hG : (word three p : Term Role (Inp Z W)).eval v ≠ WinnerSet.singleton (three 0) :=
          fun h => hall (hcap.1 h)
        apply Subtype.ext
        apply Set.Subset.antisymm
        · exact choice_sub Set.Subset.rfl
            fun k hk => word_le_baseline three rows X Y z₀ p hp hrow hX hY v k hk
        · intro k hk
          exact mem_choice_left hk hG

end Main

end KFOL.Recognition
