module

public import KFOL.Core.BichainReadOnce
public import Mathlib.Data.Finset.Card

/-! # Obstructions to marking a cube or separating Boolean endpoints

A cut uses only the coordinates and endpoints of the given rows. The same
proof allows any number of marked coordinates on each row, including zero.
-/

@[expose] public section
namespace KFOL.Bichain

variable {Var Row : Type*} [DecidableEq Row]

private def Fits (rows : Row → Var → Value) (S : Finset Row) (q : CubeQuery Var) : Prop :=
  ∃ t : Term Var, t.IsPure ∧ (∀ z ∈ S, t.eval (rows z) ≠ .possible) ∧ q.Holds t

private theorem lower_c_iff (t : Term Var) (ht : t.IsPure) (w : Var → Value) :
    t.eval (fun j => Value.ofBool (cubeLower w j)) = .c ↔ t.eval w = .c := by
  rw [t.pure_eval_cubeLower ht]
  cases t.eval w <;> decide

private theorem upper_b_iff (t : Term Var) (ht : t.IsPure) (w : Var → Value) :
    t.eval (fun j => Value.ofBool (cubeUpper w j)) = .b ↔ t.eval w = .b := by
  rw [t.pure_eval_cubeUpper ht]
  cases t.eval w <;> decide

private theorem endpoints {q : CubeQuery Var} {t : Term Var} (ht : t.IsPure) (h : q.Holds t) :
    (CubeQuery.separate q.pos q.neg).Holds t := by
  cases q with
  | separate => exact h
  | mark w =>
    change t.eval w = .possible at h
    change t.eval (fun j => Value.ofBool (cubeUpper w j)) = .c ∧
      t.eval (fun j => Value.ofBool (cubeLower w j)) = .b
    rw [t.pure_eval_cubeUpper ht, t.pure_eval_cubeLower ht, h]
    exact ⟨rfl, rfl⟩

private theorem fits_var (q : CubeQuery Var) (j : Var) :
    q.Holds (.var j) ↔ q.Eligible j := by
  cases q with
  | mark => rfl
  | separate p n =>
    change (Value.ofBool (p j) = .c ∧ Value.ofBool (n j) = .b) ↔
      (p j = true ∧ n j = false)
    cases p j <;> cases n j <;> decide

private theorem inf_stable : ∀ x y : Value,
    (Value.inf x y = .b ↔ x = .b ∨ y = .b) ∧
    (Value.inf x y = .c ↔ x = .c ∧ y = .c) := by decide +kernel
private theorem sup_stable : ∀ x y : Value,
    (Value.sup x y = .c ↔ x = .c ∨ y = .c) ∧
    (Value.sup x y = .b ↔ x = .b ∧ y = .b) := by decide +kernel

private theorem child_inf (q : CubeQuery Var) (t u : Term Var) :
    q.Holds (.inf t u) → q.Holds t ∨ q.Holds u := by
  cases q with
  | mark w =>
    exact (by decide +kernel : ∀ x y : Value, Value.inf x y = .possible →
      x = .possible ∨ y = .possible) (t.eval w) (u.eval w)
  | separate p n =>
    rintro ⟨hp, hn⟩
    obtain ⟨hpt, hpu⟩ := (inf_stable _ _).2.mp hp
    exact ((inf_stable _ _).1.mp hn).elim (fun h => Or.inl ⟨hpt, h⟩) (fun h => Or.inr ⟨hpu, h⟩)

private theorem child_sup (q : CubeQuery Var) (t u : Term Var) :
    q.Holds (.sup t u) → q.Holds t ∨ q.Holds u := by
  cases q with
  | mark w =>
    exact (by decide +kernel : ∀ x y : Value, Value.sup x y = .possible →
      x = .possible ∨ y = .possible) (t.eval w) (u.eval w)
  | separate p n =>
    rintro ⟨hp, hn⟩
    obtain ⟨hnt, hnu⟩ := (sup_stable _ _).2.mp hn
    exact ((sup_stable _ _).1.mp hp).elim (fun h => Or.inl ⟨h, hnt⟩) (fun h => Or.inr ⟨h, hnu⟩)

private theorem extend_sup {q : CubeQuery Var} {t u : Term Var} (hu : u.IsPure) (ht : q.Holds t)
    (hn : u.eval (fun j => Value.ofBool (q.neg j)) = .b) : q.Holds (.sup t u) := by
  cases q with
  | separate => exact ⟨(sup_stable _ _).1.mpr (Or.inl ht.1), (sup_stable _ _).2.mpr ⟨ht.2, hn⟩⟩
  | mark w =>
    have hnc : u.eval w ≠ .c := fun hc => Value.noConfusion (hn.symm.trans ((lower_c_iff u hu w).mpr hc))
    change Value.sup (t.eval w) (u.eval w) = .possible
    change t.eval w = .possible at ht
    rw [ht]
    exact (by decide +kernel : ∀ y : Value, y ≠ .c → Value.sup .possible y = .possible) _ hnc

private theorem extend_inf {q : CubeQuery Var} {t u : Term Var} (hu : u.IsPure) (ht : q.Holds t)
    (hp : u.eval (fun j => Value.ofBool (q.pos j)) = .c) : q.Holds (.inf t u) := by
  cases q with
  | separate => exact ⟨(inf_stable _ _).2.mpr ⟨ht.1, hp⟩, (inf_stable _ _).1.mpr (Or.inl ht.2)⟩
  | mark w =>
    have hnb : u.eval w ≠ .b := fun hb => Value.noConfusion (hp.symm.trans ((upper_b_iff u hu w).mpr hb))
    change Value.inf (t.eval w) (u.eval w) = .possible
    change t.eval w = .possible at ht
    rw [ht]
    exact (by decide +kernel : ∀ y : Value, y ≠ .b → Value.inf .possible y = .possible) _ hnb

private theorem impossible_of_faces (rows : Row → Var → Value) (S : Finset Row) (q : CubeQuery Var)
    (cover : ∀ j, q.Eligible j → ∃ z ∈ S, rows z j = .possible)
    (left : ∀ z ∈ S, ¬ Fits rows (S.erase z) (.separate (cubeLower (rows z)) q.neg))
    (right : ∀ z ∈ S, ¬ Fits rows (S.erase z) (.separate q.pos (cubeUpper (rows z)))) :
    ¬ Fits rows S q := by
  rintro ⟨t, ht, hs, hq⟩
  have interior (t : Term Var) (ht : t.IsPure) (hs : ∀ z ∈ S, t.eval (rows z) ≠ .possible)
      (hq : q.Holds t) (z : Row) (hz : z ∈ S) : t.eval (rows z) ≠ .c ∧ t.eval (rows z) ≠ .b := by
    have he := endpoints ht hq
    have hr : ∀ y ∈ S.erase z, t.eval (rows y) ≠ .possible :=
      fun y hy => hs y (Finset.mem_of_mem_erase hy)
    exact ⟨fun hc => left z hz ⟨t, ht, hr, (lower_c_iff t ht _).mpr hc, he.2⟩,
      fun hb => right z hz ⟨t, ht, hr, he.1, (upper_b_iff t ht _).mpr hb⟩⟩
  induction t with
  | var j =>
    obtain ⟨z, hz, he⟩ := cover j ((fits_var q j).mp hq)
    exact hs z hz he
  | inf t u iht ihu =>
    have h (z : Row) (hz : z ∈ S) : t.eval (rows z) ≠ .possible ∧ u.eval (rows z) ≠ .possible :=
      (by decide +kernel : ∀ x y : Value, Value.inf x y ≠ .possible → Value.inf x y ≠ .b →
        x ≠ .possible ∧ y ≠ .possible) _ _ (hs z hz) (interior _ ht hs hq z hz).2
    exact (child_inf q t u hq).elim (iht ht.1 (fun z hz => (h z hz).1))
      (ihu ht.2 (fun z hz => (h z hz).2))
  | sup t u iht ihu =>
    have h (z : Row) (hz : z ∈ S) : t.eval (rows z) ≠ .possible ∧ u.eval (rows z) ≠ .possible :=
      (by decide +kernel : ∀ x y : Value, Value.sup x y ≠ .possible → Value.sup x y ≠ .c →
        x ≠ .possible ∧ y ≠ .possible) _ _ (hs z hz) (interior _ ht hs hq z hz).1
    exact (child_sup q t u hq).elim (iht ht.1 (fun z hz => (h z hz).1))
      (ihu ht.2 (fun z hz => (h z hz).2))
  | union => exact ht.elim

private theorem cut_of_impossible (rows : Row → Var → Value) (S : Finset Row) (q : CubeQuery Var) :
    ¬ Fits rows S q → CubeCut rows S q := by
  classical
  induction S using Finset.strongInductionOn generalizing q with
  | _ S ih =>
    intro hf
    by_cases redundant : ∃ z ∈ S, ¬ Fits rows (S.erase z) q
    · obtain ⟨z, hz, hf'⟩ := redundant
      obtain ⟨hsub, hcover, hl, hr⟩ := ih _ (Finset.erase_ssubset hz) q hf'
      exact .cover (hsub.trans (Finset.erase_subset _ _)) hcover hl hr
    push Not at redundant
    apply CubeCut.cover (Finset.Subset.refl S)
    · intro j hj
      by_contra! h
      exact hf ⟨.var j, trivial, h, (fits_var q j).mpr hj⟩
    · intro z hz
      apply ih _ (Finset.erase_ssubset hz)
      rintro ⟨u, hu, hsafe, hp, hn⟩
      obtain ⟨t, ht, hquiet, hq⟩ := redundant z hz
      apply hf
      refine ⟨.sup t u, ⟨ht, hu⟩, ?_, extend_sup hu hq hn⟩
      intro y hy
      by_cases he : y = z
      · subst y
        exact fun h => Value.noConfusion (h.symm.trans
          ((sup_stable _ _).1.mpr (Or.inr ((lower_c_iff u hu _).mp hp))))
      · have hm := Finset.mem_erase.mpr ⟨he, hy⟩
        exact (by decide +kernel : ∀ x y : Value, x ≠ .possible → y ≠ .possible →
          Value.sup x y ≠ .possible) _ _ (hquiet y hm) (hsafe y hm)
    · intro z hz
      apply ih _ (Finset.erase_ssubset hz)
      rintro ⟨u, hu, hsafe, hp, hn⟩
      obtain ⟨t, ht, hquiet, hq⟩ := redundant z hz
      apply hf
      refine ⟨.inf t u, ⟨ht, hu⟩, ?_, extend_inf hu hq hp⟩
      intro y hy
      by_cases he : y = z
      · subst y
        exact fun h => Value.noConfusion (h.symm.trans
          ((inf_stable _ _).1.mpr (Or.inr ((upper_b_iff u hu _).mp hn))))
      · have hm := Finset.mem_erase.mpr ⟨he, hy⟩
        exact (by decide +kernel : ∀ x y : Value, x ≠ .possible → y ≠ .possible →
          Value.inf x y ≠ .possible) _ _ (hquiet y hm) (hsafe y hm)

/-- A query is impossible on a finite budget precisely when the supplied rows
admit a cut. No finiteness assumption on the input coordinates is needed. -/
theorem cubeCut_iff (rows : Row → Var → Value) (S : Finset Row) (q : CubeQuery Var) :
    CubeCut rows S q ↔ ∀ t : Term Var, t.IsPure →
      (∀ z ∈ S, t.eval (rows z) ≠ .possible) → ¬ q.Holds t := by
  constructor
  · intro h
    suffices hnot : ¬ Fits rows S q from fun t ht hs hq => hnot ⟨t, ht, hs, hq⟩
    induction h with
    | cover hsub hcover _ _ ihl ihr =>
      rintro ⟨t, ht, hs, hq⟩
      exact impossible_of_faces rows _ _ hcover ihl ihr
        ⟨t, ht, fun z hz => hs z (hsub hz), hq⟩
  · intro h
    exact cut_of_impossible rows S q fun ⟨t, ht, hs, hq⟩ => h t ht hs hq

end KFOL.Bichain
