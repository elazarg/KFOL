module

public import KFOL.Definitions.GrayCrown
public import KFOL.Definitions.CrownFrame
public import Mathlib.Tactic

/-! # Gray cycles and their paired-transversal crowns

All incidence facts follow from the single-coordinate adjacency of two
Boolean words. The reflected enumeration supplies such a cycle in every
positive dimension.
-/

@[expose] public section
namespace KFOL.Core.GrayCrown

variable {d : ℕ}

@[simp] theorem mem_lowerOf (x : Word d) (j : Fin d) (b : Bool) :
    (j,b) ∈ lowerOf x ↔ b = x j := by
  simp [lowerOf, Prod.mk.injEq, eq_comm]

@[simp] theorem mem_upperOf (x y : Word d) (j : Fin d) (b : Bool) :
    (j,b) ∈ upperOf x y ↔ b = x j ∨ b = y j := by
  simp [upperOf]

theorem lowerOf_injective : Function.Injective (@lowerOf d) := by
  intro x y h
  funext j
  have hh : (j,x j) ∈ lowerOf y := h ▸ (mem_lowerOf x j (x j)).mpr rfl
  exact ((mem_lowerOf y j (x j)).mp hh)

theorem adjacent_symm {x y : Word d} (h : Adjacent x y) : Adjacent y x := by
  obtain ⟨j,hj,h⟩ := h
  exact ⟨j, Ne.symm hj, fun k hk => (h k hk).symm⟩

theorem lower_subset_upper_iff {x y z : Word d} (h : Adjacent x y) :
    lowerOf z ⊆ upperOf x y ↔ z = x ∨ z = y := by
  obtain ⟨j,hj,hxy⟩ := h
  constructor
  · intro hz
    have hzbit (k : Fin d) : z k = x k ∨ z k = y k :=
      (mem_upperOf x y k (z k)).mp (hz ((mem_lowerOf z k (z k)).mpr rfl))
    rcases hzbit j with hzx | hzy
    · left
      funext k
      by_cases hk : k = j
      · simpa [hk] using hzx
      · rcases hzbit k with hx | hy
        · exact hx
        · exact hy.trans (hxy k hk).symm
    · right
      funext k
      by_cases hk : k = j
      · simpa [hk] using hzy
      · rcases hzbit k with hx | hy
        · exact hx.trans (hxy k hk)
        · exact hy
  · rintro (rfl | rfl) <;> simp [upperOf]

theorem upper_diff_lower {x y : Word d} (h : Adjacent x y) :
    ∃ j : Fin d, upperOf x y \ lowerOf x = {(j,y j)} := by
  obtain ⟨j,hj,hxy⟩ := h
  refine ⟨j, ?_⟩
  ext ⟨k,b⟩
  by_cases hk : k = j
  · subst k
    simp only [Finset.mem_sdiff, mem_upperOf, mem_lowerOf, Finset.mem_singleton,
      Prod.mk.injEq, true_and]
    aesop
  · have he := hxy k hk
    simp [he, hk]

theorem lowerOf_nonempty (hd : 0 < d) (x : Word d) : (lowerOf x).Nonempty := by
  exact ⟨(⟨0,hd⟩,x ⟨0,hd⟩), (mem_lowerOf _ _ _).mpr rfl⟩

theorem upperOf_ne_univ (hd : 2 ≤ d) {x y : Word d} (h : Adjacent x y) :
    upperOf x y ≠ Finset.univ := by
  obtain ⟨j,hj,hxy⟩ := h
  let k : Fin d := if j.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hkj : k ≠ j := by
    dsimp [k]
    split_ifs with hz
    · intro he
      have hh := congrArg Fin.val he
      change 1 = j.val at hh
      omega
    · intro he
      have hh := congrArg Fin.val he
      change 0 = j.val at hh
      omega
  intro he
  have hm : (k,!(x k)) ∈ upperOf x y := he ▸ Finset.mem_univ _
  have hxyk := hxy k hkj
  simp [hxyk] at hm

private theorem adjacent_cons {x y : Word d} (b : Bool) (h : Adjacent x y) :
    Adjacent (Fin.cons b x) (Fin.cons b y) := by
  obtain ⟨j,hj,hxy⟩ := h
  refine ⟨j.succ, by simpa using hj, ?_⟩
  intro k
  refine Fin.cases (by intro; rfl) (fun a hk => ?_) k
  exact hxy a (fun he => hk (by simp [he]))

private theorem adjacent_cons_flip (b : Bool) (x : Word d) :
    Adjacent (Fin.cons b x) (Fin.cons (!b) x) := by
  refine ⟨0, by simp, ?_⟩
  intro k
  refine Fin.cases (fun hk => (hk rfl).elim) (fun _ _ => rfl) k

@[simp] theorem reflected_length (d : ℕ) : (reflected d).length = 2 ^ d := by
  induction d with
  | zero => simp [reflected]
  | succ d ih => simp [reflected, ih, pow_succ, Nat.mul_two]

theorem reflected_ne_nil (d : ℕ) : reflected d ≠ [] := by
  have hp : 0 < 2 ^ d := by positivity
  exact List.length_pos_iff_ne_nil.mp (by simpa only [reflected_length] using hp)

theorem reflected_nodup (d : ℕ) : (reflected d).Nodup := by
  induction d with
  | zero => simp [reflected]
  | succ d ih =>
    rw [reflected, List.nodup_append]
    have hinj (b : Bool) : Function.Injective (fun x : Word d => (Fin.cons b x : Word (d+1))) := by
      intro x y h
      funext j
      exact congrFun h j.succ
    refine ⟨ih.map (hinj false), (List.nodup_reverse.mpr ih).map (hinj true), ?_⟩
    intro x hx y hy he
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    have hh := congrFun he 0
    simp at hh

theorem reflected_complete (d : ℕ) (x : Word d) : x ∈ reflected d := by
  induction d with
  | zero =>
    have hx : x = Fin.elim0 := by funext j; exact j.elim0
    simp [reflected, hx]
  | succ d ih =>
    have ht := ih (Fin.tail x)
    have he := Fin.cons_self_tail x
    rw [reflected, List.mem_append]
    cases hb : x 0
    · left
      exact List.mem_map.mpr ⟨Fin.tail x, ht, by simpa [hb] using he⟩
    · right
      exact List.mem_map.mpr ⟨Fin.tail x, List.mem_reverse.mpr ht,
        by simpa [hb] using he⟩

theorem reflected_chain (d : ℕ) : (reflected d).IsChain Adjacent := by
  induction d with
  | zero => simp [reflected]
  | succ d ih =>
    rw [reflected]
    refine (List.isChain_map_of_isChain (R := @Adjacent d) (S := @Adjacent (d+1))
      (fun x : Word d => (Fin.cons false x : Word (d+1)))
      (fun _ _ h => adjacent_cons false h) ih).append ?_ ?_
    · apply List.isChain_map_of_isChain (R := @Adjacent d) (S := @Adjacent (d+1))
        (fun x : Word d => (Fin.cons true x : Word (d+1)))
        (fun _ _ h => adjacent_cons true h)
      exact List.isChain_reverse.mpr (ih.imp fun _ _ h => adjacent_symm h)
    · intro x hx y hy
      simp only [List.getLast?_map, List.head?_map, List.head?_reverse] at hx hy
      cases he : (reflected d).getLast? with
      | none => simp [he] at hx
      | some z =>
        simp [he] at hx hy
        subst x y
        exact adjacent_cons_flip false z

@[simp] theorem reflected_head (d : ℕ) :
    (reflected d).head? = some (fun _ => false) := by
  induction d with
  | zero =>
    simp only [reflected, List.head?_cons, Option.some.injEq]
    funext j
    exact j.elim0
  | succ d ih =>
    simp only [reflected, List.head?_append, List.head?_map, ih, Option.map_some,
      Option.some_or]
    congr 1
    funext j
    refine Fin.cases rfl (fun _ => rfl) j

@[simp] theorem reflected_last (d : ℕ) :
    (reflected (d+1)).getLast? = some (Fin.cons true (fun _ => false)) := by
  simp [reflected, List.getLast?_append, List.getLast?_map, List.getLast?_reverse]

theorem reflected_wrap (d : ℕ) :
    ∀ x ∈ (reflected (d+1)).getLast?, ∀ y ∈ (reflected (d+1)).head?, Adjacent x y := by
  intro x hx y hy
  simp only [reflected_last, Option.mem_some_iff] at hx
  simp only [reflected_head, Option.mem_some_iff] at hy
  subst x y
  convert adjacent_cons_flip true (fun _ : Fin d => false) using 1
  funext j
  refine Fin.cases rfl (fun _ => rfl) j

theorem cyclic_get {α : Type*} {R : α → α → Prop} (l : List α)
    (hc : l.IsChain R)
    (hw : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y)
    (i : Fin l.length) : R (l.get i) (l.get (finRotate _ i)) := by
  cases l with
  | nil => exact i.elim0
  | cons a l =>
    by_cases hi : i = Fin.last l.length
    · subst i
      have hr : finRotate (a :: l).length (Fin.last l.length) = 0 := finRotate_last
      rw [hr]
      have hne : a :: l ≠ [] := by simp
      have hh := hw ((a :: l).getLast hne)
        (by simp [List.getLast?_eq_some_getLast hne])
        ((a :: l).head hne) (by simp [List.head?_eq_some_head hne])
      simpa [List.get_eq_getElem, List.getLast_eq_getElem,
        List.head_eq_getElem] using hh
    · have hlt : i.val < l.length := Fin.val_lt_last hi
      have hr : ((finRotate (a :: l).length i) : ℕ) = i.val + 1 :=
        coe_finRotate_of_ne_last hi
      have hh := List.isChain_iff_getElem.mp hc i.val (by simpa using Nat.succ_lt_succ hlt)
      simpa only [List.get_eq_getElem, hr] using hh

theorem finCongr_rotate {m n : ℕ} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst n
  rfl

/-- The reflected construction supplies a genuine complete cyclic Gray code. -/
def reflectedCode (d : ℕ) : Code (d+1) := by
  let l := reflected (d+1)
  let e : Fin (2 ^ (d+1)) ≃ Fin l.length := finCongr (reflected_length (d+1)).symm
  refine ⟨fun i => l.get (e i), ?_, ?_⟩
  · constructor
    · intro i j h
      exact e.injective ((reflected_nodup (d+1)).get_inj_iff.mp h)
    · intro x
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (reflected_complete (d+1) x)
      exact ⟨e.symm i, by simpa using hi⟩
  · intro i
    have hh := cyclic_get l (reflected_chain (d+1)) (reflected_wrap d) (e i)
    have he : e (finRotate (2 ^ (d+1)) i) = finRotate l.length (e i) :=
      finCongr_rotate (reflected_length (d+1)).symm i
    rw [he]
    exact hh

theorem exists_code (hd : 0 < d) : Nonempty (Code d) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact ⟨reflectedCode n⟩

theorem lowerOf_covBy_upperOf {x y : Word d} (h : Adjacent x y) :
    lowerOf x ⋖ upperOf x y := by
  apply Finset.covBy_iff_card_sdiff_eq_one.mpr
  obtain ⟨j,hj⟩ := upper_diff_lower h
  exact ⟨Finset.subset_union_left, by simp [hj]⟩

namespace Code

variable (g : Code d)

theorem lower_injective : Function.Injective g.lower := by
  intro i j h
  exact g.bijective.1 (lowerOf_injective h)

theorem incidence (i j : Fin (2 ^ d)) :
    g.lower j ⊆ g.upper i ↔ j = i ∨ j = finRotate _ i := by
  simpa only [lower, upper, g.bijective.1.eq_iff] using
    (lower_subset_upper_iff (z := g.word j) (g.adjacent i))

theorem lower_nonempty (hd : 0 < d) (i : Fin (2 ^ d)) : (g.lower i).Nonempty :=
  lowerOf_nonempty hd _

theorem upper_ne_univ (hd : 2 ≤ d) (i : Fin (2 ^ d)) :
    g.upper i ≠ Finset.univ := upperOf_ne_univ hd (g.adjacent i)

theorem upper_diff_lower_singleton (i : Fin (2 ^ d)) :
    ∃ j : Fin d, g.upper i \ g.lower i = {(j,g.word (finRotate _ i) j)} :=
  upper_diff_lower (g.adjacent i)

theorem cover (i : Fin (2 ^ d)) : g.lower i ⋖ g.upper i :=
  lowerOf_covBy_upperOf (g.adjacent i)

/-- The paired transversals of a Gray code form a cyclic cover crown. -/
def frame (hd : 2 ≤ d) : IntervalCrown.Frame (Fin d × Bool) (2 ^ d) where
  lower := g.lower
  upper := g.upper
  lower_nonempty := g.lower_nonempty (by omega)
  upper_ne_univ := g.upper_ne_univ hd
  cover := g.cover
  incidence := g.incidence


end Code

/-- A concrete paired-variable frame in every dimension at least two. -/
def pairedFrame (d : ℕ) : IntervalCrown.Frame (Fin (d+2) × Bool) (2 ^ (d+2)) :=
  (reflectedCode (d+1)).frame (by omega)

theorem exists_frame (hd : 2 ≤ d) :
    Nonempty (IntervalCrown.Frame (Fin d × Bool) (2 ^ d)) := by
  obtain ⟨g⟩ := exists_code (by omega : 0 < d)
  exact ⟨g.frame hd⟩

end KFOL.Core.GrayCrown
