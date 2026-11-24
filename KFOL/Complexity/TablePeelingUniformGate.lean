module

public import KFOL.Complexity.TablePeelingMasks

/-! # Checking gate compatibility uniformly in the owner count -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingUniformGate

open TablePeelingGame TablePeelingMasks TablePeeling FullSparseEvaluation

def rowMenu (K : ℕ) (bits : ℕ → Bool) : List ℕ :=
  (List.range K).filter bits

def rowGate (K r : ℕ) (target left right : ℕ → Bool) : Bool :=
  let L := rowMenu K left
  let R := rowMenu K right
  (rowMenu K target).isEmpty ||
    if singletonB r L || singletonB r R then fits K target [r]
    else (!L.isEmpty && !R.isEmpty) && fits K target (L ++ R)

def gateFast (K : ℕ) (x : TablePeeling.Input) (p : Previous) (m : Move) : Bool :=
  (List.range x.2.length).all fun i =>
    rowGate K (ownerId K m) (goalBit K x p i) (childBit K m false i) (childBit K m true i)


open Core.ExactSplit
variable {K n : ℕ}

private theorem rowGate_iff (r s : Fin K) (diff : s ≠ r)
    (T L R : ℕ → ℕ → Bool) (q : Fin n) :
    rowGate K r.val (T q.val) (L q.val) (R q.val) = true ↔
      ∀ X Y, Match (toGoal K n L) q X → Match (toGoal K n R) q Y →
        Match (toGoal K n T) q (WinnerSet.choice r X Y) := by
  classical
  let F (b : ℕ → ℕ → Bool) := fiber (toGoal K n b) q
  let M (b : ℕ → ℕ → Bool) := rowMenu K (b q.val)
  let V (b : ℕ → ℕ → Bool) : WinnerSet (Fin K) :=
    if h : (F b).Nonempty then ⟨F b,h⟩ else WinnerSet.singleton s
  have present (b) : (M b).isEmpty = true ↔ ¬(F b).Nonempty := by
    rw [List.isEmpty_iff,List.eq_nil_iff_forall_not_mem]
    constructor
    · rintro none ⟨k,hk⟩
      exact none k.val (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt,(mem_toGoal b q k).mp hk⟩)
    · intro none k hk
      obtain ⟨inRange,hit⟩ := List.mem_filter.mp hk
      exact none ⟨⟨k,List.mem_range.mp inRange⟩,(mem_toGoal b q _).mpr hit⟩
  have chosen (b) : Match (toGoal K n b) q (V b) := by
    intro active
    change (if h : (F b).Nonempty then (⟨F b,h⟩ : WinnerSet (Fin K)) else _).val = F b
    rw [dite_eq_left active]
  have forced (b) (active : (F b).Nonempty) (X : WinnerSet (Fin K))
      (hx : Match (toGoal K n b) q X) : X = V b := Subtype.ext ((hx active).trans ((chosen b) active).symm)
  have rep (b) (active : (F b).Nonempty) : Represents (M b) (V b) := by
    apply AddressedPoint.represents_ext
    · intro k hk; exact List.mem_range.mp (List.mem_filter.mp hk).1
    · intro k
      rw [chosen b active,mem_toGoal]
      simp [M,rowMenu,k.isLt]
  have atom (b) : singletonB r.val (M b) = true ↔ V b = WinnerSet.singleton r := by
    by_cases active : (F b).Nonempty
    · exact singletonB_represents_iff r (rep b active)
    · have empty := List.isEmpty_iff.mp ((present b).mpr active)
      simp [empty,V,active,singletonB,WinnerSet.singleton_inj,diff]
  have need (b) (hit : V b = WinnerSet.singleton r) : (F b).Nonempty := by
    by_contra no
    simp [V,no,WinnerSet.singleton_inj,diff] at hit
  change ((M T).isEmpty || (if singletonB r.val (M L) || singletonB r.val (M R)
    then fits K (T q.val) [r.val] else (!(M L).isEmpty && !(M R).isEmpty) && fits K (T q.val) (M L ++ M R))) = true ↔ _
  by_cases target : (F T).Nonempty
  · rw [show (M T).isEmpty = false from Bool.eq_false_of_not_eq_true (fun h => (present T).mp h target),Bool.false_or]
    by_cases hit : (singletonB r.val (M L) || singletonB r.val (M R)) = true
    · rw [ite_eq_left hit,fits_iff T q (represents_singleton r)]
      have pair : V L = WinnerSet.singleton r ∨ V R = WinnerSet.singleton r :=
        (Bool.or_eq_true _ _).mp hit |>.imp (atom L).mp (atom R).mp
      have gate (X Y : WinnerSet (Fin K)) (hx : Match (toGoal K n L) q X)
          (hy : Match (toGoal K n R) q Y) : WinnerSet.choice r X Y = WinnerSet.singleton r := by
        apply (WinnerSet.choice_eq_owner_iff ..).mpr
        exact pair.imp (fun h => (forced L (need L h) X hx).trans h) (fun h => (forced R (need R h) Y hy).trans h)
      constructor
      · intro ok X Y hx hy
        rwa [gate X Y hx hy]
      · intro ok
        have h := ok (V L) (V R) (chosen L) (chosen R)
        rwa [gate _ _ (chosen L) (chosen R)] at h
    · rw [ite_eq_right hit]
      have neither : V L ≠ WinnerSet.singleton r ∧ V R ≠ WinnerSet.singleton r := by
        constructor
        · intro h; exact hit ((Bool.or_eq_true _ _).mpr (Or.inl ((atom L).mpr h)))
        · intro h; exact hit ((Bool.or_eq_true _ _).mpr (Or.inr ((atom R).mpr h)))
      have openGate : WinnerSet.choice r (V L) (V R) = (V L).union (V R) := by
        simp [WinnerSet.choice,neither.1,neither.2]
      have nonzero (b) : (M b).isEmpty ≠ true ↔ (F b).Nonempty :=
        (not_congr (present b)).trans not_not
      simp only [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff]
      rw [nonzero L,nonzero R]
      constructor
      · rintro ⟨⟨left,right⟩,ok⟩ X Y hx hy
        rw [forced L left X hx,forced R right Y hy,openGate]
        exact (fits_iff T q (represents_union (rep L left) (rep R right))).mp ok
      · intro ok
        have necessity (A B : ℕ → ℕ → Bool) (other : V B ≠ WinnerSet.singleton r)
            (h : ∀ X Y, Match (toGoal K n A) q X → Match (toGoal K n B) q Y →
              Match (toGoal K n T) q (WinnerSet.choice r X Y)) : (F A).Nonempty := by
          by_contra empty
          have free (X) : Match (toGoal K n A) q X := fun p => (empty p).elim
          have hv := h (V B) (V B) (free _) (chosen B) target
          have hr := h (WinnerSet.singleton r) (V B) (free _) (chosen B) target
          rw [WinnerSet.choice_idempotent] at hv
          simp only [WinnerSet.choice,true_or,ite_true] at hr
          exact other (Subtype.ext (hv.trans hr.symm))
        have left := necessity L R neither.2 ok
        have right := necessity R L neither.1 (fun X Y hx hy => by
          rw [WinnerSet.choice_comm]; exact ok Y X hy hx)
        refine ⟨⟨left,right⟩,(fits_iff T q (represents_union (rep L left) (rep R right))).mpr ?_⟩
        rw [← openGate]
        exact ok _ _ (chosen L) (chosen R)
  · rw [(present T).mpr target,Bool.true_or]
    exact ⟨fun _ _ _ _ _ active => (target active).elim,fun _ => rfl⟩

theorem gateFast_iff {K : ℕ} (three : Fin 3 ↪ Fin K) (x : TablePeeling.Input) (p : Previous) (m : Move) :
    gateFast K x p m = true ↔ gate K x p m = true := by
  have hk : 0 < K := Nat.zero_lt_of_lt (three 0).isLt
  let r : Fin K := ⟨ownerId K m,owner_lt hk m⟩
  obtain ⟨s,hs⟩ : ∃ s : Fin K, s ≠ r := by
    by_cases eq : three 0 = r
    · exact ⟨three 1,eq ▸ three.injective.ne (by decide : (1 : Fin 3) ≠ 0)⟩
    · exact ⟨_,eq⟩
  rw [gate_iff hk,gateFast,List.all_eq_true]
  constructor
  · intro ok q
    exact (rowGate_iff r s hs _ _ _ q).mp (ok q.val (List.mem_range.mpr q.isLt))
  · intro ok i hi
    let q : Fin x.2.length := ⟨i,List.mem_range.mp hi⟩
    exact (rowGate_iff r s hs _ _ _ q).mpr (ok q)

end KFOL.Complexity.TablePeelingUniformGate
