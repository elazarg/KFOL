module

public import KFOL.Complexity.TablePeelingGame
public import KFOL.Complexity.TablePeelingFrontend
public import KFOL.Core.ExactSplit

/-! # Local checks for the bounded exact-split game

Each child is a bit matrix with one column per role. An empty row permits
all menus; any other row prescribes precisely the listed winners.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingMasks

open AddressedEnvelope FullSparseEvaluation TablePeelingGame TablePeeling
open Turing.MultiTapeTM ComputableInPolyTime

def ownerId (K : ℕ) (cur : Move) : ℕ := ((List.range K).filter fun k => cur.1.getD k false).headD 0

theorem owner_lt {K : ℕ} (hK : 0 < K) (cur : Move) : ownerId K cur < K := by
  unfold ownerId
  cases h : (List.range K).filter (fun k => cur.1.getD k false) with
  | nil => exact hK
  | cons a rest =>
    have found : a ∈ (List.range K).filter (fun k => cur.1.getD k false) := h ▸ List.mem_cons_self
    exact List.mem_range.mp (List.mem_filter.mp found).1

def childBit (K : ℕ) (cur : Move) (side : Bool) (i k : ℕ) : Bool :=
  cur.1.getD (K + 2*(i*K+k) + side.toNat) false

def goalBit (K : ℕ) (x : TablePeeling.Input) (prev : Previous) (i k : ℕ) : Bool :=
  prev.elim (member k (x.2.getD i ([],[])).2) (fun m => childBit K m (m.2.getD 0 false) i k)

def toGoal (K n : ℕ) (bit : ℕ → ℕ → Bool) : Core.ExactSplit.Goal (Fin n) (Fin K) :=
  Finset.univ.filter fun pair => bit pair.1.val pair.2.val

/-- All nonempty role lists in increasing order, without duplicates. -/
def allMenus (K : ℕ) : List Names := ((List.range K).sublists).filter (fun m => !m.isEmpty)

def fits (K : ℕ) (bit : ℕ → Bool) (v : Names) : Bool :=
  !(List.range K).any bit || (List.range K).all fun r => decide (bit r = member r v)

def gate (K : ℕ) (x : TablePeeling.Input) (prev : Previous) (cur : Move) : Bool :=
  (List.range x.2.length).all fun i =>
    (allMenus K).all fun a => (allMenus K).all fun b =>
      !(fits K (childBit K cur false i) a && fits K (childBit K cur true i) b) ||
        fits K (goalBit K x prev i) (FullSparseEvaluation.choice (ownerId K cur) a b)

def normalize (K : ℕ) (xs : Names) : Names :=
  let ys := (List.range K).filter fun r => member r xs
  if ys.isEmpty then List.range K else ys

def endTest (K : ℕ) (x : TablePeeling.Input) (prev : Previous) : Bool :=
  (List.range x.1).any fun j => (List.range x.2.length).all fun i =>
    fits K (goalBit K x prev i) (normalize K ((x.2.getD i ([],[])).1.getD j []))

theorem mem_toGoal {K n : ℕ} (bit : ℕ → ℕ → Bool) (q : Fin n) (r : Fin K) :
    r ∈ Core.ExactSplit.fiber (toGoal K n bit) q ↔ bit q.val r.val = true := by
  simp [Core.ExactSplit.fiber,toGoal]

theorem fits_iff {K n : ℕ} (bit : ℕ → ℕ → Bool) (i : Fin n) {xs : Names}
    {v : WinnerSet (Fin K)} (rep : Represents xs v) :
    fits K (bit i.val) xs = true ↔ Core.ExactSplit.Match (toGoal K n bit) i v := by
  have nonempty : (List.range K).any (bit i.val) = true ↔
      (Core.ExactSplit.fiber (toGoal K n bit) i).Nonempty := by
    simp only [List.any_eq_true,List.mem_range,Set.Nonempty]
    exact ⟨fun ⟨r,hr,hit⟩ => ⟨⟨r,hr⟩,(mem_toGoal bit i _).mpr hit⟩,
      fun ⟨r,h⟩ => ⟨r.val,r.isLt,(mem_toGoal bit i _).mp h⟩⟩
  have exactRow : (List.range K).all (fun r => decide (bit i.val r = member r xs)) = true ↔
      v.val = Core.ExactSplit.fiber (toGoal K n bit) i := by
    simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq]
    constructor
    · intro same
      ext r
      rw [mem_toGoal, same r.val r.isLt,member_iff]
      exact (AddressedPoint.represents_mem rep r).symm
    · intro eq r hr
      apply Bool.eq_iff_iff.mpr
      have h := mem_toGoal bit i (⟨r,hr⟩ : Fin K)
      rw [← eq] at h
      exact h.symm.trans ((AddressedPoint.represents_mem rep ⟨r,hr⟩).symm.trans (member_iff r xs).symm)
  change _ ↔ ((Core.ExactSplit.fiber (toGoal K n bit) i).Nonempty → _)
  simp only [fits,Bool.or_eq_true, Bool.not_eq_true',Bool.eq_false_iff]
  exact (or_congr (not_congr nonempty) exactRow).trans (by tauto)

private theorem allMenus_sound {K : ℕ} {m : Names} (good : m ∈ allMenus K) :
    ∃ v : WinnerSet (Fin K), Represents m v := by
  obtain ⟨sub, some⟩ := List.mem_filter.mp good
  have below := List.mem_sublists.mp sub
  have present : ∃ j, j ∈ m := by cases m <;> simp_all
  obtain ⟨j,hj⟩ := present
  let valid (r : ℕ) (hr : r ∈ m) := List.mem_range.mp (below.subset hr)
  let v : WinnerSet (Fin K) := ⟨{t | t.val ∈ m},⟨⟨j,valid j hj⟩,hj⟩⟩
  exact ⟨v,AddressedPoint.represents_ext valid (fun _ => Iff.rfl)⟩

private theorem allMenus_complete {K : ℕ} (v : WinnerSet (Fin K)) :
    ∃ m ∈ allMenus K, Represents m v := by
  classical
  let m := (List.range K).filter (fun r => decide (∃ s : Fin K, s ∈ v.val ∧ s.val = r))
  have mem (s : Fin K) : s.val ∈ m ↔ s ∈ v.val := by
    simp only [m,List.mem_filter,List.mem_range,s.isLt,true_and,decide_eq_true_eq]
    exact ⟨fun ⟨t,ht,eq⟩ => Fin.ext eq ▸ ht, fun h => ⟨s,h,rfl⟩⟩
  obtain ⟨r,hr⟩ := v.property
  have nn : m ≠ [] := fun eq => by simpa [eq] using (mem r).mpr hr
  have sub : m.Sublist (List.range K) := List.filter_sublist
  exact ⟨m,List.mem_filter.mpr ⟨List.mem_sublists.mpr sub,by simpa using nn⟩,
    AddressedPoint.represents_ext (fun i h => List.mem_range.mp (List.mem_filter.mp h).1) mem⟩

theorem gate_iff {K : ℕ} (hK : 0 < K) (x : TablePeeling.Input) (prev : Previous) (cur : Move) :
    gate K x prev cur = true ↔ Core.ExactSplit.Compatible (⟨ownerId K cur,owner_lt hK cur⟩ : Fin K)
      (toGoal K x.2.length (goalBit K x prev)) (toGoal K x.2.length (childBit K cur false))
      (toGoal K x.2.length (childBit K cur true)) := by
  let owner : Fin K := ⟨ownerId K cur,owner_lt hK cur⟩
  simp only [gate,List.all_eq_true,List.mem_range,Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff]
  constructor
  · intro ok i X Y left right
    obtain ⟨a,ha,repA⟩ := allMenus_complete X
    obtain ⟨b,hb,repB⟩ := allMenus_complete Y
    exact (fits_iff _ i (represents_choice owner repA repB)).mp
      ((ok i.val i.isLt a ha b hb).resolve_left (not_not.mpr ((Bool.and_eq_true _ _).mpr
        ⟨(fits_iff _ i repA).mpr left,(fits_iff _ i repB).mpr right⟩)))
  · intro ok i hi a ha b hb
    obtain ⟨X,repA⟩ := allMenus_sound ha
    obtain ⟨Y,repB⟩ := allMenus_sound hb
    by_cases hit : fits K (childBit K cur false i) a && fits K (childBit K cur true i) b
    · obtain ⟨left,right⟩ := (Bool.and_eq_true _ _).mp hit
      let q : Fin x.2.length := ⟨i,hi⟩
      exact Or.inr ((fits_iff _ q (represents_choice owner repA repB)).mpr
        (ok q X Y ((fits_iff _ q repA).mp left) ((fits_iff _ q repB).mp right)))
    · exact Or.inl hit

private theorem normalize_rep {K : ℕ} (hK : 0 < K) (xs : Names) :
    Represents (normalize K xs) (TablePeeling.readMenu hK xs) := by
  classical
  let ys := (List.range K).filter (fun r => member r xs)
  have listed (r : Fin K) : r.val ∈ ys ↔ r.val ∈ xs := by simp [ys, r.isLt]
  by_cases yes : (TablePeeling.allowed xs : Set (Fin K)).Nonempty
  · obtain ⟨r,hr⟩ := yes
    have nn : ys ≠ [] := fun eq => by simpa [eq] using (listed r).mpr hr
    have eq : normalize K xs = ys := by
      change (if ys.isEmpty then List.range K else ys) = ys
      simp [nn]
    rw [eq,TablePeeling.readMenu,dite_eq_left ⟨r,hr⟩]
    exact AddressedPoint.represents_ext (fun j hj => List.mem_range.mp (List.mem_filter.mp hj).1) listed
  · have zero : ys = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      have bound := List.mem_range.mp (List.mem_filter.mp hj).1
      exact yes ⟨⟨j,bound⟩,(listed ⟨j,bound⟩).mp hj⟩
    have eq : normalize K xs = List.range K := by
      change (if ys.isEmpty then List.range K else ys) = List.range K
      rw [zero]; rfl
    rw [eq,TablePeeling.readMenu,dite_eq_right yes]
    exact AddressedPoint.represents_ext (fun _ => List.mem_range.mp) (fun r => by simp [r.isLt])

theorem endTest_iff {K : ℕ} (hK : 0 < K) (x : TablePeeling.Input) (prev : Previous) :
    endTest K x prev = true ↔ Core.ExactSplit.Projection (TablePeeling.values hK x)
      (toGoal K x.2.length (goalBit K x prev)) := by
  simp only [endTest,List.any_eq_true,List.all_eq_true,List.mem_range]
  have atRow (j : Fin x.1) (i : Fin x.2.length) :
      Represents (normalize K ((x.2.getD i.val ([],[])).1.getD j.val [])) (TablePeeling.values hK x i j) := by
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact normalize_rep hK _
  exact ⟨fun ⟨j,hj,ok⟩ => ⟨⟨j,hj⟩,fun q => (fits_iff _ q (atRow _ q)).mp (ok q.val q.isLt)⟩,
    fun ⟨j,ok⟩ => ⟨j.val,j.isLt,fun i hi => (fits_iff _ ⟨i,hi⟩ (atRow j ⟨i,hi⟩)).mpr (ok _)⟩⟩

end KFOL.Complexity.TablePeelingMasks
