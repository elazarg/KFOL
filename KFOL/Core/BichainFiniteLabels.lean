module

public import KFOL.Core.BichainQuantified
import Mathlib.Data.Fintype.Prod

/-! # Finite input coordinates for the quantified cube rows -/

@[expose] public section
namespace KFOL.Bichain.Quantified

/-- The stage index, with zero for the clause marker. -/
def Lab.index : Lab → ℕ
  | .ch i _ | .rl i | .perm i _ | .lit i _ => i
  | .kap => 0

/-- Keep a representative beyond the last observable stage for each label family. -/
def Lab.limit (n : ℕ) : Lab → Lab
  | .ch i s => .ch (min i n) s
  | .rl i => .rl (min i n)
  | .perm i s => .perm (min i n) s
  | .lit i s => .lit (min i n) s
  | .kap => .kap

/-- The starting vertices and all rows are visible within the instance. -/
def Vtx.InInstance (F : Formula) : Vtx → Prop
  | .br i _ | .relay i | .res i _ => i ≤ F.n
  | .cl c => c < F.cls.length

theorem Vtx.inInstance_of_mem (F : Formula) {z : Vtx} (hz : z ∈ allRows F) :
    z.InInstance F := by
  have h := (mem_allRows F z).mp hz
  cases z <;> simp_all [InInstance, IsRow]

private theorem min_ne_of_lt {i top j : ℕ} (hi : top < i) (hj : j < top) :
    min i top ≠ j := by omega

private theorem min_beq {k top i : ℕ} (hi : i < top) : (min k top == i) = (k == i) := by
  by_cases hk : k ≤ top
  · rw [Nat.min_eq_left hk]
  · have left : (min k top == i) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => min_ne_of_lt (by omega) hi (beq_iff_eq.mp h)
    have right : (k == i) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => (show k ≠ i by omega) (beq_iff_eq.mp h)
    rw [left, right]

theorem inI_limit (F : Formula) (wf : F.WF) {z : Vtx} (hz : z.InInstance F) (j : Lab) :
    inI F z (j.limit (F.n + 2)) = inI F z j := by
  cases j with
  | lit k s =>
    cases z with
    | cl c =>
      have hcl : c < F.cls.length := hz
      simp only [Lab.limit, inI, List.getD_eq_getElem _ _ hcl]
      by_cases hk : k ≤ F.n + 2
      · rw [Nat.min_eq_left hk]
      · have bounds := wf F.cls[c] (List.getElem_mem hcl)
        have h₁ : (k, s) ∉ F.cls[c] := fun h => hk (by have := (bounds _ h).2; omega)
        have h₂ : (min k (F.n + 2), s) ∉ F.cls[c] :=
          fun h => by have := (bounds _ h).2; omega
        simp [h₁, h₂]
    | br | relay | res => rfl
  | ch k s =>
    cases z with
    | br i t =>
      have hi : i ≤ F.n := hz
      by_cases hk : k ≤ F.n + 2
      · simp [Lab.limit, inI, Nat.min_eq_left hk]
      · simp [Lab.limit, inI, min_ne_of_lt (by omega : F.n + 2 < k)
          (by omega : i + 1 < F.n + 2), show k ≠ i + 1 by omega]
    | relay | res | cl => rfl
  | rl k =>
    cases z with
    | br i t =>
      have hi : i ≤ F.n := hz
      by_cases hk : k ≤ F.n + 2
      · simp [Lab.limit, inI, Nat.min_eq_left hk]
      · simp [Lab.limit, inI, min_ne_of_lt (by omega : F.n + 2 < k)
          (by omega : i < F.n + 2), show k ≠ i by omega]
    | relay | res | cl => rfl
  | perm k s =>
    cases z with
    | br i t =>
      have hi : i ≤ F.n := hz
      simp only [Lab.limit, inI, min_beq (show i < F.n + 2 by omega)]
    | relay | res | cl => rfl
  | kap => rfl

theorem inJ_limit (F : Formula) {z : Vtx} (hz : z.InInstance F) (j : Lab) :
    inJ F z (j.limit (F.n + 2)) = inJ F z j := by
  cases j <;> cases z <;> try rfl
  case ch.relay k s i =>
    have hi : i ≤ F.n := hz
    simp only [Lab.limit, inJ, min_beq (show i + 1 < F.n + 2 by omega)]
    by_cases he : k = i + 1
    · subst k
      rw [Nat.min_eq_left (by omega)]
    · have hfalse : (k == i + 1) = false := by
        rw [Bool.eq_false_iff]
        exact fun h => he (beq_iff_eq.mp h)
      simp [hfalse]
  case rl.relay k i =>
    have hi : i ≤ F.n := hz
    exact min_beq (show i + 1 < F.n + 2 by omega)
  case perm.res k s i t =>
    have hi : i ≤ F.n := hz
    simp only [Lab.limit, inJ, min_beq (show i < F.n + 2 by omega)]

theorem mark_eq_limit_iff (F : Formula) {z : Vtx} (hz : z.InInstance F) (j : Lab) :
    mark F z = j.limit (F.n + 2) ↔ mark F z = j := by
  cases j <;> cases z <;> simp [mark, Lab.limit]
  all_goals
    have hi := hz
    simp only [Vtx.InInstance] at hi
    omega

/-- The finite coordinate type retains stages through the first unused one. -/
def FiniteLab (F : Formula) := {j : Lab // j.index ≤ F.n + 2}

def Lab.restrict (F : Formula) (j : Lab) : FiniteLab F :=
  ⟨j.limit (F.n + 2), by cases j <;> simp [Lab.limit, Lab.index]⟩

private def Lab.tag : Lab → Fin 5 × Bool
  | .ch _ s => (0, s)
  | .rl _ => (1, false)
  | .perm _ s => (2, s)
  | .lit _ s => (3, s)
  | .kap => (4, false)

private def finiteLabCode (F : Formula) (j : FiniteLab F) : Fin (F.n + 3) × (Fin 5 × Bool) :=
  (⟨j.val.index, by have := j.property; omega⟩, j.val.tag)

private theorem finiteLabCode_injective (F : Formula) : Function.Injective (finiteLabCode F) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ eq
  have idx := congrArg (fun z => z.1.val) eq
  have tag := congrArg Prod.snd eq
  apply Subtype.ext
  cases x <;> cases y <;> simp_all [finiteLabCode, Lab.index, Lab.tag]

instance (F : Formula) : Finite (FiniteLab F) :=
  Finite.of_injective _ (finiteLabCode_injective F)

theorem rows_limit (F : Formula) (wf : F.WF) {z : Vtx} (hz : z ∈ allRows F) (j : Lab) :
    rows F z (j.limit (F.n + 2)) = rows F z j := by
  have h := Vtx.inInstance_of_mem F hz
  simp only [rows, mark_eq_limit_iff F h j, inI_limit F wf h j, inJ_limit F h j]

end KFOL.Bichain.Quantified
