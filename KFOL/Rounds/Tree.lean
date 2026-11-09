module

public import KFOL.Definitions.Rounds
public import Mathlib.Basic.Finite.Prod
public import GameTheory.Protocol.FiniteHorizon
public import GameTheory.Protocol.FiniteInformation

/-! # Exact finite-menu public round execution -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game

open GameTheory.Protocol
universe u
variable {Role : Type u}

@[simp] theorem Position.depth_append {game : Game Role} (p : Position game)
    (a : Role → ℕ) (hv : ∀ i, a i ≤ p.current.size i) (ha : ¬ p.current.Terminal) :
    (p.append a hv ha).depth = p.depth + 1 := by
  induction p with
  | @root g =>
    cases g with
    | leaf r => exact False.elim (ha trivial)
    | round sizes next => rfl
  | down a p ih =>
    simp only [Position.append, Position.depth]
    rw [ih hv ha]

/-- The complete prefix carrier is finite, even though the action alphabet is
unbounded: only the actual finite menus contribute children. -/
instance finite_position [Finite Role] (game : Game Role) : Finite (Position game) := by
  induction game with
  | leaf r =>
    exact Finite.of_surjective (fun _ : Unit => (Position.root : Position (.leaf r))) (by
      intro p; cases p; exact ⟨(),rfl⟩)
  | round sizes next ih =>
    let _ : ∀ a, Finite (Position (next a)) := ih
    apply Finite.of_surjective
      (fun q : Option ((a : (i : Role) → Fin (sizes i+1)) × Position (next a)) =>
        match q with | none => Position.root | some ⟨a,p⟩ => Position.down a p)
    intro p
    cases p with
    | root => exact ⟨none,rfl⟩
    | down a p => exact ⟨some ⟨a,p⟩,rfl⟩


@[simp] theorem Position.path_append {game : Game Role} (p : Position game)
    (a : Role → ℕ) (hv : ∀ i, a i ≤ p.current.size i) (ha : ¬ p.current.Terminal) :
    (p.append a hv ha).path = p.path ++ [a] := by
  induction p with
  | @root g =>
    cases g with
    | leaf r => exact False.elim (ha trivial)
    | round sizes next => rfl
  | down a p ih =>
    simp only [Position.append, Position.path, List.cons_append]
    rw [ih hv ha]

theorem Position.path_injective {game : Game Role} :
    Function.Injective (Position.path (game := game)) := by
  intro p q he
  induction p with
  | root => cases q with
    | root => rfl
    | down a tail => simp only [Position.path] at he; cases he
  | @down sizes next a p ih =>
    cases q with
    | root => simp only [Position.path] at he; cases he
    | down b q =>
      obtain ⟨hab,hpq⟩ := List.cons.inj he
      have hab' : a = b := by
        funext i
        exact Fin.ext (congrFun hab i)
      subst b
      exact congrArg (Position.down a) (ih hpq)

theorem Position.append_ne_root {game : Game Role} (p : Position game)
    (a : Role → ℕ) (hv : ∀ i, a i ≤ p.current.size i) (ha : ¬ p.current.Terminal) :
    p.append a hv ha ≠ Position.root := by
  intro he
  have := congrArg Position.path he
  simp only [Position.path_append,Position.path,List.append_eq_nil_iff,List.cons_ne_nil,
    and_false] at this

theorem Position.append_injective {game : Game Role} (p q : Position game)
    (a b : Role → ℕ) (ha : ∀ i, a i ≤ p.current.size i)
    (hb : ∀ i, b i ≤ q.current.size i) (pa : ¬ p.current.Terminal)
    (qa : ¬ q.current.Terminal) (he : p.append a ha pa = q.append b hb qa) :
    p = q ∧ a = b := by
  have hp := congrArg Position.path he
  rw [Position.path_append,Position.path_append] at hp
  obtain ⟨hp,hab⟩ := List.append_singleton_inj.mp hp
  exact ⟨Position.path_injective hp,hab⟩

@[simp] theorem information_eq_position (game : Game Role) (i : Role)
    {p : Position game} (trace : game.execution.Trace p) :
    game.information.infoOf i trace = p :=
  match trace with | .start => rfl | .extend _ _ _ _ => rfl

theorem joint_bound (game : Game Role) (p : Position game) (a : Role → Option ℕ)
    (legal : game.execution.Legal p a) :
    ∀ i, (a i).getD 0 ≤ p.current.size i := by
  intro i
  have h := legal.2 i
  cases hi : a i with
  | none => rw [hi] at h; exact False.elim (h legal.1)
  | some v => rw [hi] at h; exact h.2

@[simp] theorem step_depth (game : Game Role) (p : Position game)
    (joint : {a : Role → Option ℕ // game.execution.Legal p a})
    {q : Position game} (hq : q ∈ (game.execution.step p joint).support) :
    q.depth = p.depth + 1 := by
  have hq' : q = p.append (fun i => (joint.val i).getD 0) (joint_bound game p joint.val joint.property) joint.property.1 := by
    simpa only [execution,PMF.mem_support_pure_iff] using hq
  subst q
  exact Position.depth_append _ _ _ _

theorem tree_shaped (game : Game Role) : game.execution.IsTreeShaped := by
  apply ExecutionProtocol.isTreeShaped_of_predecessor_unique
  · intro source joint isLegal hs
    have he : Position.root = source.append (fun i => (joint i).getD 0) (joint_bound game source joint isLegal) isLegal.1 := by
      simpa only [execution,PMF.mem_support_pure_iff] using hs
    exact Position.append_ne_root _ _ _ _ he.symm
  · intro target p q a b ha hb hpa hqb
    have hpa' : target = p.append (fun i => (a i).getD 0) (joint_bound game p a ha) ha.1 := by
      simpa only [execution,PMF.mem_support_pure_iff] using hpa
    have hqb' : target = q.append (fun i => (b i).getD 0) (joint_bound game q b hb) hb.1 := by
      simpa only [execution,PMF.mem_support_pure_iff] using hqb
    obtain ⟨hpq,hab⟩ := Position.append_injective _ _ _ _ _ _ _ _ (hpa'.symm.trans hqb')
    refine ⟨hpq,funext fun i => ?_⟩
    have hc := congrFun hab i
    have hai := ha.2 i
    have hbi := hb.2 i
    cases hea : a i with
    | none => rw [hea] at hai; exact False.elim (hai ha.1)
    | some av =>
      cases heb : b i with
      | none => rw [heb] at hbi; exact False.elim (hbi hb.1)
      | some bv => simpa only [hea,heb,Option.getD_some,Option.some.injEq] using hc

/-- All players remember their completed actions at every public prefix. -/
theorem perfect_recall (game : Game Role) : game.information.PerfectRecall := by
  intro i p q hp hq he
  rw [information_eq_position,information_eq_position] at he
  subst q
  have ht : hp = hq := (game.tree_shaped p).elim hp hq
  subst hq
  rfl


/-- The tree-shaped protocol has finitely many actual complete histories. -/
instance finite_history [Finite Role] (game : Game Role) : Finite game.execution.History := by
  let _ : Fintype game.execution.State := Fintype.ofFinite _
  let _ := game.execution.historyFintype game.tree_shaped
  infer_instance

/-- Finiteness certifies a uniform bound, including every off-path history. -/
theorem exists_bounded_horizon [Finite Role] (game : Game Role) :
    ∃ bound, 0 < bound ∧ game.execution.BoundedHorizon bound :=
  game.execution.exists_pos_boundedHorizon

/-- Every observed round game terminates under all legal play. -/
theorem well_founded_histories [Finite Role] (game : Game Role) :
    game.execution.WellFoundedHistories := game.execution.wellFoundedHistories_of_fintype

/-- The canonical decision-recall premise follows from full public memory. -/
theorem decision_recall (game : Game Role) : game.information.DecisionRecall :=
  game.information.decisionRecall_of_perfectRecall game.perfect_recall

end KFOL.Rounds.Game
