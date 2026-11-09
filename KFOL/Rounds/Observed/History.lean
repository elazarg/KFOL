module

public import KFOL.Rounds.Observed.Policies

/-! # Actual child histories and certified round bounds -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol

universe u

variable {Role : Type u}

/-- The canonical complete history at an intrinsic public prefix. -/
def historyAt (game : Game Role) (p : Position game) : game.execution.History :=
  game.historyEquivPosition.symm p

@[simp] theorem historyAt_state (game : Game Role) (p : Position game) :
    (historyAt game p).state = p := (game.historyEquivPosition).apply_symm_apply p

/-- Embed one actual child occurrence into the parent history carrier. -/
def historyDown (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (a : (i : Role) → Fin (sizes i + 1)) (h : (next a).execution.History) :
    (Game.round sizes next).execution.History :=
  historyAt (.round sizes next) (.down a h.state)

@[simp] theorem historyDown_state (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (a : (i : Role) → Fin (sizes i + 1)) (h : (next a).execution.History) :
    (historyDown sizes next a h).state = .down a h.state := historyAt_state _ _

theorem historyDown_injective (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (a : (i : Role) → Fin (sizes i + 1)) :
    Function.Injective (historyDown sizes next a) := by
  intro h j he
  apply (next a).historyEquivPosition.injective
  change h.state = j.state
  apply Position.path_injective
  have hs := congrArg (fun h => Position.path h.state) he
  simp only [historyDown_state,Position.path] at hs
  exact (List.cons.inj hs).2

/-- The canonical history length is exactly the intrinsic public depth. -/
theorem trace_length_eq_depth (game : Game Role) {p : Position game}
    (trace : game.execution.Trace p) : trace.length = p.depth := by
  refine ExecutionProtocol.Trace.rec (E := game.execution)
    (motive := fun p tr => tr.length = p.depth) rfl ?_ trace
  intro source target prior joint legal realized ih
  have he : target = source.append (fun i => (joint i).getD 0)
      (joint_bound game source joint legal) legal.1 := by
    simpa only [execution,PMF.mem_support_pure_iff] using realized
  change prior.length + 1 = target.depth
  rw [he,Position.depth_append]
  exact congrArg (· + 1) ih

@[simp] theorem historyDown_length (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (a : (i : Role) → Fin (sizes i + 1)) (h : (next a).execution.History) :
    (historyDown sizes next a h).trace.length = h.trace.length + 1 := by
  rw [trace_length_eq_depth,historyDown_state,Position.depth,trace_length_eq_depth]

@[simp] theorem historyDown_winner (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (a : (i : Role) → Fin (sizes i + 1)) (h : (next a).execution.History) :
    (Game.round sizes next).winner (historyDown sizes next a h) = (next a).winner h := by
  simp only [winner,historyDown_state,Position.current]

/-- A round has a genuinely positive certified horizon. -/
theorem round_bound_positive (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) {bound : Nat}
    (bounded : (Game.round sizes next).execution.BoundedHorizon bound) : 0 < bound := by
  by_contra hn
  have hb : bound = 0 := by omega
  exact bounded Position.root .start (by simp [hb,ExecutionProtocol.Trace.length])

/-- Removing the disclosed first joint move leaves a certified child horizon,
including every off-path child and every history in that child. -/
theorem child_bounded_horizon (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) {bound : Nat}
    (bounded : (Game.round sizes next).execution.BoundedHorizon bound)
    (a : (i : Role) → Fin (sizes i + 1)) :
    (next a).execution.BoundedHorizon (bound - 1) := by
  intro p trace hlo
  let h : (next a).execution.History := ⟨p,trace⟩
  have hpositive := round_bound_positive sizes next bounded
  have hb : bound ≤ (historyDown sizes next a h).trace.length := by
    rw [historyDown_length]
    change bound ≤ trace.length + 1
    omega
  have ht := bounded _ (historyDown sizes next a h).trace hb
  simpa only [execution,historyDown_state,Position.current] using ht

end KFOL.Rounds.Game.Observed
