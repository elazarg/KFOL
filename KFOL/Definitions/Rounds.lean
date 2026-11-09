module

public import GameTheory.Languages.MultiRound.Monitoring
public import GameTheory.Languages.Bridges.FOSGToEFG

/-! # Completely disclosed finite commitment rounds

The finite-menu game tree specifies actual menus and public continuations.
Observed execution uses one joint transition; serialization uses the accepted
hidden commitment bridge. Neither equilibrium nor its recursion is defined by
the intended correspondence. The initial Boolean gate remains available.
-/

@[expose] public section

noncomputable section

namespace KFOL.Rounds

open GameTheory.Languages

universe u

/-- Every role commits a bit in each round; the complete tuple is published
at the boundary. Private signals carry no additional information. -/
abbrev bitDisclosure (Role : Type u) (horizon : ℕ) : MultiRound.MonitoringGame Role where
  Action _ := Bool
  PublicSignal := Option (Role → Bool)
  PrivateSignal _ := Unit
  horizon := horizon
  initialPublic := none
  initialPrivate _ := ()
  signalLaw _ actions := PMF.pure (some actions, fun _ => ())

/-- The observed simultaneous-round source uses the library's canonical
execution and perfect-recall information model. -/
abbrev observed (Role : Type u) (horizon : ℕ) : FOSG.Game Role :=
  (bitDisclosure Role horizon).toFOSG

/-- Hidden sequential commitments, followed by one complete revelation step.
The operational schedule is explicit and introduces no action information. -/
abbrev serial {Role : Type u} [DecidableEq Role] (horizon : ℕ)
    (order : Bridges.FOSGToEFG.ExplicitOrder Role) : EFG.Game Role :=
  Bridges.FOSGToEFG.toEFG (observed Role horizon) order

/-- A finite public tree of simultaneous nonempty finite action menus. -/
inductive Game (Role : Type u) : Type u
  | leaf (winner : Role)
  | round (sizes : Role → ℕ)
      (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)

namespace Game
variable {Role : Type u}

/-- All legal public prefixes, including the empty prefix, of this tree. -/
inductive Position : Game Role → Type u
  | root {game : Game Role} : Position game
  | down {sizes : Role → ℕ} {next : ((i : Role) → Fin (sizes i + 1)) → Game Role}
      (actions : (i : Role) → Fin (sizes i + 1)) (tail : Position (next actions)) :
      Position (.round sizes next)

/-- The continuation tree at a public prefix. -/
def Position.current {game : Game Role} : Position game → Game Role
  | .root => game
  | .down _ tail => tail.current

/-- The number of complete rounds already publicly disclosed. -/
def Position.depth {game : Game Role} : Position game → ℕ
  | .root => 0
  | .down _ tail => tail.depth + 1

/-- The menu sizes at the next public boundary; terminal menus are unused. -/
def size : Game Role → Role → ℕ
  | .leaf _ => fun _ => 0
  | .round sizes _ => sizes

/-- A terminal node is a winner leaf. -/
def Terminal : Game Role → Prop
  | .leaf _ => True
  | .round _ _ => False

/-- Extend a public prefix by one legal joint move. All menu coordinates are
checked at its actual continuation, rather than padded with extra actions. -/
def Position.append {game : Game Role} (p : Position game) (actions : Role → ℕ)
    (valid : ∀ i, actions i ≤ p.current.size i) (active : ¬ p.current.Terminal) :
    Position game := match p with
  | @root _ g => match g with
    | .leaf _ => False.elim (active trivial)
    | .round sizes _ => .down (fun i => ⟨actions i,by have := valid i; exact Nat.lt_succ_of_le this⟩) .root
  | .down a tail => .down a (tail.append actions valid active)

/-- Actual public action tuples, in chronological order. -/
def Position.path {game : Game Role} : Position game → List (Role → ℕ)
  | .root => []
  | .down a tail => (fun i => (a i).val) :: tail.path

open GameTheory.Protocol

/-- Exact observed-action execution: one legal tuple per public round. -/
abbrev execution (game : Game Role) : ExecutionProtocol Role where
  State := Position game
  Action _ := ℕ
  init := Position.root
  active p _ := ¬ p.current.Terminal
  available p i := Set.Iic (p.current.size i)
  terminal p := p.current.Terminal
  step p joint := PMF.pure (p.append (fun i => (joint.val i).getD 0) (by
    intro i
    have h := joint.property.2 i
    cases hj : joint.val i with
    | none => rw [hj] at h; exact False.elim (h joint.property.1)
    | some a => rw [hj] at h; exact h.2) joint.property.1)
  progress p active := ⟨fun _ => some 0,fun _ => ⟨active,Nat.zero_le _⟩⟩

/-- Each transition publicly discloses the complete prefix, with no private
payload. Policies therefore remember every completed joint action. -/
abbrev signals (game : Game Role) : InfoSignals game.execution where
  PublicSignal := Position game
  PrivateSignal _ := Unit
  initialPublic := Position.root
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Position game
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

/-- Observed-action information, with the exact actual menu at each prefix. -/
abbrev information (game : Game Role) : InformationModel game.execution where
  toInfoSignals := game.signals
  menu i p := {a | LegalOption game.execution p i a}
  menu_adequate := by
    intro i state trace choice
    change LegalOption game.execution (game.signals.infoOf i trace) i choice ↔ _
    exact match trace with
      | .start => Iff.rfl
      | .extend _ _ _ _ => Iff.rfl

/-- The general observed simultaneous-round game. -/
abbrev toFOSG (game : Game Role) : GameTheory.Languages.FOSG.Game Role where
  execution := game.execution
  information := game.information

/-- The accepted hidden commitment serializer, with an explicit role order. -/
abbrev serialized [DecidableEq Role] (game : Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    GameTheory.Languages.EFG.Game Role :=
  GameTheory.Languages.Bridges.FOSGToEFG.toEFG game.toFOSG order

end Game

end KFOL.Rounds
