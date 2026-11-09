module

public import KFOL.Rounds.Observed.Policies

/-! # Whole-profile root/child operations preserve unilateral deviations -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol

universe u

variable {Role : Type u}

abbrev childProfile (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (a : (i : Role) → Fin (sizes i + 1)) : Profile (next a).information.behavioralSignature :=
  fun i => restrictChild sizes next i (profile i) a

abbrev rootProfile (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : Profile (Game.round sizes next).information.behavioralSignature) :
    Profile ({ Strategy := fun i => PMF (Fin (sizes i + 1)), Outcome := Role } : GameSignature Role) :=
  fun i => rootLaw sizes next i (profile i)

abbrev assembleProfile (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (root : (i : Role) → PMF (Fin (sizes i + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → Profile (next a).information.behavioralSignature) :
    Profile (Game.round sizes next).information.behavioralSignature :=
  fun i => assemblePolicy sizes next i (root i) (fun a => children a i)

@[simp] theorem rootLaw_assemblePolicy (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role)
    (root : PMF (Fin (sizes who + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → (next a).information.BehavioralPolicy who) :
    rootLaw sizes next who (assemblePolicy sizes next who root children) = root :=
  congrArg Prod.fst ((policyEquiv sizes next who).apply_symm_apply (root,children))

@[simp] theorem restrictChild_assemblePolicy (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role)
    (root : PMF (Fin (sizes who + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → (next a).information.BehavioralPolicy who)
    (a : (i : Role) → Fin (sizes i + 1)) :
    restrictChild sizes next who (assemblePolicy sizes next who root children) a = children a :=
  congrFun (congrArg Prod.snd ((policyEquiv sizes next who).apply_symm_apply (root,children))) a

@[simp] theorem rootProfile_assemble (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (root : (i : Role) → PMF (Fin (sizes i + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → Profile (next a).information.behavioralSignature) :
    rootProfile sizes next (assembleProfile sizes next root children) = root :=
  funext (fun i => rootLaw_assemblePolicy sizes next i (root i) (fun a => children a i))

@[simp] theorem childProfile_assemble (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (root : (i : Role) → PMF (Fin (sizes i + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → Profile (next a).information.behavioralSignature)
    (a : (i : Role) → Fin (sizes i + 1)) :
    childProfile sizes next (assembleProfile sizes next root children) a = children a :=
  funext (fun i => restrictChild_assemblePolicy sizes next i (root i) (fun a => children a i) a)

theorem childProfile_update [DecidableEq Role] (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (who : Role) (alternative : (Game.round sizes next).information.BehavioralPolicy who)
    (a : (i : Role) → Fin (sizes i + 1)) :
    childProfile sizes next (Profile.update profile who alternative) a =
      Profile.update (sig := (next a).information.behavioralSignature)
        (childProfile sizes next profile a) who (restrictChild sizes next who alternative a) :=
  Profile.map_update (sig := (Game.round sizes next).information.behavioralSignature) (target := (next a).information.behavioralSignature)
    (fun i policy => restrictChild sizes next i policy a) profile who alternative

theorem rootProfile_update [DecidableEq Role] (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (who : Role) (alternative : (Game.round sizes next).information.BehavioralPolicy who) :
    rootProfile sizes next (Profile.update profile who alternative) =
      Profile.update (sig := { Strategy := fun i => PMF (Fin (sizes i + 1)), Outcome := Role })
        (rootProfile sizes next profile) who (rootLaw sizes next who alternative) :=
  Profile.map_update (sig := (Game.round sizes next).information.behavioralSignature) (target := { Strategy := fun i => PMF (Fin (sizes i + 1)), Outcome := Role })
    (fun i policy => rootLaw sizes next i policy) profile who alternative

end KFOL.Rounds.Game.Observed
