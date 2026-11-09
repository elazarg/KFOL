module

public import KFOL.Rounds.Correspondence
public import KFOL.Rounds.Scalar.Distribution
public import GameTheory.Math.Probability.Product

/-! # The exact one-active-role menu and its marginal law -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.Public
open GameTheory GameTheory.Math.Probability
universe u
variable {Role : Type u} [DecidableEq Role]

abbrev sizes (owner : Role) (i : Role) : Nat := if i = owner then 1 else 0

def action (owner : Role) (bit : Fin 2) (i : Role) : Fin (sizes owner i + 1) :=
  ⟨if i = owner then bit.val else 0, by
    by_cases he : i = owner
    · simpa [sizes,he] using bit.isLt
    · simp [sizes,he]⟩

def bit (owner : Role) (joint : (i : Role) → Fin (sizes owner i + 1)) : Fin 2 :=
  ⟨(joint owner).val,by simpa [sizes] using (joint owner).isLt⟩

@[simp] theorem bit_action (owner : Role) (b : Fin 2) : bit owner (action owner b) = b := by
  apply Fin.ext
  simp [bit,action]

@[simp] theorem action_bit (owner : Role) (joint : (i : Role) → Fin (sizes owner i + 1)) :
    action owner (bit owner joint) = joint := by
  funext i
  apply Fin.ext
  by_cases he : i = owner
  · subst i
    simp [action,bit]
  · have hi := (joint i).isLt
    simp only [sizes,ite_eq_right he] at hi
    simp [action,he]
    omega

def menuBit (owner : Role) (choice : Fin (sizes owner owner+1)) : Fin 2 :=
  ⟨choice.val,by simpa [sizes] using choice.isLt⟩

def menuChoice (owner : Role) (b : Fin 2) : Fin (sizes owner owner+1) :=
  ⟨b.val,by simpa [sizes] using b.isLt⟩

@[simp] theorem menuBit_choice (owner : Role) (b : Fin 2) : menuBit owner (menuChoice owner b) = b := rfl
@[simp] theorem menuChoice_bit (owner : Role) (b : Fin (sizes owner owner+1)) :
    menuChoice owner (menuBit owner b) = b := rfl

/-- The actual joint-action marginal is the owner's actual menu law. -/
theorem bit_law [Fintype Role] (owner : Role)
    (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    (independentProduct profile).map (bit owner) = (profile owner).map (menuBit owner) := by
  calc
    _ = ((independentProduct profile).map (fun a => a owner)).map (menuBit owner) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [independentProduct_map_eval]

/-- Any actual continuation table is determined by its two actual owner
choices; the other roles have precisely one legal action. -/
theorem table_eq {α : Type*} (owner : Role)
    (p : ((i : Role) → Fin (sizes owner i+1)) → α)
    (joint : (i : Role) → Fin (sizes owner i+1)) :
    p joint = if (joint owner).val = 0 then p (action owner 0) else p (action owner 1) := by
  rw [← action_bit owner joint]
  have hv := (bit owner joint).isLt
  by_cases he : (bit owner joint).val = 0
  · have heq : bit owner joint = 0 := Fin.ext he
    simp [heq,action]
  · have heq : bit owner joint = 1 := Fin.ext (by omega)
    simp [heq,action]

/-- Exact canonical stage outcome law, with no padded actions or correlated
random seed. The coefficient is the owner's actual probability of index zero. -/
theorem stage_law [Fintype Role] (owner : Role)
    (p : ((i : Role) → Fin (sizes owner i+1)) → PMF Role)
    (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    (stageForm (sizes owner) p).mixed.play profile =
      mix (((profile owner).map (menuBit owner)) 0).toReal ENNReal.toReal_nonneg
        (pmf_toReal_apply_le_one _ _) (p (action owner 0)) (p (action owner 1)) := by
  let law := (profile owner).map (menuBit owner)
  have he : p = fun joint => if (bit owner joint).val = 0 then p (action owner 0) else p (action owner 1) :=
    funext (table_eq owner p)
  change (independentProduct profile).bind p = _
  rw [he]
  change (independentProduct profile).bind ((fun b : Fin 2 =>
    if b.val = 0 then p (action owner 0) else p (action owner 1)) ∘ bit owner) = _
  rw [← PMF.bind_map,bit_law]
  ext who
  rw [PMF.bind_apply,tsum_fintype,Fin.sum_univ_two,mix_apply]
  have hsum : law 0 + law 1 = 1 := by
    have hh := PMF.tsum_coe law
    simpa only [tsum_fintype,Fin.sum_univ_two] using hh
  have hcomp : law 1 = ENNReal.ofReal (1 - (law 0).toReal) := by
    apply (ENNReal.toReal_eq_toReal_iff' (law.apply_ne_top _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by have := pmf_toReal_apply_le_one law 0; linarith)]
    have hh := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (law.apply_ne_top _) (law.apply_ne_top _)] at hh
    norm_num at hh
    linarith
  change law 0 * p (action owner 0) who + law 1 * p (action owner 1) who = _
  rw [ENNReal.ofReal_toReal (law.apply_ne_top _),← hcomp]
  simp only [bit_action]
  rfl

end KFOL.Rounds.Game.Public
