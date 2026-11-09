module

public import KFOL.Rounds.Scalar.Reciprocal
public import KFOL.Rounds.Public.Values

/-! # Actual scalar threshold games and their possible sequential winners -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Strict root preference forces the first actual continuation law. -/
theorem publicChoice_singletons_of_gt (owner : Role) (left right : Game Role)
    (order : ExplicitOrder Role) (p q : PMF Role)
    (hp : left.sequentialValues order = {p}) (hq : right.sequentialValues order = {q})
    (hlt : (q owner).toReal < (p owner).toReal) :
    (publicChoice owner left right).sequentialValues order = {p} := by
  ext law
  rw [sequentialValues_publicChoice_iff]
  constructor
  · rintro ⟨p',hp',q',hq',α,h0,h1,hl,hr,rfl⟩
    have hep : p' = p := by simpa only [hp,Set.mem_singleton_iff] using hp'
    have heq : q' = q := by simpa only [hq,Set.mem_singleton_iff] using hq'
    subst p'; subst q'
    have hα : α = 1 := by
      apply le_antisymm h1
      exact le_of_not_gt (fun h => not_le_of_gt hlt (hr h))
    subst α
    simp only [mix_one,Set.mem_singleton_iff]
  · intro hlaw
    have he : law = p := hlaw
    rw [he]
    exact ⟨p,hp.symm ▸ Set.mem_singleton p,q,hq.symm ▸ Set.mem_singleton q,
      1,(by norm_num),le_rfl,(fun _ => hlt.le),(fun h => (lt_irrefl 1 h).elim),
      (mix_one p q).symm⟩

/-- Strict root preference forces the second actual continuation law. -/
theorem publicChoice_singletons_of_lt (owner : Role) (left right : Game Role)
    (order : ExplicitOrder Role) (p q : PMF Role)
    (hp : left.sequentialValues order = {p}) (hq : right.sequentialValues order = {q})
    (hlt : (p owner).toReal < (q owner).toReal) :
    (publicChoice owner left right).sequentialValues order = {q} := by
  ext law
  rw [sequentialValues_publicChoice_iff]
  constructor
  · rintro ⟨p',hp',q',hq',α,h0,h1,hl,hr,rfl⟩
    have hep : p' = p := by simpa only [hp,Set.mem_singleton_iff] using hp'
    have heq : q' = q := by simpa only [hq,Set.mem_singleton_iff] using hq'
    subst p'; subst q'
    have hα : α = 0 := by
      apply le_antisymm _ h0
      exact le_of_not_gt (fun h => not_le_of_gt hlt (hl h))
    subst α
    simp only [mix_zero,Set.mem_singleton_iff]
  · intro hlaw
    have he : law = q := hlaw
    rw [he]
    exact ⟨p,hp.symm ▸ Set.mem_singleton p,q,hq.symm ▸ Set.mem_singleton q,
      0,le_rfl,(by norm_num),(fun h => (lt_irrefl 0 h).elim),(fun _ => hlt.le),
      (mix_zero p q).symm⟩

/-- At indifference the actual possible winners are exactly the union of the
independently selected continuation supports. Endpoint mixes suffice for the
reverse inclusion, so no spurious convex-closure rule is used. -/
theorem possibleWinners_publicChoice_of_eq (owner : Role) (left right : Game Role)
    (order : ExplicitOrder Role) (p q : PMF Role)
    (hp : left.sequentialValues order = {p}) (hq : right.sequentialValues order = {q})
    (heq : (p owner).toReal = (q owner).toReal) :
    possibleWinners ((publicChoice owner left right).sequentialValues order) =
      possibleWinners {p} ∪ possibleWinners {q} := by
  ext who
  constructor
  · rintro ⟨law,hlaw,hwho⟩
    obtain ⟨p',hp',q',hq',α,h0,h1,_,_,rfl⟩ :=
      (sequentialValues_publicChoice_iff owner left right order law).mp hlaw
    have hep : p' = p := by simpa only [hp,Set.mem_singleton_iff] using hp'
    have heq' : q' = q := by simpa only [hq,Set.mem_singleton_iff] using hq'
    subst p'; subst q'
    by_cases hpa : p who ≠ 0
    · exact Or.inl ⟨p,rfl,hpa⟩
    · refine Or.inr ⟨q,rfl,?_⟩
      intro hqa
      exact hwho (by simp only [mix_apply,not_ne_iff.mp hpa,hqa,mul_zero,zero_add])
  · intro hwho
    have hp_mem : p ∈ (publicChoice owner left right).sequentialValues order :=
      (sequentialValues_publicChoice_iff owner left right order p).mpr
        ⟨p,hp.symm ▸ Set.mem_singleton p,q,hq.symm ▸ Set.mem_singleton q,
          1,(by norm_num),le_rfl,(fun _ => heq.ge),(fun h => (lt_irrefl 1 h).elim),
          (mix_one p q).symm⟩
    have hq_mem : q ∈ (publicChoice owner left right).sequentialValues order :=
      (sequentialValues_publicChoice_iff owner left right order q).mpr
        ⟨p,hp.symm ▸ Set.mem_singleton p,q,hq.symm ▸ Set.mem_singleton q,
          0,le_rfl,(by norm_num),(fun h => (lt_irrefl 0 h).elim),(fun _ => heq.le),
          (mix_zero p q).symm⟩
    rcases hwho with ⟨p',hp',hpa⟩ | ⟨q',hq',hqa⟩
    · have he : p' = p := hp'
      exact ⟨p,hp_mem,he ▸ hpa⟩
    · have he : q' = q := hq'
      exact ⟨q,hq_mem,he ▸ hqa⟩

end KFOL.Rounds.Game.Scalar
