module

public import KFOL.Definitions.ProfileRelations
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Push

/-! # Complete rainbow-Horn presentations of profile relations

Three available owner gates give coordinatewise conjunction. Every finite
conjunction-closed relation has a Horn presentation; owner mixing reduces
its minimal clauses to forced bits, same-owner unary implications, and pure
rainbow conflicts. Empty relations and empty coordinate sets are included.
-/

@[expose] public section
namespace KFOL.Core.ProfileRelations
universe u v
variable {Index : Type u} {Role : Type v}
variable [DecidableEq Role] (owner : Index → Role)

private theorem mixed_and (three : Fin 3 ↪ Role) (x y : Index → Bool) :
    mixedChoice owner (three 2) (mixedChoice owner (three 0) x y)
      (mixedChoice owner (three 1) x y) = fun i => x i && y i := by
  funext i
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  by_cases h0 : owner i = three 0
  · have h1 : owner i ≠ three 1 := by simpa only [h0] using h01
    have h2 : owner i ≠ three 2 := by simpa only [h0] using h02
    cases hx : x i <;> cases hy : y i <;> simp [mixedChoice,h0,hx,hy]
  by_cases h1 : owner i = three 1
  · have h2 : owner i ≠ three 2 := by simpa only [h1] using h12
    cases hx : x i <;> cases hy : y i <;> simp [mixedChoice,h1,hx,hy]
  · by_cases h2 : owner i = three 2 <;>
      cases hx : x i <;> cases hy : y i <;> simp [mixedChoice,h0,h1,h2,hx,hy]

/-- Three owner gates make every closed profile relation conjunction-closed. -/
theorem ChoiceClosed.and {R : Set (Index → Bool)} (hc : ChoiceClosed owner R)
    (three : Fin 3 ↪ Role) {x y : Index → Bool} (hx : x ∈ R) (hy : y ∈ R) :
    (fun i => x i && y i) ∈ R := by
  rw [← mixed_and owner three x y]
  exact hc _ _ _ (hc _ _ _ hx hy) (hc _ _ _ hx hy)

private theorem rainbow_choice {S : Finset Index} (hr : Rainbow owner S)
    (r : Role) (x y : Index → Bool) (h : AllTrue S (mixedChoice owner r x y)) :
    AllTrue S x ∨ AllTrue S y := by
  classical
  by_cases hex : ∃ i ∈ S, owner i = r
  · obtain ⟨i,hi,hir⟩ := hex
    have hh : x i = true ∨ y i = true := by simpa [mixedChoice,hir] using h i hi
    have other (j : Index) (hj : j ∈ S) (hji : j ≠ i) : owner j ≠ r := by
      intro hjr
      exact hji (hr j hj i hi (hjr.trans hir.symm))
    rcases hh with hxi | hyi
    · left
      intro j hj
      by_cases hji : j = i
      · simpa only [hji] using hxi
      · have hp : x j = true ∧ y j = true := by
          simpa [mixedChoice,other j hj hji] using h j hj
        exact hp.1
    · right
      intro j hj
      by_cases hji : j = i
      · simpa only [hji] using hyi
      · have hp : x j = true ∧ y j = true := by
          simpa [mixedChoice,other j hj hji] using h j hj
        exact hp.2
  · left
    intro j hj
    have hjr : owner j ≠ r := fun hh => hex ⟨j,hj,hh⟩
    have hp : x j = true ∧ y j = true := by simpa [mixedChoice,hjr] using h j hj
    exact hp.1

/-- Every theory in the restricted vocabulary is preserved by all mixed gates. -/
theorem Theory.models_choiceClosed (T : Theory owner) : ChoiceClosed owner T.Models := by
  intro r x y hx hy
  refine ⟨?_,?_,?_⟩
  · intro i hi
    simp [mixedChoice,hx.1 i hi,hy.1 i hi]
  · intro i j hij hp
    have ho := T.same_owner i j hij
    by_cases hir : owner i = r
    · have hjr : owner j = r := ho.symm.trans hir
      have hh : x i = true ∨ y i = true := by simpa [mixedChoice,hir] using hp
      rcases hh with hxi | hyi
      · simp [mixedChoice,hjr,hx.2.1 i j hij hxi]
      · simp [mixedChoice,hjr,hy.2.1 i j hij hyi]
    · have hjr : owner j ≠ r := fun h => hir (ho.trans h)
      have hh : x i = true ∧ y i = true := by simpa [mixedChoice,hir] using hp
      simp [mixedChoice,hjr,hx.2.1 i j hij hh.1,hy.2.1 i j hij hh.2]
  · intro S hS hp
    rcases rainbow_choice owner (T.rainbow S hS) r x y hp with hh | hh
    · exact hx.2.2 S hS hh
    · exact hy.2.2 S hS hh

omit [DecidableEq Role] in
/-- A rainbow conflict has at most one antecedent per owner. -/
theorem Rainbow.card_le [Fintype Role] {S : Finset Index} (h : Rainbow owner S) :
    S.card ≤ Fintype.card Role := by
  classical
  let f : S → Role := fun i => owner i.val
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact h i.val i.property j.val j.property he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private def Feasible (R : Set (Index → Bool)) (S : Finset Index) : Prop :=
  ∃ x ∈ R, AllTrue S x

private def ValidImp (R : Set (Index → Bool)) (S : Finset Index) (b : Index) : Prop :=
  ∀ x ∈ R, AllTrue S x → x b = true

variable [DecidableEq Index]

omit [DecidableEq Index] in
private theorem minimal_subset (P : Finset Index → Prop) (S : Finset Index) (h : P S) :
    ∃ T, T ⊆ S ∧ P T ∧ ∀ U, U ⊆ T → P U → T ⊆ U := by
  classical
  let F := S.powerset.filter P
  have hS : S ∈ F := by simp [F,h]
  obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image F Finset.card ⟨S,hS⟩
  obtain ⟨hTS,hPT⟩ := Finset.mem_filter.mp hT
  have hsub := Finset.mem_powerset.mp hTS
  refine ⟨T,hsub,hPT,?_⟩
  intro U hUT hPU
  have hUF : U ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hUT.trans hsub),hPU⟩
  exact (Finset.eq_of_subset_of_card_le hUT (hmin U hUF)).symm.le

private theorem erase_mix {S : Finset Index} {a b : Index} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (ho : owner a = owner b) {x y : Index → Bool}
    (hx : AllTrue (S.erase a) x) (hy : AllTrue (S.erase b) y) :
    AllTrue S (mixedChoice owner (owner a) x y) := by
  intro i hi
  by_cases hia : i = a
  · subst i
    have hya := hy a (Finset.mem_erase.mpr ⟨hab,ha⟩)
    simp [mixedChoice,hya]
  by_cases hib : i = b
  · subst i
    have hxb := hx b (Finset.mem_erase.mpr ⟨Ne.symm hab,hb⟩)
    simp [mixedChoice,ho,hxb]
  · have hxi := hx i (Finset.mem_erase.mpr ⟨hia,hi⟩)
    have hyi := hy i (Finset.mem_erase.mpr ⟨hib,hi⟩)
    simp [mixedChoice,hxi,hyi]

private theorem rainbow_forbidden {R : Set (Index → Bool)} (hc : ChoiceClosed owner R)
    (S : Finset Index) (hn : ¬Feasible R S) :
    ∃ T, T ⊆ S ∧ Rainbow owner T ∧ ¬Feasible R T := by
  classical
  obtain ⟨T,hTS,hT,hmin⟩ := minimal_subset (fun U => ¬Feasible R U) S hn
  have witness (a : Index) (ha : a ∈ T) : Feasible R (T.erase a) := by
    by_contra hh
    exact (Finset.notMem_erase a T) ((hmin _ (Finset.erase_subset a T) hh) ha)
  refine ⟨T,hTS,?_,hT⟩
  intro a ha b hb ho
  by_contra hab
  obtain ⟨x,hx,hax⟩ := witness a ha
  obtain ⟨y,hy,hby⟩ := witness b hb
  exact hT ⟨mixedChoice owner (owner a) x y,hc _ _ _ hx hy,
    erase_mix owner ha hb hab ho hax hby⟩

private theorem minimal_implication {R : Set (Index → Bool)}
    (hc : ChoiceClosed owner R) (S : Finset Index) (b : Index)
    (hv : ValidImp R S b) (hf : Feasible R S) :
    (∀ x ∈ R, x b = true) ∨
      ∃ a ∈ S, owner a = owner b ∧ ∀ x ∈ R, x a = true → x b = true := by
  classical
  obtain ⟨T,hTS,hT,hmin⟩ := minimal_subset (fun U => ValidImp R U b) S hv
  obtain ⟨y,hy,hSy⟩ := hf
  have hTy : AllTrue T y := fun i hi => hSy i (hTS hi)
  have witness (a : Index) (ha : a ∈ T) :
      ∃ x ∈ R, AllTrue (T.erase a) x ∧ x b = false := by
    have hn : ¬ValidImp R (T.erase a) b := by
      intro hh
      exact (Finset.notMem_erase a T) ((hmin _ (Finset.erase_subset a T) hh) ha)
    simp only [ValidImp] at hn
    push Not at hn
    obtain ⟨x,hx,hall,hb⟩ := hn
    refine ⟨x,hx,hall,?_⟩
    cases he : x b <;> simp_all
  have same (a : Index) (ha : a ∈ T) : owner a = owner b := by
    by_contra ho
    obtain ⟨x,hx,hall,hb⟩ := witness a ha
    have hz : AllTrue T (mixedChoice owner (owner a) x y) := by
      intro i hi
      by_cases hia : i = a
      · subst i
        simp [mixedChoice,hTy a ha]
      · simp [mixedChoice,hall i (Finset.mem_erase.mpr ⟨hia,hi⟩),hTy i hi]
    have hzb := hT _ (hc _ _ _ hx hy) hz
    have hob : owner b ≠ owner a := Ne.symm ho
    simp [mixedChoice,hob,hb] at hzb
  have unique (a : Index) (ha : a ∈ T) (c : Index) (hcT : c ∈ T) : a = c := by
    by_contra hac
    obtain ⟨x,hx,hax,hbx⟩ := witness a ha
    obtain ⟨z,hz,hcz,hbz⟩ := witness c hcT
    have hall := erase_mix owner ha hcT hac ((same a ha).trans (same c hcT).symm) hax hcz
    have hzb := hT _ (hc _ _ _ hx hz) hall
    simp [mixedChoice,← same a ha,hbx,hbz] at hzb
  by_cases hne : T.Nonempty
  · obtain ⟨a,ha⟩ := hne
    right
    refine ⟨a,hTS ha,same a ha,?_⟩
    intro x hx hxa
    apply hT x hx
    intro i hi
    simpa only [unique i hi a ha] using hxa
  · left
    intro x hx
    apply hT x hx
    intro i hi
    exact (hne ⟨i,hi⟩).elim

variable [Fintype Index]

private noncomputable def trueBits (x : Index → Bool) : Finset Index := by
  classical
  exact Finset.univ.filter (fun i => x i = true)

omit [DecidableEq Index] in
private theorem mem_trueBits (x : Index → Bool) (i : Index) :
    i ∈ trueBits x ↔ x i = true := by
  classical
  simp [trueBits]

omit [DecidableEq Index] in
private theorem trueBits_injective : Function.Injective (trueBits (Index := Index)) := by
  intro x y h
  funext i
  have hh : x i = true ↔ y i = true := by rw [← mem_trueBits x i,← mem_trueBits y i,h]
  cases hx : x i <;> cases hy : y i <;> simp_all

private noncomputable def canonical (R : Set (Index → Bool)) : Theory owner := by
  classical
  exact {
    forced := Finset.univ.filter (fun i => ∀ x ∈ R, x i = true)
    implies := fun i j => owner i = owner j ∧ ∀ x ∈ R, x i = true → x j = true
    same_owner := fun _ _ h => h.1
    conflicts := Finset.univ.filter (fun S => Rainbow owner S ∧ ¬Feasible R S)
    rainbow := fun _ h => (Finset.mem_filter.mp h).2.1 }

omit [DecidableEq Role] in
private theorem canonical_models (R : Set (Index → Bool)) {x : Index → Bool} (hx : x ∈ R) :
    (canonical owner R).Models x := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2 x hx
  · intro i j hij hxi
    exact hij.2 x hx hxi
  · intro S hS hall
    exact (Finset.mem_filter.mp hS).2.2 ⟨x,hx,hall⟩

private theorem canonical_complete {R : Set (Index → Bool)} (hc : ChoiceClosed owner R)
    (three : Fin 3 ↪ Role) {x : Index → Bool} (hx : (canonical owner R).Models x) : x ∈ R := by
  classical
  have hfeasible : Feasible R (trueBits x) := by
    by_contra hn
    obtain ⟨S,hS,hr,hs⟩ := rainbow_forbidden owner hc _ hn
    have hconf : S ∈ (canonical owner R).conflicts := by simp [canonical,hr,hs]
    apply hx.2.2 S hconf
    exact fun i hi => (mem_trueBits x i).mp (hS hi)
  let above := (Finset.univ : Finset (Index → Bool)).filter
    (fun y => y ∈ R ∧ AllTrue (trueBits x) y)
  obtain ⟨y,hy,hmin⟩ := Finset.exists_min_image above (fun y => (trueBits y).card)
    (by obtain ⟨y,hy,hall⟩ := hfeasible; exact ⟨y,by simp [above,hy,hall]⟩)
  obtain ⟨hyR,hyall⟩ := (Finset.mem_filter.mp hy).2
  have hyx : trueBits x ⊆ trueBits y := fun i hi => (mem_trueBits y i).mpr (hyall i hi)
  have minimal (z : Index → Bool) (hz : z ∈ R) (hzall : AllTrue (trueBits x) z) :
      trueBits y ⊆ trueBits z := by
    let w := fun i => y i && z i
    have hwR : w ∈ R := hc.and owner three hyR hz
    have hwall : AllTrue (trueBits x) w := by
      intro i hi
      simp [w,hyall i hi,hzall i hi]
    have hw : w ∈ above := by simp [above,hwR,hwall]
    have hsub : trueBits w ⊆ trueBits y := by
      intro i hi
      have hh : y i = true ∧ z i = true := by
        simpa [trueBits,w] using hi
      exact (mem_trueBits y i).mpr hh.1
    have he : trueBits w = trueBits y := Finset.eq_of_subset_of_card_le hsub (hmin w hw)
    intro i hi
    have hw' : i ∈ trueBits w := he.symm ▸ hi
    have hh : y i = true ∧ z i = true := by simpa [trueBits,w] using hw'
    exact (mem_trueBits z i).mpr hh.2
  by_contra hnot
  have hne : trueBits x ≠ trueBits y := by
    intro he
    exact hnot ((trueBits_injective he).symm ▸ hyR)
  obtain ⟨b,hby,hbx⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hyx,hne⟩)
  have hbfalse : x b ≠ true := fun hh => hbx ((mem_trueBits x b).mpr hh)
  have hvalid : ValidImp R (trueBits x) b := by
    intro z hz hzall
    exact (mem_trueBits z b).mp (minimal z hz hzall hby)
  rcases minimal_implication owner hc _ b hvalid hfeasible with hf | ⟨a,ha,ho,himp⟩
  · exact hbfalse (hx.1 b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩))
  · exact hbfalse (hx.2.1 a b ⟨ho,himp⟩ ((mem_trueBits x a).mp ha))

/-- Membership is determined by all valid constraints in the three restricted
forms; this is the canonical, presentation-independent version of the theorem. -/
theorem ChoiceClosed.mem_iff_constraints {R : Set (Index → Bool)}
    (hc : ChoiceClosed owner R) (three : Fin 3 ↪ Role) (x : Index → Bool) :
    x ∈ R ↔
      (∀ i, (∀ y ∈ R, y i = true) → x i = true) ∧
      (∀ i j, owner i = owner j →
        (∀ y ∈ R, y i = true → y j = true) → x i = true → x j = true) ∧
      ∀ S : Finset Index, Rainbow owner S →
        (∀ y ∈ R, ¬AllTrue S y) → ¬AllTrue S x := by
  classical
  constructor
  · intro hx
    exact ⟨fun _ h => h x hx,fun _ _ _ h => h x hx,fun _ _ h => h x hx⟩
  · rintro ⟨hf,hi,hcfl⟩
    apply canonical_complete owner hc three
    refine ⟨?_,?_,?_⟩
    · intro i hforced
      exact hf i (Finset.mem_filter.mp hforced).2
    · intro i j himp
      exact hi i j himp.1 himp.2
    · intro S hS
      obtain ⟨hr,hn⟩ := (Finset.mem_filter.mp hS).2
      exact hcfl S hr (fun y hy hall => hn ⟨y,hy,hall⟩)

/-- Exactly the mixed-gate-closed finite Boolean relations have presentations
by forced bits, same-owner unary implications, and rainbow conflicts. -/
theorem choiceClosed_iff_theory (three : Fin 3 ↪ Role) (R : Set (Index → Bool)) :
    ChoiceClosed owner R ↔ ∃ T : Theory owner, ∀ x, x ∈ R ↔ T.Models x := by
  constructor
  · intro hc
    exact ⟨canonical owner R,fun x => ⟨canonical_models owner R,
      canonical_complete owner hc three⟩⟩
  · rintro ⟨T,hT⟩ r x y hx hy
    exact (hT _).mpr (T.models_choiceClosed owner r x y ((hT x).mp hx) ((hT y).mp hy))

end KFOL.Core.ProfileRelations
