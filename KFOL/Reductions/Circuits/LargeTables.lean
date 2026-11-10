module

public import KFOL.Reductions.Circuits.Builder
public import KFOL.Reductions.Circuits.Unfold
public import KFOL.Reset.Tables

/-! A linear shared reset graph can have exponentially many minimal guards.
The explicit selector family is independent of hardness or running-time claims. -/

@[expose] public section
namespace KFOL.Circuit.LargeTables

abbrev Variable := Bool ⊕ (ℕ × Bool)
def rootName : Variable := .inl false
def markerName : Variable := .inl true
def rail (i : ℕ) (sign : Bool) : Variable := .inr (i,sign)

/-- The displayed proof-level unfolding reuses its previous term twice.
Its native graph implementation below reuses one previous output reference. -/
def tree : ℕ → Reset.Term Variable
  | 0 => Reset.Term.step (.var markerName) (.var rootName)
  | n + 1 => Reset.Term.step
      (Reset.Term.step (tree n) (.var (rail n true)))
      (Reset.Term.step (Reset.Term.step (tree n) (.var (rail n false))) (.var rootName))

@[simp] theorem root_tree (n : ℕ) : (tree n).root = rootName := by
  cases n <;> rfl

/-- The marker is selected exactly by ambiguity of z and one chosen rail
from each independent pair. This characterizes every status valuation. -/
theorem selected_marker (n : ℕ) (B : Set Variable) :
    (tree n).Selected B markerName ↔ rootName ∈ B ∧
      ∀ i < n, rail i true ∈ B ∨ rail i false ∈ B := by
  induction n with
  | zero => simp [tree,Reset.Term.step,Reset.Term.Selected,rootName,markerName]
  | succ n ih =>
    have h : (tree (n+1)).Selected B markerName ↔
        rootName ∈ B ∧ (tree n).Selected B markerName ∧ (rail n true ∈ B ∨ rail n false ∈ B) := by
      simp [tree,Reset.Term.step,Reset.Term.Selected,rootName,markerName,rail]
      tauto
    rw [h,ih]
    constructor
    · rintro ⟨hz,⟨_,hprevious⟩,hlast⟩
      refine ⟨hz,fun i hi => ?_⟩
      by_cases he : i = n
      · simpa only [he] using hlast
      · exact hprevious i (by omega)
    · rintro ⟨hz,hall⟩
      exact ⟨hz,⟨hz,fun i hi => hall i (by omega)⟩,hall n (by omega)⟩

/-- One explicit prerequisite set for each binary orientation. -/
def guard (n : ℕ) (orientation : Fin n → Bool) : Finset Variable :=
  insert rootName (Finset.univ.image (fun i : Fin n => rail i.val (orientation i)))

@[simp] theorem root_mem_guard (n : ℕ) (orientation : Fin n → Bool) :
    rootName ∈ guard n orientation := Finset.mem_insert_self ..

@[simp] theorem rail_mem_guard (n : ℕ) (orientation : Fin n → Bool) (i : Fin n) (sign : Bool) :
    rail i.val sign ∈ guard n orientation ↔ sign = orientation i := by
  simp only [guard,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  simp only [rail,rootName,Sum.inr.injEq,Prod.mk.injEq,Sum.inr_ne_inl,false_or]
  constructor
  · rintro ⟨j,hj,hs⟩
    have he : j = i := Fin.ext hj
    simpa only [he] using hs.symm
  · intro hs
    exact ⟨i,rfl,hs.symm⟩

theorem guard_selected (n : ℕ) (orientation : Fin n → Bool) :
    (tree n).Selected (guard n orientation : Set Variable) markerName := by
  apply (selected_marker n _).mpr
  refine ⟨root_mem_guard n orientation,fun i hi => ?_⟩
  let index : Fin n := ⟨i,hi⟩
  cases hs : orientation index
  · exact Or.inr ((rail_mem_guard n orientation index false).mpr hs.symm)
  · exact Or.inl ((rail_mem_guard n orientation index true).mpr hs.symm)

/-- Every displayed prerequisite is genuinely inclusion-minimal, rather than
merely one of exponentially many syntactic derivations of fewer guards. -/
theorem guard_mem_table (n : ℕ) (orientation : Fin n → Bool) :
    guard n orientation ∈ (tree n).table markerName := by
  apply ((tree n).mem_table_iff markerName _).mpr
  refine ⟨guard_selected n orientation,fun B hBA hselected => ?_⟩
  obtain ⟨hz,hpairs⟩ := (selected_marker n (B : Set Variable)).mp hselected
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hz
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain hp | hn := hpairs i.val i.isLt
    · have he := (rail_mem_guard n orientation i true).mp (hBA hp)
      simpa only [Finset.mem_coe,he] using hp
    · have he := (rail_mem_guard n orientation i false).mp (hBA hn)
      simpa only [Finset.mem_coe,he] using hn

theorem guard_injective (n : ℕ) : Function.Injective (guard n) := by
  intro first second he
  funext i
  have hm : rail i.val (first i) ∈ guard n first := (rail_mem_guard n first i _).mpr rfl
  rw [he] at hm
  exact (rail_mem_guard n second i _).mp hm

theorem guard_subset_iff (n : ℕ) (first second : Fin n → Bool) :
    guard n first ⊆ guard n second ↔ first = second := by
  constructor
  · intro h
    exact guard_injective n ((tree n).table_antichain markerName
      (guard_mem_table n first) (guard_mem_table n second) h)
  · rintro rfl
    exact Finset.Subset.refl _

/-- A proved family of 2^n distinct minimal guards in the actual canonical
reset table. No enumeration or unproved finite exhaustiveness is used. -/
theorem exponential_table (n : ℕ) : 2^n ≤ ((tree n).table markerName).card := by
  have hsubset : Finset.univ.image (guard n) ⊆ (tree n).table markerName := by
    intro A hA
    obtain ⟨orientation,_,rfl⟩ := Finset.mem_image.mp hA
    exact guard_mem_table n orientation
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ (guard_injective n)] at hcard
  simpa using hcard

end KFOL.Circuit.LargeTables
