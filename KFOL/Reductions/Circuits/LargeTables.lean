module

public import KFOL.Reductions.Circuits.Builder
public import KFOL.Reductions.Circuits.Unfold
public import KFOL.Reset.Extraction

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

/-- Every successful status set contains one of the displayed binary guards.
The orientation chooses the positive rail whenever it is available. -/
theorem exists_guard_subset_of_selected (n : ℕ) (B : Set Variable)
    (selected : (tree n).Selected B markerName) :
    ∃ orientation : Fin n → Bool, (guard n orientation : Set Variable) ⊆ B := by
  classical
  obtain ⟨hroot,hpairs⟩ := (selected_marker n B).mp selected
  let orientation : Fin n → Bool := fun i => if rail i.val true ∈ B then true else false
  refine ⟨orientation,?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hroot
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases hp : rail i.val true ∈ B
    · simpa only [orientation,ite_eq_left hp] using hp
    · have hn := (hpairs i.val i.isLt).resolve_left hp
      simpa only [orientation,ite_eq_right hp] using hn

/-- The actual canonical table is precisely the product of the n independent
binary rail choices, with the common root prerequisite added to every guard. -/
theorem table_marker_eq (n : ℕ) :
    (tree n).table markerName = Finset.univ.image (guard n) := by
  apply Finset.Subset.antisymm
  · intro A hA
    have hselected := ((tree n).mem_table_iff markerName A).mp hA
    obtain ⟨orientation,hsubset⟩ := exists_guard_subset_of_selected n (A : Set Variable) hselected.1
    have hguard := guard_mem_table n orientation
    have he : guard n orientation = A := (tree n).table_antichain markerName hguard hA hsubset
    exact Finset.mem_image.mpr ⟨orientation,Finset.mem_univ _,he⟩
  · intro A hA
    obtain ⟨orientation,_,rfl⟩ := Finset.mem_image.mp hA
    exact guard_mem_table n orientation

/-- Exact exponential table size, with proved exhaustiveness. -/
theorem card_table_marker (n : ℕ) : ((tree n).table markerName).card = 2^n := by
  rw [table_marker_eq,Finset.card_image_of_injective _ (guard_injective n)]
  simp

/-- Every canonical guard has the same size: one common root and n rails. -/
theorem card_guard (n : ℕ) (orientation : Fin n → Bool) :
    (guard n orientation).card = n+1 := by
  have hroot : rootName ∉ Finset.univ.image (fun i : Fin n => rail i.val (orientation i)) := by
    simp [rootName,rail]
  have hinjective : Function.Injective (fun i : Fin n => rail i.val (orientation i)) := by
    intro i j he
    exact Fin.ext (congrArg (fun x : ℕ × Bool => x.1) (Sum.inr.inj he))
  rw [guard,Finset.card_insert_of_notMem hroot,Finset.card_image_of_injective _ hinjective]
  simp

theorem card_mem_table_marker (n : ℕ) {A : Finset Variable}
    (hA : A ∈ (tree n).table markerName) : A.card = n+1 := by
  rw [table_marker_eq] at hA
  obtain ⟨orientation,_,rfl⟩ := Finset.mem_image.mp hA
  exact card_guard n orientation

/-- The marker payload alone has exactly (n+1)2^n prerequisite occurrences. -/
theorem sum_guard_card_marker (n : ℕ) :
    ∑ A ∈ (tree n).table markerName, A.card = (n+1)*2^n := by
  calc
    _ = ∑ _A ∈ (tree n).table markerName, (n+1) :=
      Finset.sum_congr rfl (fun _ hA => card_mem_table_marker n hA)
    _ = (n+1)*2^n := by simp [card_table_marker,Nat.mul_comm]

/-- The exhibited unfolded tree attains the marker-occurrence lower bound. -/
theorem occurrences_marker_tree (n : ℕ) : (tree n).occurrences markerName = 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [tree,Reset.Term.occurrences_step,Reset.Term.occurrences_var,ih]
    simp only [markerName,rootName,rail,Sum.inl_ne_inr,ite_false,Bool.true_eq_false,
      Sum.inl.injEq,Nat.add_zero]
    rw [pow_succ]
    omega

/-- The exact table count gives the exponential lower bound. -/
theorem exponential_table (n : ℕ) : 2^n ≤ ((tree n).table markerName).card := by
  simpa only [card_table_marker] using Nat.le_refl (2^n)

end KFOL.Circuit.LargeTables
