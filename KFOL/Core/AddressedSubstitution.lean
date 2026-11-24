module

public import KFOL.Algebra.Semilattice
public import KFOL.Core.AddressedRectangle
public import KFOL.Core.SingleSourceCompletion
public import KFOL.Core.MonochromaticCutObstruction
public import KFOL.Equational.Native

/-! # Reading a logical input on physical rails

A logical input is the auxiliary-owner fold of the rails in its address.
At a joint physical row just the marked logical address can carry the
observer, and every posted logical address gives the primary atom.
-/

@[expose] public section
namespace KFOL.Core.AddressedRails

open WinnerSet
attribute [local instance] Equational.coreStructure

namespace Book

variable {Role Label Track Bit : Type*} (B : Book Label Track Bit)

def rail (f : Label) (i : Bit) : Rail Track Bit := (B.track f, i, B.digit f i)

@[simp] theorem on_rail (f : Label) (i : Bit) : B.On f (B.rail f i) := ⟨rfl, rfl⟩

variable [Fintype Bit] [Nonempty Bit]

/-- The logical menu carried by an address in a physical valuation. -/
noncomputable def read (c : Role) (x : Rail Track Bit → WinnerSet Role) (f : Label) :
    WinnerSet Role :=
  choiceFold c Finset.univ Finset.univ_nonempty (fun i => x (B.rail f i))

theorem read_aux (c : Role) (x : Rail Track Bit → WinnerSet Role) (f : Label) :
    B.read c x f = singleton c ↔ ∃ i, x (B.rail f i) = singleton c := by
  simp [read, choiceFold_eq_owner_iff]

theorem read_other {c r : Role} (diff : c ≠ r) (x : Rail Track Bit → WinnerSet Role)
    (f : Label) :
    B.read c x f = singleton r ↔ ∀ i, x (B.rail f i) = singleton r := by
  simp [read, choiceFold_eq_other_iff c r diff]

private theorem source_and_no_aux {c k : Role} (diff : c ≠ k)
    (x : Rail Track Bit → WinnerSet Role) (f : Label) (mark : k ∈ (B.read c x f).val) :
    (∃ i, k ∈ (x (B.rail f i)).val) ∧ ∀ i, x (B.rail f i) ≠ singleton c := by
  have clear : ∀ i, x (B.rail f i) ≠ singleton c := by
    intro i eq
    have e := (B.read_aux c x f).mpr ⟨i, eq⟩
    exact diff ((by simpa [e] using mark : k = c).symm)
  refine ⟨?_, clear⟩
  simpa only [Finset.mem_univ, true_and] using (mem_choiceFold_of_no_owner c Finset.univ
    Finset.univ_nonempty _ (fun i _ => clear i) k).mp mark

/-- At a grouped dynamic valuation, a rival address in the same track
is blocked by a complementary rail. An address on another track has no
source of the observer. -/
theorem read_mark_source {c k : Role} (diff : c ≠ k) (f : Label)
    (x : Rail Track Bit → WinnerSet Role)
    (onlyHead : ∀ u, k ∈ (x u).val → B.On f u)
    (complement : ∀ u : Rail Track Bit, u.1 = B.track f → ¬ B.On f u → x u = singleton c)
    (g : Label) (mark : k ∈ (B.read c x g).val) : g = f := by
  obtain ⟨⟨i, win⟩, clear⟩ := B.source_and_no_aux diff x g mark
  have same : B.track f = B.track g := (onlyHead _ win).1
  apply B.unique g f same.symm
  intro j
  by_contra unequal
  exact clear j (complement (B.rail g j) same.symm (fun on => unequal on.2.symm))

/-- Every addressed input omits the mark on a static row with a single
head and both rails at another bit in that track posted at the auxiliary
owner. -/
theorem read_static {c k : Role} (diff : c ≠ k) (u : Rail Track Bit) (i : Bit)
    (x : Rail Track Bit → WinnerSet Role) (onlyHead : ∀ v, k ∈ (x v).val → v = u)
    (posts : ∀ v : Rail Track Bit, v.1 = u.1 → v.2.1 = i → x v = singleton c)
    (f : Label) : k ∉ (B.read c x f).val := by
  intro present
  obtain ⟨⟨j, win⟩, clear⟩ := B.source_and_no_aux diff x f present
  have tr : B.track f = u.1 := congrArg Prod.fst (onlyHead _ win)
  exact clear i (posts (B.rail f i) tr rfl)

omit [Fintype Bit] in
/-- A sparse vertex posting contains the full address of a label exactly
when it contains that logical label. -/
theorem all_rails_posted_iff (P : Set Label) (sparse : B.Sparse P) (f : Label) :
    (∀ i, B.Posted P (B.rail f i)) ↔ f ∈ P := by
  constructor
  · intro all
    obtain ⟨i⟩ := ‹Nonempty Bit›
    obtain ⟨g, hg, same, _⟩ := all i
    have eq : g = f := B.unique g f same (by
      intro j
      obtain ⟨h, hh, same', bit⟩ := all j
      have sameLabel := sparse h hh g hg (same'.trans same.symm)
      simpa only [sameLabel, rail] using bit)
    exact eq ▸ hg
  · exact fun mem i => ⟨f, mem, B.on_rail f i⟩

theorem read_realized [DecidableEq Role] (c : Role) (f : Label) :
    ∃ t : ProfileBudgets.CoreTerm Role (Rail Track Bit), ∀ x, t.realize x = B.read c x f := by
  let inputs (i : Bit) : Term Role (Rail Track Bit) := .var (B.rail f i)
  obtain ⟨t, core, values⟩ := Term.exists_core_choice_fold c Finset.univ Finset.univ_nonempty
    inputs (fun _ _ => trivial)
  refine ⟨Equational.Core.encode t core, fun x => ?_⟩
  rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
  exact values x

/-- Substitute address words in any logical core word. -/
theorem substitute [DecidableEq Role] (c : Role) (g : ProfileBudgets.CoreTerm Role Label) :
    ∃ t : ProfileBudgets.CoreTerm Role (Rail Track Bit), ∀ x, t.realize x = g.realize (B.read c x) := by
  choose terms correct using B.read_realized c
  refine ⟨g.subst terms, fun x => ?_⟩
  rw [FirstOrder.Language.Term.realize_subst]
  exact congrArg (fun v => g.realize v) (funext fun f => correct f x)

/-- The unanimous cap profile on logical labels becomes the condition that
the physical cap postings meet every address. -/
theorem unanimous_cap [DecidableEq Role] (c : Role) (g : ProfileBudgets.CoreTerm Role Label)
    (unanimous : ∀ A : Label → Bool, profile c A g = true ↔ ∀ f, A f = true)
    (x : Rail Track Bit → WinnerSet Role) :
    g.realize (B.read c x) = singleton c ↔ ∀ f, ∃ i, x (B.rail f i) = singleton c := by
  classical
  rw [winnerSet_eq_singleton_iff_profile, unanimous]
  simp only [decide_eq_true_eq, B.read_aux]

/-- A logical positive profile passes when every rail of each required
address is posted at its owner. -/
theorem endpoint [DecidableEq Role] (c r : Role) (diff : c ≠ r)
    (g : ProfileBudgets.CoreTerm Role Label) (A : Label → Bool)
    (win : profile r A g = true) (x : Rail Track Bit → WinnerSet Role)
    (posts : ∀ f, A f = true → ∀ i, x (B.rail f i) = singleton r) :
    g.realize (B.read c x) = singleton r := by
  classical
  apply (winnerSet_eq_singleton_iff_profile _ _ _).mpr
  exact profile_mono r A _ (fun f hf => decide_eq_true ((B.read_other diff x f).mpr
    (posts f hf))) g win

end Book
end KFOL.Core.AddressedRails

namespace KFOL.Core.AddressedSubstitution

open scoped Classical

open Sources SingleSourceCompletion ProfileSourceFiber MonochromaticCutObstruction
attribute [local instance] Equational.coreStructure

variable {Role Label : Type*} [DecidableEq Role]

omit [DecidableEq Role] in
/-- A logical monochromatic loss suppresses its marked input at a physical
valuation whenever all its postings hold and no other logical input can
supply the physical observer. The two observers may differ. -/
theorem omit_of_marked_loss (three : Fin 3 ↪ Role) (t : ProfileBudgets.CoreTerm Role Label)
    (f : Label) (A : Label → Bool) (owner logical physical : Role)
    (diff : owner ≠ logical) (other : owner ≠ physical)
    (quiet : logical ∉ (t.realize (pureProbe three logical f owner diff A)).val)
    (values : Label → WinnerSet Role) (sources : ∀ i, physical ∈ (values i).val → i = f)
    (posted : ∀ i, A i = true → values i = WinnerSet.singleton owner) :
    physical ∉ (t.realize values).val := by
  classical
  let g := Equational.Core.decode t
  have eq (v : Label → WinnerSet Role) : g.eval v = t.realize v := Equational.Core.eval_decode _ _
  intro found
  obtain ⟨i, hi, mark⟩ := (membership_iff_source three g (Equational.Core.isCore_decode t)
    values physical).mp ((eq values).symm ▸ found)
  obtain rfl := sources i hi
  let p : Observation Role i := ⟨logical, fun j => if A j.val then .atom ⟨owner, diff⟩ else .neutral⟩
  let q : Observation Role i := ⟨physical, pattern physical i values⟩
  have inc : postings p ⊆ postings q := by
    rintro ⟨j, r⟩ ⟨s, atom, rfl⟩
    by_cases yes : A j.val = true
    · have val : owner = s.val := by
        simpa [p, yes, Subtype.ext_iff] using atom
      refine ⟨⟨owner, other⟩, ?_, val⟩
      exact (passive_eq_atom_iff _ _ _).mpr (posted _ yes)
    · simp [p, yes] at atom
  have transported := supplies_downward three g (Equational.Core.isCore_decode t) p q inc mark
  exact quiet (by simpa only [Supplies, g, Equational.Core.eval_decode, pureProbe, p] using transported)

omit [DecidableEq Role] in
/-- Substitution through addresses preserves a grouped logical row, allowing
extra posted atoms on virtual inputs outside the demanded coalition. -/
theorem quiet_read {Track Bit : Type*} [Fintype Bit] [Nonempty Bit]
    (three : Fin 3 ↪ Role) (B : AddressedRails.Book Label Track Bit)
    (t : ProfileBudgets.CoreTerm Role Label) (f : Label) (A : Label → Bool)
    (owner logical physical aux : Role) (old : owner ≠ logical)
    (new : owner ≠ physical) (ar : aux ≠ owner) (ak : aux ≠ physical)
    (quiet : logical ∉ (t.realize (pureProbe three logical f owner old A)).val)
    (x : AddressedRails.Rail Track Bit → WinnerSet Role)
    (onlyHead : ∀ u, physical ∈ (x u).val → B.On f u)
    (complement : ∀ u : AddressedRails.Rail Track Bit,
      u.1 = B.track f → ¬ B.On f u → x u = WinnerSet.singleton aux)
    (posted : ∀ g, A g = true → ∀ i, x (B.rail g i) = WinnerSet.singleton owner) :
    physical ∉ (t.realize (B.read aux x)).val :=
  omit_of_marked_loss three t f A owner logical physical old new quiet (B.read aux x)
    (B.read_mark_source ak f x onlyHead complement)
    (fun g hg => (B.read_other ar x g).mpr (posted g hg))

open AddressedRails AddressedRectangle

omit [DecidableEq Role] in
/-- A logical row of either orientation is omitted on its actual grouped
rail valuation. Only its own marked address can contribute the observer. -/
theorem quiet_dynamic {Track Bit Row : Type*} [Fintype Bit] [Nonempty Bit]
    (three : Fin 3 ↪ Role) {B : Book Label Track Bit} (R : Rows B Row)
    (t : ProfileBudgets.CoreTerm Role Label) (z : Row) (logical : Role)
    (diff : orient three (R.left z) 0 ≠ logical)
    (quiet : logical ∉ (t.realize (pureProbe three logical (R.mark z)
      (orient three (R.left z) 0) diff (fun f => decide (f ∈ R.posted z)))).val) :
    R.observer three (.inl z) ∉ (t.realize (B.read (three 2) (R.values three (.inl z)))).val := by
  classical
  let o := orient three (R.left z)
  change o 1 ∉ (t.realize (B.read (three 2) (joint o B (R.posted z) (R.mark z)))).val
  rw [← orient_two three (R.left z)]
  apply quiet_read three B t (R.mark z) _ (o 0) logical (o 1) (o 2) diff
    (o.injective.ne (by decide)) (o.injective.ne (by decide)) (o.injective.ne (by decide)) quiet
  · exact fun u hm => (joint_mark o B _ _ u).mp hm
  · exact fun u tr miss => (joint_aux o B _ _ u).mpr ⟨tr, miss⟩
  · intro g hg i
    have member : g ∈ R.posted z := of_decide_eq_true hg
    exact (joint_primary o B _ _ _).mpr ⟨R.apart z g member, g, member, B.on_rail g i⟩

omit [DecidableEq Role] in
/-- Every logical word omits the mark of every static row. -/
theorem quiet_static {Track Bit : Type*} [Fintype Bit] [Nonempty Bit]
    (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (t : ProfileBudgets.CoreTerm Role Label) (p : Static Track Bit) :
    three 1 ∉ (t.realize (B.read (three 2) (staticValues three p))).val := by
  classical
  have clear (f : Label) : three 1 ∉ (B.read (three 2) (staticValues three p) f).val := by
    apply B.read_static (three.injective.ne (by decide)) p.1 p.2.val _ _ _ f
    · intro u hit
      by_contra ne
      have n12 : three 1 ≠ three 2 := three.injective.ne (by decide)
      unfold staticValues at hit
      split_ifs at hit <;> simp_all
    · intro u tr bit
      have ne : u ≠ p.1 := fun e => p.2.property (bit.symm.trans (congrArg (fun v => v.2.1) e))
      simp [staticValues, ne, tr, bit]
  intro win
  let g := Equational.Core.decode t
  have eq (v : Label → WinnerSet Role) : g.eval v = t.realize v := Equational.Core.eval_decode _ _
  obtain ⟨f, source, _⟩ := (membership_iff_source three g (Equational.Core.isCore_decode t)
    (B.read (three 2) (staticValues three p)) (three 1)).mp ((eq _).symm ▸ win)
  exact clear f source

end KFOL.Core.AddressedSubstitution
