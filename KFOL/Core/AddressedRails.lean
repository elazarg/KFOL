module

public import KFOL.Core.ProfileBudgets.Queries
public import KFOL.Core.OfferLock

/-! # Shared addresses in two singleton demands

The static observations at a rail mark its head and post the rails of a
different bit of its track at the auxiliary owner. A safe fold support
meeting a track consequently contains a rail of every bit there.
-/

@[expose] public section
namespace KFOL.Core.AddressedRails

open ProfileBudgets

abbrev Rail (Track Bit : Type*) := Track × Bit × Bool

structure Book (Label Track Bit : Type*) where
  track : Label → Track
  digit : Label → Bit → Bool
  unique : ∀ f h, track f = track h → (∀ i, digit f i = digit h i) → f = h

variable {Label Track Bit : Type*}
namespace Book

variable (B : Book Label Track Bit)
def On (f : Label) (u : Rail Track Bit) : Prop :=
  B.track f = u.1 ∧ B.digit f u.2.1 = u.2.2

def Posted (F : Set Label) (u : Rail Track Bit) : Prop := ∃ f ∈ F, B.On f u

def Sparse (F : Set Label) : Prop := ∀ f ∈ F, ∀ h ∈ F, B.track f = B.track h → f = h

/-- A right vertex may also contain every label of a track. -/
def SparseOrFull (F : Set Label) : Prop :=
  ∀ g, (∀ f ∈ F, ∀ h ∈ F, B.track f = g → B.track h = g → f = h) ∨
    (∀ f, B.track f = g → f ∈ F)

theorem Sparse.sparseOrFull {F : Set Label} (s : B.Sparse F) : B.SparseOrFull F :=
  fun _ => Or.inl (fun f hf h hh fg hg => s f hf h hh (fg.trans hg.symm))

/-- A safe support reaching all bit positions of the track on which it meets
the auxiliary coalition identifies a single common label. Partial overlaps
on other tracks can be arbitrary. -/
theorem shared_address (A D : Set Label) (g : Track) (S : Set (Rail Track Bit))
    (ha : B.Sparse A) (hd : B.SparseOrFull D)
    (within : ∀ u ∈ S, B.Posted A u ∧ B.Posted D u)
    (start : ∃ u ∈ S, u.1 = g)
    (span : ∀ u ∈ S, ∀ i : Bit, ∃ v ∈ S, v.1 = u.1 ∧ v.2.1 = i) :
    ∃ f ∈ A, f ∈ D ∧ B.track f = g ∧
      ∀ u : Rail Track Bit, u.1 = g → (B.Posted A u ∧ B.Posted D u ↔ B.On f u) := by
  obtain ⟨u, hu, tg⟩ := start
  obtain ⟨⟨f, hf, ft, _⟩, ⟨h, hh, ht, _⟩⟩ := within u hu
  have member : f ∈ D := by
    obtain sparse | full := hd g
    · have same : f = h := by
        apply B.unique f h (ft.trans ht.symm)
        intro i
        obtain ⟨v, hv, vt, vi⟩ := span u hu i
        obtain ⟨⟨f', hf', ft', fd⟩, ⟨h', hh', ht', hd'⟩⟩ := within v hv
        have f'eq := ha f' hf' f hf (ft'.trans (vt.trans ft.symm))
        have h'eq := sparse h' hh' h hh (ht'.trans (vt.trans tg)) (ht.trans tg)
        simpa only [f'eq, h'eq, vi] using fd.trans hd'.symm
      exact same ▸ hh
    · exact full f (ft.trans tg)
  refine ⟨f, hf, member, ft.trans tg, ?_⟩
  intro v vg
  constructor
  · rintro ⟨⟨j, hj, ht', bit⟩, _⟩
    have e := ha j hj f hf (ht'.trans (vg.trans (ft.trans tg).symm))
    exact e ▸ ⟨ht', bit⟩
  · intro on
    exact ⟨⟨f, hf, on⟩, ⟨f, member, on⟩⟩

end Book

variable {Role : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

/-- Extract a safe support inside the two main coalitions which meets the
auxiliary coalition. This also applies when the original word uses other gates. -/
theorem support_of_three {Var Row : Type*} [Fintype Var] (three : Fin 3 ↪ Role)
    (b : Row → Budget Role Var) (habs : SingleAbsorber b (three 2))
    (A B C : Var → Bool) (t : CoreTerm Role Var) (safe : Satisfies b t)
    (a : profile (three 0) A t = true) (h : profile (three 1) B t = true)
    (c : profile (three 2) C t = true) :
    ∃ S : Set Var, SafeSupport b (three 2) S ∧
      (∀ u ∈ S, A u = true ∧ B u = true) ∧ ∃ u ∈ S, C u = true := by
  classical
  have n01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have n02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have n12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  let J : Finset Role := {three 0, three 1, three 2}
  let flags (r : Role) := if r = three 0 then A else if r = three 1 then B else C
  have f0 : flags (three 0) = A := by simp [flags]
  have f1 : flags (three 1) = B := by simp [flags, Ne.symm n01]
  have f2 : flags (three 2) = C := by simp [flags, Ne.symm n02, Ne.symm n12]
  have wins (r : Role) (hr : r ∈ J) : profile r (flags r) t = true := by
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [f0] using a
    · simpa only [f1] using h
    · simpa only [f2] using c
  obtain ⟨s, prune, hs⟩ := exists_pruning_rainbow (three 2) J flags t wins
  obtain ⟨S, _, shape, budgets⟩ := prune.ownedFold.support
  refine ⟨S, fun i => (budgets _ _).mp (prune.satisfies habs safe i), ?_, ?_⟩
  · have w0 := (shape (three 0) A).mp (f0 ▸ hs (three 0) (by simp [J]))
    have w1 := (shape (three 1) B).mp (f1 ▸ hs (three 1) (by simp [J]))
    simp only [ite_eq_right n02, ite_eq_right n12] at w0 w1
    exact fun u hu => ⟨w0 u hu, w1 u hu⟩
  · simpa only [ite_true, Finset.mem_coe] using (shape (three 2) C).mp (f2 ▸ hs (three 2) (by simp [J]))

omit [DecidableEq Role] in
/-- The static support condition gives one rail at each bit of the initial
rail's track, even when other tracks have missing bits in the support. -/
theorem safe_spans {Probe : Type*} (aux : Role) (b : Probe → Budget Role (Rail Track Bit))
    (static : ∀ (u : Rail Track Bit) (i : Bit), i ≠ u.2.1 →
      ∃ p, ¬ ((b p).values u).val ⊆ (b p).allowed ∧
        ∀ v, (b p).values v = WinnerSet.singleton aux → v.1 = u.1 ∧ v.2.1 = i)
    (S : Set (Rail Track Bit)) (safe : SafeSupport b aux S) :
    ∀ u ∈ S, ∀ i : Bit, ∃ v ∈ S, v.1 = u.1 ∧ v.2.1 = i := by
  intro u hu i
  by_cases same : i = u.2.1
  · exact ⟨u, hu, rfl, same.symm⟩
  obtain ⟨p, bad, posts⟩ := static u i same
  obtain all | ⟨_, v, hv, atom⟩ := safe p
  · exact (bad (all u hu)).elim
  · exact ⟨v, hv, posts v atom⟩

end KFOL.Core.AddressedRails
