module

public import KFOL.Core.AddressedRectangle
public import KFOL.Core.AddressedSelectorCap
public import KFOL.Core.AddressedSubstitution
public import KFOL.Core.OneOwnerSelector

/-! # Recovering the rectangle witness from the complete selector table -/

@[expose] public section
namespace KFOL.Core.AddressedTableExtraction

open AddressedRails AddressedRectangle ProfileBudgets WinnerSet
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Label Track Bit Row : Type*} [DecidableEq Role]
variable [Fintype Bit] [Nonempty Bit]

/-- The internal cap is the conjunction of the address clauses. -/
noncomputable def cap (B : Book Label Track Bit) (flags : Rail Track Bit → Bool) : Bool :=
  decide (∀ f, ∃ i, flags (B.rail f i) = true)

/-- Retain the selector; each of its designated singletons exposes just its
corresponding group on the read-back logical inputs. -/
noncomputable def baseline (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (left right : CoreTerm Role Label) (z : WinnerSet Role) (v : Rail Track Bit → WinnerSet Role) :
    WinnerSet Role :=
  (OneOwnerSelector.mask (three 1) z (left.realize (B.read (three 2) v))).union
    (OneOwnerSelector.mask (three 0) z (right.realize (B.read (three 2) v)))

noncomputable def operation (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (left right : CoreTerm Role Label) (z : WinnerSet Role) (v : Rail Track Bit → WinnerSet Role) :
    WinnerSet Role :=
  AddressedSelectorCap.target (three 2) (cap B) (baseline three B left right) z v

omit [DecidableEq Role] in
theorem baseline_retain (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (left right : CoreTerm Role Label) (z : WinnerSet Role) (v : Rail Track Bit → WinnerSet Role) :
    z.val ⊆ (baseline three B left right z v).val :=
  fun _ h => Or.inl (Or.inl h)

omit [DecidableEq Role] in
theorem baseline_side (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (left right : CoreTerm Role Label) (side : Bool) (v : Rail Track Bit → WinnerSet Role) :
    baseline three B left right (singleton (orient three side 0)) v =
      (singleton (orient three side 0)).union
        ((if side then left else right).realize (B.read (three 2) v)) := by
  have ne : three 0 ≠ three 1 := three.injective.ne (by decide)
  cases side <;> apply Subtype.ext <;>
    simp only [baseline, OneOwnerSelector.mask_eq, orient_zero, ite_true, Bool.false_eq_true,
      ite_false, singleton_inj, ne, Ne.symm ne, val_union] <;> ext k <;>
    simp only [Set.mem_union] <;> tauto

omit [Fintype Bit] in
theorem cap_top (B : Book Label Track Bit) : cap B (fun _ => true) = true := by
  obtain ⟨i⟩ := ‹Nonempty Bit›
  exact decide_eq_true (fun _ => ⟨i,rfl⟩)

omit [Fintype Bit] [Nonempty Bit] in
theorem cap_empty [Nonempty Label] (B : Book Label Track Bit) : cap B (fun _ => false) = false := by
  obtain ⟨f⟩ := ‹Nonempty Label›
  apply decide_eq_false
  intro h
  obtain ⟨_, bad⟩ := h f
  cases bad

variable [Nonempty Label] [Nontrivial Bit]

/-- A realizer of the complete target yields one physical word satisfying
both endpoint profiles and every active grouped and static omission. -/
theorem extract (three : Fin 3 ↪ Role) (B : Book Label Track Bit) (R : Rows B Row)
    (S : Finset Row) (x y : Label → Bool) (left right : CoreTerm Role Label)
    (leftWin : profile (three 0) x left = true)
    (rightWin : profile (three 1) (fun f => !(y f)) right = true)
    (dynamic : ∀ z ∈ S, orient three (R.left z) 1 ∉
      ((if R.left z then left else right).realize
        (B.read (three 2) (R.values three (.inl z)))).val)
    (staticQuiet : ∀ p : Static Track Bit, three 1 ∉
      (left.realize (B.read (three 2) (staticValues three p))).val)
    (t : CoreTerm Role (Option (Rail Track Bit)))
    (realizes : ∀ z v, t.realize (fun j => j.elim z v) = operation three B left right z v) :
    ∃ h : CoreTerm Role (Rail Track Bit),
      (R.encoding three).Quiet S h ∧ (R.encoding three).Demands x y h := by
  classical
  have n01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have n02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have n12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  obtain ⟨h,_,preserve⟩ := AddressedSelectorCap.extract (three 2) (three 0) n02
    (cap B) (cap_top B) (baseline three B left right) (baseline_retain three B left right) t realizes
  have quiet_side (side : Bool) (v : Rail Track Bit → WinnerSet Role)
      (quiet : orient three side 1 ∉ ((if side then left else right).realize (B.read (three 2) v)).val) :
      orient three side 1 ∉ (h.realize v).val := by
    let which := orient three side
    have distinct : which 1 ≠ which 0 := which.injective.ne (by decide)
    have safe : which 0 ≠ three 2 := by
      change orient three side 0 ≠ three 2
      cases side <;> simp [n02,n12]
    have other : which 1 ≠ three 2 := by
      change orient three side 1 ≠ three 2
      cases side <;> simp [n02,n12]
    apply (preserve (singleton (which 0)) v (fun e => safe (singleton_inj.mp e))).1 _ other
    rw [baseline_side three B left right side v]
    exact fun member => member.elim distinct quiet
  refine ⟨h, ?_, ?_⟩
  · intro p active
    cases p with
    | inl z => exact quiet_side _ _ (dynamic z (active z rfl))
    | inr p =>
      have quiet := quiet_side true (staticValues three p) (by simpa using staticQuiet p)
      change three 1 ∉ (h.realize (staticValues three p)).val
      simpa only [orient_one, ite_true] using quiet
  · have endpoint (side : Bool) (P : Label → Bool)
        (win : profile (orient three side 0) P (if side then left else right) = true) :
        profile (orient three side 0) (Rows.flags (B := B) {f | P f = true}) h = true := by
      let r := orient three side 0
      let s := orient three side 1
      have rc : r ≠ three 2 := by
        change orient three side 0 ≠ three 2
        cases side <;> simp [n02,n12]
      have sc : s ≠ three 2 := by
        change orient three side 1 ≠ three 2
        cases side <;> simp [n02,n12]
      have sr : s ≠ r := (orient three side).injective.ne (by decide)
      let flags := Rows.flags (B := B) {f | P f = true}
      let v (u : Rail Track Bit) : WinnerSet Role := if flags u then singleton r else singleton s
      have atom := B.endpoint (three 2) r (Ne.symm rc) (if side then left else right) P win v
        (by
          intro f hf i
          have flag : flags (B.rail f i) = true := decide_eq_true ⟨f,hf,B.on_rail f i⟩
          simp [v,flag])
      have bits : (fun u => decide (v u = singleton r)) = flags := by
        funext u
        cases e : flags u <;> simp [v,e,singleton_inj,sr]
      have noCap : (fun u => decide (v u = singleton (three 2))) = fun _ => false := by
        funext u
        cases e : flags u <;> simp [v,e,singleton_inj,rc,sc]
      have one : baseline three B left right (singleton r) v = singleton r := by
        rw [baseline_side three B left right side v, atom, WinnerSet.union_self]
      have ha := (preserve (singleton r) v (fun e => rc (singleton_inj.mp e))).2
        (by rw [noCap]; exact cap_empty B) r one
      simpa only [bits] using (winnerSet_eq_singleton_iff_profile h r v).mp ha
    constructor
    · exact endpoint true x leftWin
    · change profile (three 1) (Rows.flags (B := B) {f | y f = false}) h = true
      have win := endpoint false (fun f => !(y f)) rightWin
      simpa only [Rows.flags, Bool.not_eq_true', orient_zero, Bool.false_eq_true, ite_false] using win

/-- Logical source losses and endpoint tests suffice for extracting the full
physical rectangle witness from a realizer of the complete table. -/
theorem extract_of_group_losses (three : Fin 3 ↪ Role) (B : Book Label Track Bit) (R : Rows B Row)
    (S : Finset Row) (x y : Label → Bool) (left right : CoreTerm Role Label)
    (leftWin : profile (three 0) x left = true)
    (rightWin : profile (three 1) (fun f => !(y f)) right = true)
    (lose : ∀ z ∈ S, ∃ (k : Role) (other : orient three (R.left z) 0 ≠ k),
      k ∉ ((if R.left z then left else right).realize (MonochromaticCutObstruction.pureProbe
        three k (R.mark z) (orient three (R.left z) 0) other
        (fun f => decide (f ∈ R.posted z)))).val)
    (t : CoreTerm Role (Option (Rail Track Bit)))
    (realizes : ∀ z v, t.realize (fun j => j.elim z v) = operation three B left right z v) :
    ∃ h : CoreTerm Role (Rail Track Bit),
      (R.encoding three).Quiet S h ∧ (R.encoding three).Demands x y h := by
  apply extract three B R S x y left right leftWin rightWin _ (AddressedSubstitution.quiet_static three B left) t realizes
  intro z hz
  obtain ⟨k, other, quiet⟩ := lose z hz
  exact AddressedSubstitution.quiet_dynamic three R _ z k other quiet

end KFOL.Core.AddressedTableExtraction
