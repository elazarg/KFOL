/- Semantic certificates for reset/union and two-owner H reductions.
The complexity and tree-size arguments are stated in the paper. -/
import Reset

set_option autoImplicit false
namespace MinimalChoice.SmallFragments
open ResetCalculus
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem multiple_mono {α : Type} {A B : S α} (h : Sub A B)
    (hm : Multiple A) : Multiple B := by
  rcases hm with ⟨x, y, hxy, hx, hy⟩
  exact ⟨x, y, hxy, h x hx, h y hy⟩

theorem multiple_iff_ne_atom {α : Type} (A : S α) (r : α) (hr : A r) :
    Multiple A ↔ A ≠ atom r := by
  constructor
  · intro hm he
    exact not_multiple_atom r (he ▸ hm)
  · intro hn
    rcases atom_or_multiple A ⟨r, hr⟩ with ⟨s, hs⟩ | hm
    · have hrs : r = s := show atom s r from hs ▸ hr
      exact False.elim (hn (hs.trans (congrArg atom hrs.symm)))
    · exact hm

theorem guard_multiple {α : Type} (A : S α) (r : α) (ha : NE A) :
    Multiple (join A (atom r)) ↔ A ≠ atom r := by
  rw [multiple_iff_ne_atom _ r (Or.inr rfl)]
  simp [join_eq_atom_iff A (atom r) ha (atom_ne r) r]

def unions {α : Type} : List (S α) → S α → S α
  | [], base => base
  | A :: rest, base => join A (unions rest base)

theorem unions_mem {α : Type} (xs : List (S α)) (base : S α) (w : α) :
    unions xs base w ↔ base w ∨ ∃ A ∈ xs, A w := by
  induction xs with
  | nil => simp [unions]
  | cons A xs ih => simp only [unions, join, ih, List.mem_cons]; grind

theorem unions_ne {α : Type} (xs : List (S α)) (base : S α) (hb : NE base) :
    NE (unions xs base) := by
  rcases hb with ⟨w, hw⟩
  exact ⟨w, (unions_mem xs base w).mpr (Or.inl hw)⟩

theorem unions_atom_iff {α : Type} (xs : List (S α)) (r : α)
    (hx : ∀ A ∈ xs, NE A) :
    unions xs (atom r) = atom r ↔ ∀ A ∈ xs, A = atom r := by
  induction xs with
  | nil => simp [unions]
  | cons A xs ih =>
    rw [unions, join_eq_atom_iff A _ (hx A (by simp))
      (unions_ne xs _ (atom_ne r)) r]
    have ht : ∀ B ∈ xs, NE B := fun B hB => hx B (by simp [hB])
    rw [ih ht]
    simp

noncomputable def rightResets {α : Type} : List (S α) → S α → S α
  | [], base => base
  | A :: rest, base => reset A (rightResets rest base)

noncomputable def leftResets {α : Type} : List (S α) → S α → S α
  | [], base => base
  | A :: rest, base => leftResets rest (reset base A)

theorem rightResets_multiple {α : Type} (xs : List (S α)) (base : S α) :
    Multiple (rightResets xs base) ↔ Multiple base := by
  induction xs <;> simp_all [rightResets, reset_multiple]

theorem rightResets_mem {α : Type} (xs : List (S α)) (base : S α)
    (hm : Multiple base) (w : α) :
    rightResets xs base w ↔ base w ∨ ∃ A ∈ xs, A w := by
  induction xs with
  | nil => simp [rightResets]
  | cons A xs ih =>
    simp only [rightResets, reset_membership, rightResets_multiple, hm, true_and, ih,
      List.mem_cons]
    grind

/-- Outside the common baseline, a left comb retains its marker exactly
when all guards are ambiguous. -/
theorem leftResets_marker {α : Type} (gs : List (S α)) (C W : S α) (w : α)
    (hw : ¬ W w) (hg : ∀ g ∈ gs, Sub g W) :
    leftResets gs C w ↔ C w ∧ ∀ g ∈ gs, Multiple g := by
  induction gs generalizing C with
  | nil => simp [leftResets]
  | cons g gs ih =>
    have hgw : ¬ g w := fun h => hw (hg g (by simp) w h)
    have ht : ∀ q ∈ gs, Sub q W := fun q hq => hg q (by simp [hq])
    rw [leftResets, ih (reset C g) ht, reset_membership]
    simp only [hgw, false_or, List.mem_cons]
    grind

noncomputable def H {α : Type} (r : α) (X Y Z : S α) : S α :=
  reset (own r Y Z) X

theorem reset_from_H {α : Type} (r : α) (A B : S α) :
    H r B A A = reset A B := by rw [H, own_idem]

theorem H_idem {α : Type} (r : α) (A : S α) : H r A A A = A := by
  rw [reset_from_H, basis_idem]

theorem H_resolved {α : Type} (r x : α) (Y Z : S α) :
    H r (atom x) Y Z = atom x := by
  simp [H, reset, not_multiple_atom]

theorem rightResets_resolved {α : Type} (xs : List (S α)) (r : α) :
    rightResets xs (atom r) = atom r := by
  induction xs <;> simp_all [rightResets, reset, not_multiple_atom]

theorem H_marker {α : Type} (r : α) (X Y Z W : S α) (w : α)
    (hx : Multiple X) (hX : Sub X W) (hY : Sub Y W) (hw : ¬ W w) :
    H r X Y Z w ↔ Z w ∧ Y ≠ atom r := by
  have hxw : ¬ X w := fun h => hw (hX w h)
  have hyw : ¬ Y w := fun h => hw (hY w h)
  by_cases hrw : r = w
  · subst r
    have hy : Y ≠ atom w := fun he => hyw (he.symm ▸ (rfl : atom w w))
    rw [H, reset_membership, own_mem_owner]
    simp [hxw, hyw, hy, hx]
  have hz : Z w → Z ≠ atom r := by
    intro h he
    have hwr : w = r := show atom r w from he ▸ h
    exact hrw hwr.symm
  rw [H, reset_membership, own_mem_other r w hrw]
  simp only [hxw, hyw, hx, false_or, true_and]
  grind

def Lit (β : Type) := β × Bool

def Holds {β : Type} (v : β → Prop) (l : Lit β) : Prop :=
  if l.2 then v l.1 else ¬ v l.1

def Sat {β : Type} (F : List (List (Lit β))) (v : β → Prop) : Prop :=
  ∀ c ∈ F, ∃ l ∈ c, Holds v l

/-- Satisfied guard clauses of an unsatisfiable CNF force a conflicting rail. -/
theorem unsat_rails {β : Type} (F : List (List (Lit β))) (p n : β → Prop)
    (hu : ∀ v, ¬ Sat F v)
    (hc : ∀ c ∈ F, ∃ l ∈ c, if l.2 then p l.1 else n l.1) :
    ∃ i, p i ∧ n i := by
  apply Classical.byContradiction
  intro hn
  apply hu p
  intro c hcf
  rcases hc c hcf with ⟨l, hl, hp⟩
  refine ⟨l, hl, ?_⟩
  cases hb : l.2
  · have hneg : n l.1 := by simpa [hb] using hp
    simp only [Holds, hb, Bool.false_eq_true, ↓reduceIte]
    exact fun h => hn ⟨l.1, h, hneg⟩
  · simpa [Holds, hb] using hp


noncomputable def hClause {α β : Type} (a b : α) (Z : S α) (Y : β → S α)
    (clause : List (Lit β)) (C : S α) : S α :=
  match clause with
  | [] => C
  | l :: rest => H (if l.2 then a else b) Z (Y l.1) (hClause a b Z Y rest C)

theorem hClause_marker {α β : Type} (a b : α) (Z W C : S α) (Y : β → S α)
    (clause : List (Lit β)) (w : α) (hz : Multiple Z) (hZW : Sub Z W)
    (hY : ∀ i, Sub (Y i) W) (hw : ¬ W w) :
    hClause a b Z Y clause C w ↔ C w ∧
      ∀ l ∈ clause, Y l.1 ≠ atom (if l.2 then a else b) := by
  induction clause with
  | nil => simp [hClause]
  | cons l rest ih =>
    rw [hClause, H_marker _ Z _ _ W w hz hZW (hY l.1) hw, ih]
    simp only [List.mem_cons]
    grind

theorem unsat_h_clause {α β : Type} (a b : α) (hab : a ≠ b)
    (F : List (List (Lit β))) (Y : β → S α) (hu : ∀ v, ¬ Sat F v) :
    ∃ clause ∈ F, ∀ l ∈ clause, Y l.1 ≠ atom (if l.2 then a else b) := by
  have hf : ∃ clause ∈ F, ∀ l ∈ clause, ¬ Holds (fun i => Y i = atom a) l := by
    simpa [Sat] using hu (fun i => Y i = atom a)
  rcases hf with ⟨clause, hc, hf⟩
  refine ⟨clause, hc, ?_⟩
  intro l hl
  have h := hf l hl
  cases hb : l.2
  · have hy : Y l.1 = atom a := by simpa [Holds, hb] using h
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hy]
    exact fun he => hab (atom_inj.mp he)
  · simpa [Holds, hb] using h

/-- The semantic UNSAT direction for the actual H-clause/right-comb construction. -/
theorem h_unsat_absorption {α β : Type} (a b : α) (hab : a ≠ b)
    (F : List (List (Lit β))) (Y : β → S α) (Z W C : S α)
    (hz : Multiple Z) (hZW : Sub Z W) (hY : ∀ i, Sub (Y i) W)
    (hu : ∀ v, ¬ Sat F v) :
    let R := rightResets (F.map (fun clause => hClause a b Z Y clause C)) W
    reset C R = R := by
  have hmW := multiple_mono hZW hz
  let R := rightResets (F.map (fun clause => hClause a b Z Y clause C)) W
  have hmR : Multiple R := (rightResets_multiple _ W).mpr hmW
  have hCR : Sub C R := by
    intro w hc
    apply (rightResets_mem _ W hmW w).mpr
    by_cases hw : W w
    · exact Or.inl hw
    · rcases unsat_h_clause a b hab F Y hu with ⟨clause, hcf, hf⟩
      refine Or.inr ⟨hClause a b Z Y clause C, List.mem_map.mpr ⟨clause, hcf, rfl⟩, ?_⟩
      exact (hClause_marker a b Z W C Y clause w hz hZW hY hw).mpr ⟨hc, hf⟩
  change reset C R = R
  funext w
  apply propext
  simp only [reset_membership, hmR, true_and]
  exact ⟨fun h => h.elim id (hCR w), Or.inl⟩

/-- A satisfied literal in each clause removes a fresh marker. This supplies
counterexamples independently of the UNSAT soundness theorem. -/
theorem h_sat_separation {α β : Type} (a b : α) (F : List (List (Lit β)))
    (Y : β → S α) (Z W C : S α) (w : α) (hz : Multiple Z)
    (hZW : Sub Z W) (hY : ∀ i, Sub (Y i) W) (hw : ¬ W w) (hc : C w)
    (hs : ∀ clause ∈ F, ∃ l ∈ clause, Y l.1 = atom (if l.2 then a else b)) :
    let R := rightResets (F.map (fun clause => hClause a b Z Y clause C)) W
    reset C R ≠ R := by
  let R := rightResets (F.map (fun clause => hClause a b Z Y clause C)) W
  change reset C R ≠ R
  have hmW := multiple_mono hZW hz
  have hn : ¬ R w := by
    dsimp only [R]
    rw [rightResets_mem _ W hmW]
    rintro (h | ⟨branch, hb, hbw⟩)
    · exact hw h
    · rcases List.mem_map.mp hb with ⟨clause, hcf, he⟩
      subst branch
      have hall := ((hClause_marker a b Z W C Y clause w hz hZW hY hw).mp hbw).2
      rcases hs clause hcf with ⟨l, hl, he⟩
      exact hall l hl he
  intro he
  have hmR : Multiple R := (rightResets_multiple _ W).mpr hmW
  have hp : reset C R w := (reset_membership C R w).mpr (Or.inr ⟨hmR, hc⟩)
  exact hn (he ▸ hp)


theorem unions_multiple_atom {α : Type} (xs : List (S α)) (r : α)
    (hx : ∀ A ∈ xs, NE A) :
    Multiple (unions xs (atom r)) ↔ ∃ A ∈ xs, A ≠ atom r := by
  have hr : unions xs (atom r) r := (unions_mem xs _ r).mpr (Or.inl rfl)
  rw [multiple_iff_ne_atom _ r hr]
  simp [Ne, unions_atom_iff xs r hx]

def clauseGuard {α β : Type} (P N : β → S α) (T : S α)
    (clause : List (Lit β)) : S α :=
  unions (clause.map (fun l => if l.2 then P l.1 else N l.1)) T

theorem clauseGuard_multiple {α β : Type} (P N : β → S α) (r : α)
    (hp : ∀ i, NE (P i)) (hn : ∀ i, NE (N i)) (clause : List (Lit β)) :
    Multiple (clauseGuard P N (atom r) clause) ↔
      ∃ l ∈ clause, if l.2 then P l.1 ≠ atom r else N l.1 ≠ atom r := by
  have hne : ∀ A ∈ clause.map (fun l => if l.2 then P l.1 else N l.1), NE A := by
    intro A ha
    rcases List.mem_map.mp ha with ⟨l, _, he⟩
    subst A
    cases l.2 <;> simp [hp, hn]
  rw [clauseGuard, unions_multiple_atom _ r hne]
  simp only [List.mem_map]
  constructor
  · rintro ⟨A, ⟨l, hl, he⟩, ha⟩
    subst A
    refine ⟨l, hl, ?_⟩
    cases hb : l.2 <;> simpa [hb] using ha
  · rintro ⟨l, hl, ha⟩
    refine ⟨if l.2 then P l.1 else N l.1, ⟨l, hl, rfl⟩, ?_⟩
    cases hb : l.2 <;> simpa [hb] using ha

/-- The Boolean implication used by the reset/union reduction, at arbitrary
nonempty winner sets and for any unsatisfiable CNF. -/
theorem union_guard_logic {α β : Type} (F : List (List (Lit β)))
    (P N : β → S α) (T : S α) (inh : β) (ht : NE T)
    (hp : ∀ i, NE (P i)) (hn : ∀ i, NE (N i)) (hu : ∀ v, ¬ Sat F v)
    (hc : ∀ clause ∈ F, Multiple (clauseGuard P N T clause)) :
    ∃ i, Multiple (join (P i) T) ∧ Multiple (join (N i) T) := by
  rcases atom_or_multiple T ht with ⟨r, hr⟩ | hm
  · subst T
    have hrails : ∀ clause ∈ F, ∃ l ∈ clause,
        if l.2 then P l.1 ≠ atom r else N l.1 ≠ atom r := by
      intro clause hcf
      exact (clauseGuard_multiple P N r hp hn clause).mp (hc clause hcf)
    rcases unsat_rails F (fun i => P i ≠ atom r) (fun i => N i ≠ atom r) hu hrails
      with ⟨i, hi, hj⟩
    exact ⟨i, (guard_multiple (P i) r (hp i)).mpr hi,
      (guard_multiple (N i) r (hn i)).mpr hj⟩
  · exact ⟨inh, multiple_mono (fun _ h => Or.inr h) hm,
      multiple_mono (fun _ h => Or.inr h) hm⟩

def badBranch {α : Type} (C : S α) (pair : S α × S α) : S α :=
  reset (reset C pair.1) pair.2

theorem badBranch_marker {α : Type} (C W : S α) (pair : S α × S α)
    (w : α) (hw : ¬ W w) (hp : Sub pair.1 W) (hn : Sub pair.2 W) :
    badBranch C pair w ↔ C w ∧ Multiple pair.1 ∧ Multiple pair.2 := by
  have hpm : ¬pair.1 w := fun h => hw (hp w h)
  have hnm : ¬pair.2 w := fun h => hw (hn w h)
  simp only [badBranch, reset_membership, hpm, hnm, false_or]
  grind

/-- Absorption for the native reset/union construction from its guard
implication. `union_guard_logic` supplies that implication for UNSAT. -/
theorem union_absorption {α : Type} (pairs : List (S α × S α))
    (clauses : List (S α)) (C W : S α) (hmW : Multiple W)
    (hp : ∀ pair ∈ pairs, Sub pair.1 W ∧ Sub pair.2 W)
    (hg : ∀ g ∈ clauses, Sub g W)
    (hlogic : (∀ g ∈ clauses, Multiple g) →
      ∃ pair ∈ pairs, Multiple pair.1 ∧ Multiple pair.2) :
    let R := rightResets (pairs.map (badBranch C)) W
    reset (leftResets clauses C) R = R := by
  let R := rightResets (pairs.map (badBranch C)) W
  change reset (leftResets clauses C) R = R
  have hmR : Multiple R := (rightResets_multiple _ W).mpr hmW
  have hs : Sub (leftResets clauses C) R := by
    intro w ha
    apply (rightResets_mem _ W hmW w).mpr
    by_cases hw : W w
    · exact Or.inl hw
    · have hm := (leftResets_marker clauses C W w hw hg).mp ha
      rcases hlogic hm.2 with ⟨pair, hpair, hpm, hnm⟩
      refine Or.inr ⟨badBranch C pair, List.mem_map.mpr ⟨pair, hpair, rfl⟩, ?_⟩
      exact (badBranch_marker C W pair w hw (hp pair hpair).1 (hp pair hpair).2).mpr
        ⟨hm.1, hpm, hnm⟩
  funext w
  apply propext
  simp only [reset_membership, hmR, true_and]
  exact ⟨fun h => h.elim id (hs w), Or.inl⟩

theorem union_separation {α : Type} (pairs : List (S α × S α))
    (clauses : List (S α)) (C W : S α) (w : α) (hmW : Multiple W)
    (hp : ∀ pair ∈ pairs, Sub pair.1 W ∧ Sub pair.2 W)
    (hg : ∀ g ∈ clauses, Sub g W) (hw : ¬ W w) (hc : C w)
    (hpass : ∀ g ∈ clauses, Multiple g)
    (hconsistent : ∀ pair ∈ pairs, ¬ (Multiple pair.1 ∧ Multiple pair.2)) :
    let R := rightResets (pairs.map (badBranch C)) W
    reset (leftResets clauses C) R ≠ R := by
  let R := rightResets (pairs.map (badBranch C)) W
  change reset (leftResets clauses C) R ≠ R
  have hmR : Multiple R := (rightResets_multiple _ W).mpr hmW
  have hn : ¬ R w := by
    dsimp only [R]
    rw [rightResets_mem _ W hmW]
    rintro (h | ⟨branch, hb, hbw⟩)
    · exact hw h
    · rcases List.mem_map.mp hb with ⟨pair, hpair, he⟩
      subst branch
      have hm := (badBranch_marker C W pair w hw (hp pair hpair).1 (hp pair hpair).2).mp hbw
      exact hconsistent pair hpair ⟨hm.2.1, hm.2.2⟩
  have hl := (leftResets_marker clauses C W w hw hg).mpr ⟨hc, hpass⟩
  intro he
  have hleft := (reset_membership _ R w).mpr (Or.inr ⟨hmR, hl⟩)
  exact hn (he ▸ hleft)


/-- Finite pigeonhole, proved from duplicate-free lists in Std. -/
theorem fin_injective_surjective {k : Nat} (f : Fin k → Fin k)
    (hf : Function.Injective f) (w : Fin k) : ∃ i, f i = w := by
  apply Classical.byContradiction
  intro hn
  have hne : ∀ i, f i ≠ w := fun i h => hn ⟨i, h⟩
  have hnodup : ((List.finRange k).map f).Nodup :=
    List.Pairwise.map f (fun i j hij he => hij (hf he)) (List.nodup_finRange k)
  have hsub : (List.finRange k).map f ⊆ (List.finRange k).erase w := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, _, he⟩
    subst x
    exact (List.mem_erase_of_ne (hne i)).mpr (List.mem_finRange (f i))
  have hlen := hnodup.length_le_of_subset hsub
  rw [List.length_map, List.length_finRange,
    List.length_erase_of_mem (List.mem_finRange w), List.length_finRange] at hlen
  have hw := w.isLt
  omega

/-- A fresh baseline marker forces either an ambiguous vertex or a
resolved edge guard. This is the generic K-colouring obstruction. -/
theorem colouring_guard_obstruction {k : Nat} (X : Fin k → S (Fin k))
    (W : S (Fin k)) (hne : ∀ i, NE (X i)) (hX : ∀ i, Sub (X i) W)
    (w : Fin k) (hw : ¬ W w) (hatom : ∀ i, ¬ Multiple (X i)) :
    ∃ i j, i ≠ j ∧ ¬ Multiple (join (X i) (X j)) := by
  apply Classical.byContradiction
  intro hn
  have hs : ∀ i, ∃ r, X i = atom r := by
    intro i
    rcases atom_or_multiple (X i) (hne i) with h | h
    · exact h
    · exact False.elim (hatom i h)
  let f : Fin k → Fin k := fun i => Classical.choose (hs i)
  have hf : ∀ i, X i = atom (f i) := fun i => Classical.choose_spec (hs i)
  have hinj : Function.Injective f := by
    intro i j he
    apply Classical.byContradiction
    intro hij
    apply hn
    refine ⟨i, j, hij, ?_⟩
    rw [hf i, hf j, he]
    have hj : join (atom (f j)) (atom (f j)) = atom (f j) := by
      funext r
      exact propext ⟨fun h => h.elim id id, Or.inl⟩
    rw [hj]
    exact not_multiple_atom _
  rcases fin_injective_surjective f hinj w with ⟨i, hi⟩
  have hwi : X i w := by rw [hf i, hi]; rfl
  exact hw (hX i w hwi)

#print axioms colouring_guard_obstruction
#print axioms union_guard_logic
#print axioms union_absorption
#print axioms union_separation
#print axioms h_unsat_absorption
#print axioms h_sat_separation
#print axioms leftResets_marker
#print axioms H_marker
#print axioms unsat_rails
end MinimalChoice.SmallFragments
