module

public import KFOL.Core.MonochromaticCutObstruction
public import KFOL.Core.SingletonProfileAbsorption

/-! # Independent adoption tests at one register

The input family is an antichain of posting sets. A test for its member
`T` has a simultaneous core witness precisely when the corresponding
negative head row has already been discharged.
-/

@[expose] public section

namespace KFOL.Core.OfferHistory

open MonochromaticCutObstruction (pureProbe pure_atom)
attribute [local instance] Equational.coreStructure

abbrev Word (Role V : Type*) := Equational.Term (Equational.CoreSymbol Role) V

/-- A loss with just one posting color. -/
structure Loss (Role V : Type*) where
  head : V
  owner : Role
  tail : V → Bool

variable {Role D V : Type*} [DecidableEq Role] [DecidableEq D]

def Quiet (three : Fin 3 ↪ Role) (q : Loss Role V) (t : Word Role V) : Prop :=
  ∀ k (ne : q.owner ≠ k), k ∉ (t.realize (pureProbe three k q.head q.owner ne q.tail)).val

omit [DecidableEq Role] in
private theorem var_quiet (three : Fin 3 ↪ Role) (q : Loss Role V) {x : V}
    (ne : x ≠ q.head) : Quiet three q (.var x) := by
  intro k other hm
  change k ∈ (pureProbe three k q.head q.owner other q.tail x).val at hm
  unfold pureProbe at hm
  exact ne ((Sources.mem_probe_iff three k q.head _ x).mp hm)

omit [DecidableEq Role] in
private theorem choice_quiet (three : Fin 3 ↪ Role) (q : Loss Role V) {a b : Word Role V}
    (u : Role) (ha : Quiet three q a) (hb : Quiet three q b) : Quiet three q (choiceTerm u a b) :=
  fun k ne hm => (WinnerSet.choice_subset_union u _ _ hm).elim (ha k ne) (hb k ne)

/-- An owner win at a monochromatic row discharges its mark at every observer. -/
private theorem quiet_of_win (three : Fin 3 ↪ Role) (q : Loss Role V) (t : Word Role V)
    (off : q.tail q.head = false) (win : profile q.owner q.tail t = true) : Quiet three q t := by
  intro k ne
  rw [(pure_atom three k t q.head q.owner ne q.owner q.tail off ne).mpr ⟨rfl, win⟩]
  exact fun h => ne h.symm

private theorem conflicting {r s : Role} (hrs : r ≠ s) {A B : V → Bool}
    (disj : ∀ x, A x = true → B x = true → False) (t : Word Role V)
    (ar : profile r A t = true) (bs : profile s B t = true) : False := by
  let owners : Bool → Role := fun b => if b then s else r
  let sets : Bool → V → Bool := fun b => if b then B else A
  have inj : Function.Injective owners := by
    intro i j e
    cases i <;> cases j <;> simp_all [owners, Ne.symm hrs]
  obtain ⟨x, hx⟩ := profile_common_source owners inj sets t (by
    intro i
    cases i <;> assumption)
  exact disj x (hx false) (hx true)

private theorem head_forces_tail [DecidableEq V] (three : Fin 3 ↪ Role) (q : Loss Role V)
    (t : Word Role V) (k : Role) (other : q.owner ≠ k) (off : q.tail q.head = false)
    (head : profile q.owner (fun x => decide (x = q.head)) t = true) (quiet : Quiet three q t) :
    profile q.owner q.tail t = true := by
  let values := pureProbe three k q.head q.owner other q.tail
  rcases eq_singleton_or_subset_of_profile_singleton t q.owner q.head values head with atom | sub
  · exact ((pure_atom three k t q.head q.owner other q.owner q.tail off other).mp atom).2
  · exact (quiet k other (sub ((Sources.mem_probe_iff three k q.head _ q.head).mpr rfl))).elim

/-- Data inputs, the marked head, the dummy head carrying the next offers,
and three inputs supporting a mixed-owner word. -/
inductive Input (D : Type*) where
  | data (x : D) | h | j | u | v | w
  deriving DecidableEq

open Input

def onData (T : Finset D) : Input D → Bool
  | .data x => decide (x ∈ T)
  | _ => false

/-- The coalition posted in the foreign offer indexed by `T`. -/
def opposite (T : Finset D) : Input D → Bool
  | .data x => decide (x ∉ T)
  | .j => false
  | _ => true

def anchors : Input D → Bool
  | .u | .v | .w => true
  | _ => false

def others (x : D) : Input D → Bool
  | .data y => decide (y ≠ x)
  | _ => false

def atOne (a : Input D) (b : Input D) : Bool := decide (b = a)

def atPair (a b : Input D) (i : Input D) : Bool := decide (i = a ∨ i = b)

/-- All nondummy rows retained before the next foreign adoption. The witness
also obeys any monochromatic dummy row, including those already discharged. -/
inductive Row (r s : Role) (R : Finset (Finset D)) : Loss Role (Input D) → Prop where
  | head {L} (mem : L ∈ R) : Row r s R ⟨.h, r, onData L⟩
  | dummy (q : Role) (A : Input D → Bool) : Row r s R ⟨.j, q, A⟩
  | dataR (x : D) : Row r s R ⟨.data x, r, anchors⟩
  | dataS (x : D) : Row r s R ⟨.data x, s, others x⟩
  | uR : Row r s R ⟨.u, r, atOne .v⟩
  | uS : Row r s R ⟨.u, s, atOne .w⟩
  | vR : Row r s R ⟨.v, r, atOne .u⟩
  | vS : Row r s R ⟨.v, s, atOne .w⟩
  | wS : Row r s R ⟨.w, s, atPair .u .v⟩

private def guard (r s : Role) : Word Role (Input D) :=
  choiceTerm s (choiceTerm r (.var .u) (.var .v)) (.var .w)

omit [DecidableEq Role] in
private theorem fold_quiet (three : Fin 3 ↪ Role) (q : Loss Role V) (r : Role)
    (xs : List (Word Role V)) (z : Word Role V) (hz : Quiet three q z)
    (hx : ∀ x ∈ xs, Quiet three q x) : Quiet three q (foldTerm r xs z) := by
  induction xs with
  | nil => exact hz
  | cons a l ih =>
    exact choice_quiet three q r (hx _ List.mem_cons_self)
      (ih (fun b hb => hx b (List.mem_cons_of_mem a hb)))

private noncomputable def inner (s : Role) (L : Finset D) (nonempty : L.Nonempty) :
    Word Role (Input D) :=
  foldTerm s (L.toList.map fun i => .var (.data i)) (.var (.data nonempty.choose))

omit [DecidableEq D] in
private theorem inner_owner (s : Role) (L : Finset D) (hL : L.Nonempty) (A : Input D → Bool) :
    profile s A (inner s L hL) = true ↔ ∃ i ∈ L, A (.data i) = true := by
  rw [inner, profile_fold_owner]
  simp only [profile_var, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and]
  exact ⟨fun h => h.elim (fun e => ⟨_, hL.choose_spec, e⟩) id, Or.inr⟩

omit [DecidableEq D] in
private theorem inner_other (s r : Role) (ne : s ≠ r) (L : Finset D) (hL : L.Nonempty)
    (A : Input D → Bool) :
    profile r A (inner s L hL) = true ↔ ∀ i ∈ L, A (.data i) = true := by
  rw [inner, profile_fold_other s r ne]
  simp only [profile_var, List.forall_mem_map, Finset.mem_toList]
  exact ⟨And.right, fun h => ⟨h _ hL.choose_spec, h⟩⟩

omit [DecidableEq D] [DecidableEq Role] in
private theorem inner_quiet (three : Fin 3 ↪ Role) (q : Loss Role (Input D)) (s : Role)
    (L : Finset D) (hL : L.Nonempty) (away : ∀ i ∈ L, Input.data i ≠ q.head) :
    Quiet three q (inner s L hL) := by
  apply fold_quiet three q s _ _ (var_quiet three q (away _ hL.choose_spec))
  simpa only [List.forall_mem_map, Finset.mem_toList] using
    fun i hi => var_quiet three q (away i hi)

omit [DecidableEq D] [DecidableEq Role] in
private theorem guard_quiet (three : Fin 3 ↪ Role) (q : Loss Role (Input D)) (r s : Role)
    (u : Input.u ≠ q.head) (v : Input.v ≠ q.head) (w : Input.w ≠ q.head) :
    Quiet three q (guard r s) :=
  choice_quiet three q s (choice_quiet three q r (var_quiet three q u) (var_quiet three q v))
    (var_quiet three q w)

private noncomputable def operands (s : Role) (R : Finset (Finset D))
    (large : ∀ L ∈ R, 1 < L.card) : List (Word Role (Input D)) :=
  R.attach.toList.map fun L => inner s L.val (Finset.card_pos.mp (by have := large _ L.property; omega))

private noncomputable def witness (r s : Role) (R : Finset (Finset D))
    (large : ∀ L ∈ R, 1 < L.card) : Word Role (Input D) :=
  foldTerm r (operands s R large) (choiceTerm r (.var .h) (guard r s))

variable (three : Fin 3 ↪ Role) (r s : Role) (hrs : r ≠ s) (R : Finset (Finset D))
  (large : ∀ L ∈ R, 1 < L.card)

include hrs in
omit [DecidableEq D] in
private theorem witness_owner (A : Input D → Bool) :
    profile r A (witness r s R large) = true ↔
      A .h = true ∨ profile r A (guard r s) = true ∨
      ∃ L ∈ R, ∀ i ∈ L, A (.data i) = true := by
  classical
  simp only [witness, profile_fold_owner, profile_choice, ite_true, Bool.or_eq_true,
    profile_var, or_assoc]
  apply or_congr Iff.rfl (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨z, mem, yes⟩
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp mem
    exact ⟨_, L.property, (inner_other s r hrs.symm _ _ _).mp yes⟩
  · rintro ⟨L, hL, all⟩
    let l : {l // l ∈ R} := ⟨L, hL⟩
    refine ⟨_, List.mem_map.mpr ⟨l, by simp, rfl⟩, ?_⟩
    exact (inner_other s r hrs.symm _ _ _).mpr all

include hrs in
omit [DecidableEq D] in
private theorem witness_foreign (A : Input D → Bool) :
    profile s A (witness r s R large) = true ↔
      A .h = true ∧ profile s A (guard r s) = true ∧
      ∀ L ∈ R, ∃ i ∈ L, A (.data i) = true := by
  classical
  simp only [witness, profile_fold_other r s hrs, profile_choice, hrs, ite_false, Bool.and_eq_true,
    profile_var, operands, List.forall_mem_map, Finset.mem_toList, Finset.mem_attach, true_implies,
    inner_owner, Subtype.forall, and_assoc]

omit [DecidableEq D] [DecidableEq Role] in
private theorem witness_quiet_of_operands (q : Loss Role (Input D))
    (h : Input.h ≠ q.head) (g : Quiet three q (guard r s))
    (each : ∀ L ∈ R, ∀ hL : L.Nonempty, Quiet three q (inner s L hL)) :
    Quiet three q (witness r s R large) := by
  apply fold_quiet three q r _ _ (choice_quiet three q r (var_quiet three q h) g)
  simp only [operands, List.forall_mem_map, Finset.mem_toList, Finset.mem_attach, true_implies]
  intro L
  exact each _ L.property _

include hrs in
private theorem witness_quiet (q : Loss Role (Input D)) (row : Row r s R q) :
    Quiet three q (witness r s R large) := by
  cases row with
  | head mem =>
    apply quiet_of_win three _ _ rfl
    exact (witness_owner r s hrs R large _).mpr (Or.inr (Or.inr ⟨_, mem, fun _ hi =>
      decide_eq_true hi⟩))
  | dummy owner A =>
    apply witness_quiet_of_operands three r s R large _ (by simp)
      (guard_quiet three _ r s (by simp) (by simp) (by simp))
    exact fun L _ hL => inner_quiet three _ s L hL (fun _ _ => by simp)
  | dataR x =>
    apply quiet_of_win three _ _ rfl
    apply (witness_owner r s hrs R large _).mpr
    apply Or.inr (Or.inl ?_)
    simp [guard, profile_choice, hrs.symm, anchors]
  | dataS x =>
    apply witness_quiet_of_operands three r s R large _ (by simp)
      (guard_quiet three _ r s (by simp) (by simp) (by simp))
    intro L mem hL
    apply quiet_of_win three _ _ (by simp [others])
    apply (inner_owner s L hL _).mpr
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (large L mem)
    by_cases e : i = x
    · exact ⟨j, hj, decide_eq_true (fun he => hij (e.trans he.symm))⟩
    · exact ⟨i, hi, decide_eq_true e⟩
  | uR | uS | vR | vS | wS =>
    apply witness_quiet_of_operands three r s R large _ (by simp) ?_
      (fun L _ hL => inner_quiet three _ s L hL (fun _ _ => by simp))
    first
    | solve
      | apply quiet_of_win three _ _ (by rfl)
        simp [guard, profile_choice, hrs, hrs.symm, atOne, atPair]
    | apply choice_quiet three _ s _ (var_quiet three _ (by simp))
      apply quiet_of_win three _ _ (by rfl)
      simp [profile_choice, atOne]

include hrs large in
/-- The same word witnesses each prescribed prefix offer and the adoption
of the head singleton, even before the associated rows are removed. -/
theorem prefix_witness :
    ∃ t : Word Role (Input D), profile r (atOne .h) t = true ∧
      (∀ L ∈ R, profile r (onData L) t = true) ∧
      ∀ q, Row r s R q → Quiet three q t := by
  refine ⟨witness r s R large, (witness_owner r s hrs R large _).mpr (Or.inl (by simp [atOne])),
    ?_, witness_quiet three r s hrs R large⟩
  intro L mem
  exact (witness_owner r s hrs R large _).mpr (Or.inr (Or.inr ⟨_, mem, fun _ hi =>
    decide_eq_true hi⟩))

include hrs large in
/-- A surviving head row is the only possible obstruction to a foreign
adoption. The two hypotheses on `active` also allow rows deleted by that
adoption to be omitted. -/
theorem adoption_iff_removed (T : Finset D)
    (separate : ∀ L ∈ R, L ≠ T → ¬ L ⊆ T)
    (active : Loss Role (Input D) → Prop)
    (lower : T ∈ R → active ⟨.h, r, onData T⟩)
    (upper : ∀ q, active q → Row r s R q) :
    (∃ t : Word Role (Input D), profile r (atOne .h) t = true ∧
      profile s (opposite T) t = true ∧ ∀ q, active q → Quiet three q t) ↔ T ∉ R := by
  constructor
  · rintro ⟨t, head, foreign, quiet⟩ retained
    have force := head_forces_tail three (⟨.h, r, onData T⟩ : Loss Role (Input D)) t s hrs rfl head
      (quiet _ (lower retained))
    apply conflicting hrs (A := onData T) (B := opposite T) _ t force foreign
    intro x a b
    cases x <;> simp_all [onData, opposite]
  · intro gone
    refine ⟨witness r s R large, (witness_owner r s hrs R large _).mpr (Or.inl (by simp [atOne])),
      (witness_foreign r s hrs R large _).mpr ⟨rfl, ?_, ?_⟩,
      fun q hq => witness_quiet three r s hrs R large q (upper q hq)⟩
    · simp [guard, profile_choice, hrs, opposite]
    · intro L hL
      obtain ⟨i, hi, no⟩ := Finset.not_subset.mp (separate L hL (fun e => gone (e ▸ hL)))
      exact ⟨_, hi, decide_eq_true no⟩

/-- A summary capable of answering all these tests distinguishes all residual
subfamilies. The summary type and its decision rule are arbitrary. -/
theorem summary_injective {State : Type*} (family : Finset (Finset D))
    (summarize : {R : Finset (Finset D) // R ⊆ family} → State)
    (ask : State → Finset D → Prop)
    (correct : ∀ R T, T ∈ family → (ask (summarize R) T ↔ T ∉ R.val)) :
    Function.Injective summarize := by
  intro R Q e
  apply Subtype.ext
  ext T
  by_cases inFamily : T ∈ family
  · exact not_iff_not.mp ((correct R T inFamily).symm.trans (e ▸ correct Q T inFamily))
  · exact iff_of_false (fun h => inFamily (R.property h)) (fun h => inFamily (Q.property h))

end KFOL.Core.OfferHistory
