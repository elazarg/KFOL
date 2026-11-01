/- A tractable operation containing two distinct raw owners. Guard syntax
is independent of the observer; the observer determines its excluded atoms. -/
import OwnerFragments
set_option autoImplicit false
namespace MinimalChoice.ChainGuards
open ResetCalculus OwnerFragments
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def G {α : Type} (a b : α) (X Y Z : S α) : S α :=
  reset (own a (own b Y Z) Y) X

/-- The two-owner expression is just a selective reset, with a symmetric
set of two blocking atoms. No test depends on Z. -/
theorem selective_inner {α : Type} (a b : α) (hab : a ≠ b)
    (Y Z : S α) (hy : NE Y) (hz : NE Z) :
    own a (own b Y Z) Y =
      (if Y = atom a ∨ Y = atom b then Y else join Y Z) := by
  classical
  by_cases ha : Y = atom a
  · subst Y
    simp [own, atom_inj, hab]
  · by_cases hb : Y = atom b
    · subst Y
      simp [own, atom_inj, Ne.symm hab]
    · have hn : own b Y Z ≠ atom a := by
        intro he
        exact ha ((own_eq_other_iff b a (Ne.symm hab) Y Z hy hz).mp he).1
      have hout : own a (own b Y Z) Y = join (own b Y Z) Y :=
        ite_eq_right (not_or.mpr ⟨hn, ha⟩)
      rw [hout]
      simp only [ha, hb, or_self, ↓reduceIte]
      by_cases hz' : Z = atom b
      · subst Z
        funext k
        simp [own, join, or_comm]
      · simp only [own, hb, hz', or_self, ↓reduceIte]
        funext k
        apply propext
        simp only [join]
        grind

def Clear {α : Type} (a b k : α) (Y : S α) : Prop :=
  (k = a ∨ Y ≠ atom a) ∧ (k = b ∨ Y ≠ atom b)

theorem G_membership {α : Type} (a b k : α) (hab : a ≠ b)
    (X Y Z : S α) (hy : NE Y) (hz : NE Z) :
    G a b X Y Z k ↔ X k ∨ (Multiple X ∧ (Y k ∨ (Clear a b k Y ∧ Z k))) := by
  have ya : Y k → k ≠ a → Y ≠ atom a := by
    intro h hn he; rw [he] at h; exact hn h
  have yb : Y k → k ≠ b → Y ≠ atom b := by
    intro h hn he; rw [he] at h; exact hn h
  have za : Z k → k ≠ a → Z ≠ atom a := by
    intro h hn he; rw [he] at h; exact hn h
  have zb : Z k → k ≠ b → Z ≠ atom b := by
    intro h hn he; rw [he] at h; exact hn h
  have innerN : Y ≠ atom a → own b Y Z ≠ atom a := by
    intro hn he
    exact hn ((own_eq_other_iff b a (Ne.symm hab) Y Z hy hz).mp he).1
  by_cases hka : k = a
  · subst k
    simp only [G, reset_membership, own_mem_owner,
      own_mem_other b a (Ne.symm hab), Clear]
    grind
  · by_cases hkb : k = b
    · subst k
      simp only [G, reset_membership, own_mem_other a b hab, own_mem_owner,
        Clear]
      grind
    · simp only [G, reset_membership, own_mem_other a k (Ne.symm hka),
        own_mem_other b k (Ne.symm hkb),
        Clear]
      grind

inductive Term (β : Type) where
  | input : β → Term β
  | reset : Term β → Term β → Term β
  | g : Term β → Term β → Term β → Term β

def Term.root {β : Type} : Term β → β
  | .input j => j
  | .reset _ y => y.root
  | .g x _ _ => x.root

noncomputable def Term.denote {α β : Type} (a b : α) (v : β → S α) : Term β → S α
  | .input j => v j
  | .reset x y => ResetCalculus.reset (x.denote a b v) (y.denote a b v)
  | .g x y z => G a b (x.denote a b v) (y.denote a b v) (z.denote a b v)

theorem Term.nonempty {α β : Type} (t : Term β) (a b : α) (v : β → S α)
    (hv : ∀ j, NE (v j)) : NE (t.denote a b v) := by
  induction t with
  | input j => exact hv j
  | reset x y _ hy => exact reset_ne _ _ hy
  | g x y z hx _ _ => exact reset_ne _ _ hx

theorem Term.many {α β : Type} (t : Term β) (a b : α) (v : β → S α) :
    Multiple (t.denote a b v) ↔ Multiple (v t.root) := by
  induction t with
  | input j => rfl
  | reset x y _ hy => exact (reset_multiple _ _).trans hy
  | g x y z hx _ _ => exact (reset_multiple _ _).trans hx

theorem Term.atom {α β : Type} (t : Term β) (a b r : α) (v : β → S α) :
    t.denote a b v = MinimalChoice.atom r ↔ v t.root = MinimalChoice.atom r := by
  induction t with
  | input j => rfl
  | reset x y _ hy => exact (reset_eq_atom _ _ r).trans hy
  | g x y z hx _ _ => exact (reset_eq_atom _ _ r).trans hx

theorem Term.clear {α β : Type} (t : Term β) (a b k : α) (v : β → S α) :
    Clear a b k (t.denote a b v) ↔ Clear a b k (v t.root) := by
  have ha := t.atom a b a v
  have hb := t.atom a b b v
  unfold Clear
  grind

def Term.guards {β : Type} : Term β → List (Guard β)
  | .input j => [⟨j, [], []⟩]
  | .reset x y => y.guards ++ x.guards.map (Guard.addMany y.root)
  | .g x y z => x.guards ++ (y.guards ++
      z.guards.map (Guard.addOutside y.root)).map (Guard.addMany x.root)

theorem Term.guard_semantics {α β : Type} (t : Term β) (a b k : α) (hab : a ≠ b)
    (v : β → S α) (hv : ∀ j, NE (v j)) :
    t.denote a b v k ↔ Eval t.guards (fun j => Multiple (v j))
      (fun j => Clear a b k (v j)) (fun j => v j k) := by
  induction t with
  | input j => simp [denote, guards, Eval, Guard.Holds]
  | reset x y hx hy =>
    simp only [denote, guards, reset_membership, eval_append, eval_many, hx, hy, Term.many]
  | g x y z hx hy hz =>
    simp only [denote, guards, G_membership a b k hab _ _ _ (y.nonempty a b v hv)
      (z.nonempty a b v hv), eval_append, eval_many, eval_outside, hx, hy, hz,
      Term.many, Term.clear]

theorem clear_of_many {α : Type} (a b k : α) (Y : S α) (h : Multiple Y) : Clear a b k Y :=
  ⟨Or.inr (fun he => not_multiple_atom a (he ▸ h)),
    Or.inr (fun he => not_multiple_atom b (he ▸ h))⟩

theorem clear_of_mem {α : Type} (a b k : α) (Y : S α) (h : Y k) : Clear a b k Y := by
  classical
  constructor
  · by_cases he : k = a
    · exact Or.inl he
    · exact Or.inr (by intro hh; rw [hh] at h; exact he h)
  · by_cases he : k = b
    · exact Or.inl he
    · exact Or.inr (by intro hh; rw [hh] at h; exact he h)

/-- Testing just owner a is complete for all winner-set equations. -/
theorem Term.equation_iff {α β : Type} (three : Three α) (a b : α) (hab : a ≠ b)
    (s t : Term β) :
    (∀ v, (∀ j, NE (v j)) → s.denote a b v = t.denote a b v) ↔
      Covers s.guards t.guards ∧ Covers t.guards s.guards := by
  obtain ⟨c, hca, hcb⟩ := third_outside (three_others three) a b
  have eqObs (left right : Term β) : Covers left.guards right.guards ↔
      ∀ v, (∀ j, NE (v j)) → left.denote a b v a → right.denote a b v a := by
    rw [covers_iff a b c hab (Ne.symm hca) (Ne.symm hcb)]
    have sem (u : Term β) (v : β → S α) (hv : ∀ j, NE (v j)) :
        u.denote a b v a ↔ Eval u.guards (fun j => Multiple (v j))
          (fun j => v j ≠ MinimalChoice.atom b) (fun j => v j a) := by
      simpa [Clear, hab] using u.guard_semantics a b a hab v hv
    constructor
    · intro h v hv hu
      exact (sem right v hv).mpr (h v hv ((sem left v hv).mp hu))
    · intro h v hv hu
      exact (sem right v hv).mp (h v hv ((sem left v hv).mpr hu))
  constructor
  · intro he
    exact ⟨(eqObs s t).mpr (fun v hv h => he v hv ▸ h),
      (eqObs t s).mpr (fun v hv h => (he v hv).symm ▸ h)⟩
  · rintro ⟨hst, hts⟩ v hv
    funext k
    apply propext
    rw [s.guard_semantics a b k hab v hv, t.guard_semantics a b k hab v hv]
    exact ⟨covers_sound _ _ hst _ _ _ (fun j => clear_of_many a b k (v j))
      (fun j => clear_of_mem a b k (v j)),
      covers_sound _ _ hts _ _ _ (fun j => clear_of_many a b k (v j))
      (fun j => clear_of_mem a b k (v j))⟩

def Term.equationB {β : Type} [DecidableEq β] (s t : Term β) : Bool :=
  coversB s.guards t.guards && coversB t.guards s.guards

theorem Term.equationB_correct {α β : Type} [DecidableEq β]
    (three : Three α) (a b : α) (hab : a ≠ b) (s t : Term β) :
    s.equationB t = true ↔ ∀ v, (∀ j, NE (v j)) → s.denote a b v = t.denote a b v := by
  rw [s.equation_iff three a b hab t]
  simp [equationB, Bool.and_eq_true, coversB_correct]

def Term.leaves {β : Type} : Term β → Nat
  | .input _ => 1
  | .reset x y => x.leaves + y.leaves
  | .g x y z => x.leaves + (y.leaves + z.leaves)

theorem Term.guards_length {β : Type} (t : Term β) : t.guards.length = t.leaves := by
  induction t with
  | input j => rfl
  | reset x y hx hy => simp [guards, leaves, hx, hy, Nat.add_comm]
  | g x y z hx hy hz => simp [guards, leaves, hx, hy, hz]

/- The same calculus works for any one nonempty proper set of blocking
atoms. No cardinality or number of named owners occurs in its guards. -/
noncomputable def policy {α : Type} (D : α → Prop) (X Y Z : S α) : S α :=
  reset (if ∃ r, D r ∧ Y = atom r then Y else join Y Z) X

def ClearPolicy {α : Type} (D : α → Prop) (k : α) (Y : S α) : Prop :=
  ∀ r, D r → k = r ∨ Y ≠ atom r

theorem policy_many {α : Type} (D : α → Prop) (X Y Z : S α) :
    Multiple (policy D X Y Z) ↔ Multiple X := reset_multiple _ _

theorem clearPolicy_many {α : Type} (D : α → Prop) (k : α) (Y : S α)
    (h : Multiple Y) : ClearPolicy D k Y :=
  fun r _ => Or.inr (fun he => not_multiple_atom r (he ▸ h))

theorem clearPolicy_mem {α : Type} (D : α → Prop) (k : α) (Y : S α)
    (h : Y k) : ClearPolicy D k Y := by
  intro r _
  by_cases hr : k = r
  · exact Or.inl hr
  · exact Or.inr (by intro he; rw [he] at h; exact hr h)

theorem policy_membership {α : Type} (D : α → Prop) (k : α) (X Y Z : S α) :
    policy D X Y Z k ↔ X k ∨ (Multiple X ∧ (Y k ∨ (ClearPolicy D k Y ∧ Z k))) := by
  by_cases he : ∃ r, D r ∧ Y = atom r
  · obtain ⟨r, hdr, hY⟩ := he
    have hc : ClearPolicy D k Y → Y k := by
      intro h
      rcases h r hdr with hk | hn
      · rw [hY, hk]; rfl
      · exact False.elim (hn hY)
    have he : ∃ r, D r ∧ Y = atom r := ⟨r, hdr, hY⟩
    simp only [policy, ite_eq_left he, reset_membership]
    grind
  · have hc : ClearPolicy D k Y := by
      intro r hr
      exact Or.inr (fun hh => he ⟨r, hr, hh⟩)
    simp only [policy, ite_eq_right he, reset_membership, join, hc, true_and]

noncomputable def Term.denotePolicy {α β : Type} (D : α → Prop) (v : β → S α) : Term β → S α
  | .input j => v j
  | .reset x y => ResetCalculus.reset (x.denotePolicy D v) (y.denotePolicy D v)
  | .g x y z => policy D (x.denotePolicy D v) (y.denotePolicy D v) (z.denotePolicy D v)

theorem Term.policy_many {α β : Type} (t : Term β) (D : α → Prop) (v : β → S α) :
    Multiple (t.denotePolicy D v) ↔ Multiple (v t.root) := by
  induction t with
  | input j => rfl
  | reset x y _ hy => exact (reset_multiple _ _).trans hy
  | g x y z hx _ _ => exact (MinimalChoice.ChainGuards.policy_many _ _ _ _).trans hx

theorem Term.policy_atom {α β : Type} (t : Term β) (D : α → Prop) (v : β → S α) (r : α) :
    t.denotePolicy D v = MinimalChoice.atom r ↔ v t.root = MinimalChoice.atom r := by
  induction t with
  | input j => rfl
  | reset x y _ hy => exact (reset_eq_atom _ _ r).trans hy
  | g x y z hx _ _ => exact (reset_eq_atom _ _ r).trans hx

theorem Term.policy_clear {α β : Type} (t : Term β) (D : α → Prop) (k : α) (v : β → S α) :
    ClearPolicy D k (t.denotePolicy D v) ↔ ClearPolicy D k (v t.root) := by
  constructor <;> intro h r hr
  · rcases h r hr with hk | hn
    · exact Or.inl hk
    · exact Or.inr (fun he => hn ((t.policy_atom D v r).mpr he))
  · rcases h r hr with hk | hn
    · exact Or.inl hk
    · exact Or.inr (fun he => hn ((t.policy_atom D v r).mp he))

theorem Term.policy_guard_semantics {α β : Type} (t : Term β) (D : α → Prop) (k : α)
    (v : β → S α) :
    t.denotePolicy D v k ↔ Eval t.guards (fun j => Multiple (v j))
      (fun j => ClearPolicy D k (v j)) (fun j => v j k) := by
  induction t with
  | input j => simp [denotePolicy, guards, Eval, Guard.Holds]
  | reset x y hx hy =>
    simp only [denotePolicy, guards, reset_membership, eval_append, eval_many, hx, hy, Term.policy_many]
  | g x y z hx hy hz =>
    simp only [denotePolicy, guards, policy_membership, eval_append, eval_many,
      eval_outside, hx, hy, hz, Term.policy_many, Term.policy_clear]

theorem clearPolicy_atom {α : Type} (D : α → Prop) (k u : α) :
    ClearPolicy D k (atom u) ↔ (D u → k = u) := by
  constructor
  · intro h hu
    rcases h u hu with he | hn
    · exact he
    · exact False.elim (hn rfl)
  · intro h r hr
    by_cases he : u = r
    · subst r; exact Or.inl (h hr)
    · exact Or.inr (fun hh => he (atom_inj.mp hh))

theorem policy_minimal {α β : Type} (D : α → Prop) (k r c : α)
    (hkr : k ≠ r) (hkc : k ≠ c) (hr : D r) (hc : ¬ D c) (g : Guard β) (j : β) :
    ClearPolicy D k (minimalVal k r c g j) ↔ minimalVal k r c g j ≠ atom r := by
  have hrc : r ≠ c := by intro he; exact hc (he ▸ hr)
  have hm1 := (pair_multiple k r).mpr hkr
  have hm2 := (pair_multiple r c).mpr hrc
  have hp1 := clearPolicy_many D k _ hm1
  have hp2 := clearPolicy_many D k _ hm2
  have hn1 : join (atom k) (atom r) ≠ atom r := fun he => not_multiple_atom r (he ▸ hm1)
  have hn2 : join (atom r) (atom c) ≠ atom r := fun he => not_multiple_atom r (he ▸ hm2)
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;>
    by_cases ho : j ∈ g.outside <;>
    simp_all [minimalVal, clearPolicy_atom, atom_inj, Ne.symm hrc]

theorem covers_policy_iff {α β : Type} (D : α → Prop) (k r c : α)
    (hkr : k ≠ r) (hkc : k ≠ c) (hr : D r) (hc : ¬ D c)
    (left right : List (Guard β)) :
    Covers left right ↔ ∀ v : β → S α, (∀ j, NE (v j)) →
      Eval left (fun j => Multiple (v j)) (fun j => ClearPolicy D k (v j)) (fun j => v j k) →
      Eval right (fun j => Multiple (v j)) (fun j => ClearPolicy D k (v j)) (fun j => v j k) := by
  constructor
  · intro h v _
    exact covers_sound _ _ h _ _ _ (fun j => clearPolicy_many D k (v j))
      (fun j => clearPolicy_mem D k (v j))
  · intro h g hg
    have hrc : r ≠ c := by intro he; exact hc (he ▸ hr)
    let v := minimalVal k r c g
    have hn : (fun j => ClearPolicy D k (v j)) = (fun j => v j ≠ atom r) := by
      funext j
      exact propext (policy_minimal D k r c hkr hkc hr hc g j)
    have hl : Eval left (fun j => Multiple (v j)) (fun j => ClearPolicy D k (v j))
        (fun j => v j k) := by
      rw [hn]
      apply (eval_minimalVal k r c hkr hkc hrc g left).mpr
      exact ⟨g, hg, rfl, (fun _ hh => hh), fun _ hh => Or.inr (Or.inl hh)⟩
    have hh := h v (minimalVal_ne k r c g) hl
    rw [hn] at hh
    exact (eval_minimalVal k r c hkr hkc hrc g right).mp hh

/-- Every one nonempty proper blocking policy has exactly the same
equations, decided by the same guard checker. -/
theorem Term.policy_equation_iff {α β : Type} (three : Three α)
    (D : α → Prop) (hd : ∃ r, D r) (hp : ∃ c, ¬ D c) (s t : Term β) :
    (∀ v, (∀ j, NE (v j)) → s.denotePolicy D v = t.denotePolicy D v) ↔
      Covers s.guards t.guards ∧ Covers t.guards s.guards := by
  obtain ⟨r, hr⟩ := hd
  obtain ⟨c, hc⟩ := hp
  obtain ⟨k, hkr, hkc⟩ := third_outside (three_others three) r c
  have obs (left right : Term β) : Covers left.guards right.guards ↔
      ∀ v, (∀ j, NE (v j)) → left.denotePolicy D v k → right.denotePolicy D v k := by
    rw [covers_policy_iff D k r c hkr hkc hr hc]
    simp only [← left.policy_guard_semantics D k, ← right.policy_guard_semantics D k]
  constructor
  · intro he
    exact ⟨(obs s t).mpr (fun v hv h => he v hv ▸ h),
      (obs t s).mpr (fun v hv h => (he v hv).symm ▸ h)⟩
  · rintro ⟨hst, hts⟩ v _
    funext i
    apply propext
    rw [s.policy_guard_semantics D i, t.policy_guard_semantics D i]
    exact ⟨covers_sound _ _ hst _ _ _ (fun j => clearPolicy_many D i (v j))
      (fun j => clearPolicy_mem D i (v j)),
      covers_sound _ _ hts _ _ _ (fun j => clearPolicy_many D i (v j))
      (fun j => clearPolicy_mem D i (v j))⟩

theorem Term.policy_checker_correct {α β : Type} [DecidableEq β] (three : Three α)
    (D : α → Prop) (hd : ∃ r, D r) (hp : ∃ c, ¬ D c) (s t : Term β) :
    s.equationB t = true ↔
      ∀ v, (∀ j, NE (v j)) → s.denotePolicy D v = t.denotePolicy D v := by
  rw [s.policy_equation_iff three D hd hp t]
  simp [equationB, Bool.and_eq_true, coversB_correct]

theorem G_is_policy {α : Type} (a b : α) (hab : a ≠ b) (X Y Z : S α)
    (hy : NE Y) (hz : NE Z) :
    G a b X Y Z = policy (fun r => r = a ∨ r = b) X Y Z := by
  have hp : (∃ r, (r = a ∨ r = b) ∧ Y = atom r) ↔ Y = atom a ∨ Y = atom b := by
    simp only [exists_or, exists_eq_left, or_and_right]
  simp only [G, policy, selective_inner a b hab Y Z hy hz, hp]

theorem G_owner_symmetry {α : Type} (a b : α) (hab : a ≠ b) (X Y Z : S α)
    (hy : NE Y) (hz : NE Z) : G a b X Y Z = G b a X Y Z := by
  have hd : (fun r => r = a ∨ r = b) = (fun r => r = b ∨ r = a) := by
    funext r
    exact propext Or.comm
  rw [G_is_policy a b hab X Y Z hy hz, hd, ← G_is_policy b a (Ne.symm hab) X Y Z hy hz]

theorem policy_defines_reset {α : Type} (D : α → Prop) (X Y : S α) :
    policy D Y X X = reset X Y := by
  unfold policy
  split
  · rfl
  · have he : join X X = X := by funext k; exact propext ⟨fun h => h.elim id id, Or.inl⟩
    rw [he]

theorem policy_all {α : Type} (X Y Z : S α) (hy : NE Y) :
    policy (fun _ => True) X Y Z = reset (reset Z Y) X := by
  rcases atom_or_multiple Y hy with ⟨r, hr⟩ | hm
  · subst Y
    have he : ∃ r', True ∧ atom r = atom r' := ⟨r, True.intro, rfl⟩
    simp only [policy, ite_eq_left he, reset, not_multiple_atom, ite_false]
  · have he : ¬ ∃ r, True ∧ Y = atom r := by
      rintro ⟨r, _, hr⟩
      exact not_multiple_atom r (hr ▸ hm)
    simp only [policy, ite_eq_right he, reset, hm, ite_true]
    have hjoin : join Y Z = join Z Y := by funext k; exact propext Or.comm
    rw [hjoin]

theorem policy_none {α : Type} (X Y Z : S α) :
    policy (fun _ => False) X Y Z = reset (reset Y X) (reset Z X) := by
  have he : ¬ ∃ r, False ∧ Y = atom r := by simp
  simp only [policy, ite_eq_right he]
  funext k
  apply propext
  simp only [reset_membership, reset_multiple, join]
  grind

end MinimalChoice.ChainGuards
#print axioms MinimalChoice.ChainGuards.G_membership
#print axioms MinimalChoice.ChainGuards.Term.equation_iff
#print axioms MinimalChoice.ChainGuards.Term.equationB_correct
#print axioms MinimalChoice.ChainGuards.Term.policy_equation_iff
#print axioms MinimalChoice.ChainGuards.Term.policy_checker_correct
