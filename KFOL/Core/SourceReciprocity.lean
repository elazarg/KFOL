module

public import KFOL.Core.SourceProbes
public import KFOL.Algebra.Atomic.CoreSupport
public import KFOL.Core.CompletionDepthErasure

/-! # Captured sources and reciprocal losses

A false source probe removes that variable from the whole cofactor obtained
by fixing the posted atoms. In a binary operation, opposite losses therefore
require the same posting color.
-/

@[expose] public section
namespace KFOL.Core.Sources

variable {Role Var : Type*}

private theorem singleton_persists {t : Term Role Var} (ht : t.IsPublic) (r : Role)
    {v w : Var → WinnerSet Role} (h : ∀ i, v i = WinnerSet.singleton r →
      w i = WinnerSet.singleton r) (hv : t.eval v = WinnerSet.singleton r) :
    t.eval w = WinnerSet.singleton r := by
  induction t with
  | var i => exact h i hv
  | winner => exact hv
  | rename => exact ht.elim
  | choice s a b ha hb =>
    by_cases hs : s = r
    · subst s
      exact (WinnerSet.choice_eq_owner_iff _ _ r).2
        (((WinnerSet.choice_eq_owner_iff _ _ r).1 hv).imp (ha ht.1) (hb ht.2))
    · obtain ⟨hx, hy⟩ := (WinnerSet.choice_eq_other_iff _ _ s hs).1 hv
      exact (WinnerSet.choice_eq_other_iff _ _ s hs).2 ⟨ha ht.1 hx, hb ht.2 hy⟩

/-- A source bit vanishes exactly when fixing the posted atoms makes the entire
operation independent of that input, for every choice of the remaining menus. -/
theorem probe_loss_iff_cofactor_independent (three : Fin 3 ↪ Role) (t : Term Role Var)
    (ht : t.IsCore) (k : Role) (j : Var) (p : Pattern k j) :
    k ∉ (t.eval (probe three k j p)).val ↔
      ∀ v w : Var → WinnerSet Role, (∀ i, i ≠ j → v i = w i) →
        (∀ (i : {i // i ≠ j}) r, p i = .atom r → v i.val = WinnerSet.singleton r.val) →
        t.eval v = t.eval w := by
  classical
  constructor
  · intro hloss v w hagree hfix
    have constant {u : Term Role Var} (hu : u.IsCore) {r : Role} (hr : r ≠ k)
        (hp : u.eval (probe three k j p) = WinnerSet.singleton r) :
        u.eval v = WinnerSet.singleton r ∧ u.eval w = WinnerSet.singleton r := by
      have posted (i : Var) (hi : probe three k j p i = WinnerSet.singleton r) :
          v i = WinnerSet.singleton r ∧ w i = WinnerSet.singleton r := by
        by_cases he : i = j
        · subst i
          exact (hr (WinnerSet.singleton_inj.mp (by simpa using hi)).symm).elim
        · rw [probe_other three k j p i he] at hi
          have hv := hfix ⟨i, he⟩ ⟨r, hr⟩ ((representative_atom_iff three k _ ⟨r, hr⟩).1 hi)
          exact ⟨hv, (hagree i he).symm.trans hv⟩
      exact ⟨singleton_persists hu.isPublic r (fun i hi => (posted i hi).1) hp,
        singleton_persists hu.isPublic r (fun i hi => (posted i hi).2) hp⟩
    induction t with
    | var i =>
      exact hagree i fun he => hloss ((mem_probe_iff three k j p i).2 he)
    | winner => exact ht.elim
    | rename => exact ht.elim
    | choice r a b ha hb =>
      by_cases hr : r = k
      · subst r
        have hn := not_or.mp (hloss ∘ (WinnerSet.mem_choice_owner k _ _).2)
        exact congrArg₂ (WinnerSet.choice k) (ha ht.1 hn.1) (hb ht.2 hn.2)
      · by_cases hat : a.eval (probe three k j p) = WinnerSet.singleton r ∨
            b.eval (probe three k j p) = WinnerSet.singleton r
        · rcases hat with h | h
          · obtain ⟨hv, hw⟩ := constant ht.1 hr h
            simp [Term.eval, WinnerSet.choice, hv, hw]
          · obtain ⟨hv, hw⟩ := constant ht.2 hr h
            simp [Term.eval, WinnerSet.choice, hv, hw]
        · have hn : ¬(k ∈ (a.eval (probe three k j p)).val ∨
              k ∈ (b.eval (probe three k j p)).val) := fun h =>
            hloss ((WinnerSet.mem_choice_other r k hr _ _).2 ⟨h, (not_or.mp hat).1, (not_or.mp hat).2⟩)
          exact congrArg₂ (WinnerSet.choice r) (ha ht.1 (not_or.mp hn).1) (hb ht.2 (not_or.mp hn).2)
  · intro h
    let v := probe three k j p
    let w : Var → WinnerSet Role := Function.update v j (representative three k .neutral)
    have he := h v w (fun i hi => (Function.update_of_ne hi _ _).symm) (fun i r hr => by
      change probe three k j p i.val = _
      rw [probe_other three k j p i.val i.property, hr]
      rfl)
    intro hp
    obtain ⟨i, hi, _⟩ := (membership_iff_source three t ht w k).1 (he ▸ hp)
    by_cases hi' : i = j
    · subst i
      simp [w] at hi
    · simp [w, v, hi'] at hi

/-- At two inputs, if a posting at the first kills the second, every opposite
loss posts the second input at exactly that color. The losses may have
different observers. -/
theorem binary_probe_loss_reciprocity (three : Fin 3 ↪ Role) (t : Term Role Bool)
    (ht : t.IsCore) (k l : Role) (p : Passive k) (r : {r : Role // r ≠ l})
    (hx : k ∉ (t.eval (probe three k false (fun _ => p))).val)
    (hy : l ∉ (t.eval (probe three l true (fun _ => .atom r))).val) :
    ∃ s : {s : Role // s ≠ k}, p = .atom s ∧ s.val = r.val := by
  classical
  have cx := (probe_loss_iff_cofactor_independent three t ht k false _).1 hx
  have cy := (probe_loss_iff_cofactor_independent three t ht l true _).1 hy
  have same (s : Role) (hs : ∀ a, p = .atom a → s = a.val) : s = r.val := by
    let v (b : Bool) := WinnerSet.singleton (if b then s else r.val)
    have ex := cx (fun _ => WinnerSet.singleton s) v (by
      intro i hi; cases i <;> simp_all [v]) (fun _ a ha => congrArg WinnerSet.singleton (hs a ha))
    have ey := cy (fun _ => WinnerSet.singleton r.val) v (by
      intro i hi; cases i <;> simp_all [v]) (by
      intro i a ha
      exact congrArg WinnerSet.singleton (Subtype.ext_iff.mp (Passive.atom.inj ha)))
    rw [ht.eval_eq_of_support _ _ (fun _ _ => rfl)] at ex ey
    exact WinnerSet.singleton_inj.mp (ex.trans ey.symm)
  cases p with
  | atom s => exact ⟨s, rfl, same s.val (fun a h => Subtype.ext_iff.mp (Passive.atom.inj h))⟩
  | neutral =>
    exact (r.property (same l (by simp)).symm).elim

/-- The binary reciprocity test also applies after fixing arbitrarily many
other inputs. A positive winner outside the fixed menus rules out the
constant residue. Each of the two losses may use its own observer. -/
theorem fixed_background_loss_reciprocity {Fix : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (t : Term Role (Bool ⊕ Fix)) (ht : t.IsCore)
    (fixed : Fix → WinnerSet Role)
    (positive : ∃ k : Role, (∀ j, k ∉ (fixed j).val) ∧
      ∃ v : Bool → WinnerSet Role, k ∈ (t.eval (Sum.elim v fixed)).val)
    (k l : Role)
    (p : Passive k) (r : {r : Role // r ≠ l})
    (hx : k ∉ (t.eval (Sum.elim (probe three k false (fun _ => p)) fixed)).val)
    (hy : l ∉ (t.eval (Sum.elim (probe three l true (fun _ => .atom r)) fixed)).val) :
    ∃ s : {s : Role // s ≠ k}, p = .atom s ∧ s.val = r.val := by
  classical
  let _ := Equational.coreStructure Role
  obtain ⟨e, he⟩ := CompletionDepth.Expr.exists_of_core (Equational.Core.encode t ht)
  have agrees (v : Bool ⊕ Fix → WinnerSet Role) : e.eval v = t.eval v := by
    rw [he, ← Equational.Core.eval_decode, Equational.Core.decode_encode]
  let flags (j : Fix) : Option Role :=
    if h : ∃ s, fixed j = WinnerSet.singleton s then some h.choose else none
  have hf (j : Fix) (s : Role) : fixed j = WinnerSet.singleton s ↔ flags j = some s := by
    unfold flags
    split
    next h =>
      simp only [Option.some.injEq]
      exact ⟨fun he => WinnerSet.singleton_inj.mp (h.choose_spec.symm.trans he),
        fun he => h.choose_spec.trans (congrArg WinnerSet.singleton he)⟩
    next h => simpa using fun heq => h ⟨s, heq⟩
  obtain ⟨z, _, hz⟩ := e.exists_erasure three flags
  have h := hz fixed hf
  cases z with
  | dead a =>
    obtain ⟨q, hq, _, hall⟩ := h
    obtain ⟨k, hnot, v, hv⟩ := positive
    change ∀ v, e.eval (Sum.elim v fixed) = q at hall
    rw [← agrees, hall v] at hv
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hq hv)
    exact (hnot j hj).elim
  | live f _ =>
    obtain ⟨g, hg⟩ := f.exists_core three
    apply binary_probe_loss_reciprocity three (Equational.Core.decode g)
      (Equational.Core.isCore_decode g) k l p r
    · intro hm
      apply hx
      rw [Equational.Core.eval_decode, hg] at hm
      rw [← agrees]
      exact (h _).1 hm
    · intro hm
      apply hy
      rw [Equational.Core.eval_decode, hg] at hm
      rw [← agrees]
      exact (h _).1 hm

private theorem binary_probe_false (three : Fin 3 ↪ Role) (k : Role) (p : Passive k) :
    probe three k false (fun _ => p) = fun b : Bool =>
      if b then representative three k p else WinnerSet.singleton k := by
  funext b; cases b <;> simp [probe]

private theorem binary_probe_true (three : Fin 3 ↪ Role) (k : Role) (p : Passive k) :
    probe three k true (fun _ => p) = fun b : Bool =>
      if b then WinnerSet.singleton k else representative three k p := by
  funext b; cases b <;> simp [probe]

/-- A satellite that is live at a neutral hub and captured when the hub is
posted at `r` must itself be posted at `r` in any loss at the hub. The other
inputs may be fixed at any menus omitting the observer of the hub loss. -/
theorem satellite_posted_at_hub_loss {Fix : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (t : Term Role (Bool ⊕ Fix)) (ht : t.IsCore)
    (fixed : Fix → WinnerSet Role) (k r : Role) (hk : ∀ j, k ∉ (fixed j).val)
    (p : Passive k)
    (loss : k ∉ (t.eval (Sum.elim (probe three k false (fun _ => p)) fixed)).val)
    (live : k ∈ (t.eval (Sum.elim (probe three k true (fun _ => .neutral)) fixed)).val)
    (captured : ∀ A B : WinnerSet Role,
      t.eval (Sum.elim (fun b : Bool => if b then A else WinnerSet.singleton r) fixed) =
      t.eval (Sum.elim (fun b : Bool => if b then B else WinnerSet.singleton r) fixed)) :
    ∃ s : {s : Role // s ≠ k}, p = .atom s ∧ s.val = r := by
  classical
  let row (X Y : WinnerSet Role) : Bool ⊕ Fix → WinnerSet Role :=
    Sum.elim (fun b : Bool => if b then Y else X) fixed
  let atom := WinnerSet.singleton k
  have hpos : k ∈ (t.eval (row (representative three k .neutral) atom)).val := by
    simpa only [binary_probe_true] using live
  by_cases hr : r = k
  · subst r
    let active : Bool ⊕ Fix → Bool := Sum.elim (! ·) (fun _ => false)
    have hval (X) : (fun i => if active i then X else row atom atom i) = row X atom := by
      funext i
      rcases i with b | j
      · cases b <;> rfl
      · rfl
    have hm : k ∈ (t.eval (row atom atom)).val := by
      rcases ht.isPublic.unary_constant_or_extensive active (row atom atom) with ⟨Q, hQ⟩ | he
      · simp only [hval] at hQ
        rwa [hQ, ← hQ (representative three k .neutral)]
      · simpa only [hval] using he atom (show k ∈ atom.val from rfl)
    have hsq := captured atom (representative three k p)
    rw [binary_probe_false] at loss
    exact (loss (hsq ▸ hm)).elim
  · refine fixed_background_loss_reciprocity three t ht fixed
      ⟨k, hk, _, live⟩ k k p ⟨r, hr⟩ loss ?_
    rw [binary_probe_true]
    change k ∉ (t.eval (row (WinnerSet.singleton r) atom)).val
    have hsq := captured atom (WinnerSet.singleton r)
    change t.eval (row (WinnerSet.singleton r) atom) =
      t.eval (row (WinnerSet.singleton r) (WinnerSet.singleton r)) at hsq
    rw [hsq]
    intro hm
    obtain ⟨i, hi, _⟩ := (membership_iff_source three t ht _ k).1 hm
    rcases i with b | j
    · cases b <;> exact hr hi.symm
    · exact hk j hi

/-- Two opposite proper losses that have compatible outside postings obey
the binary matching rule. Their common outside fixing need only omit the
observer of the positive. Each loss may have a different observer. -/
theorem reciprocal_posting_of_compatible_background {Fix : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (t : Term Role (Bool ⊕ Fix)) (ht : t.IsCore)
    (k m l : Role) (r : {r : Role // r ≠ l}) (p : Passive m)
    (fixed : Fix → WinnerSet Role) (hk : ∀ j, k ∉ (fixed j).val)
    (bx : Fix → Passive m) (by' : Fix → Passive l)
    (hbx : ∀ j a, bx j = .atom a → fixed j = WinnerSet.singleton a.val)
    (hby : ∀ j a, by' j = .atom a → fixed j = WinnerSet.singleton a.val)
    (lossX : m ∉ (t.eval (probe three m (.inl false : Bool ⊕ Fix)
      (fun j => match j.val with | .inl _ => p | .inr i => bx i))).val)
    (lossY : l ∉ (t.eval (probe three l (.inl true : Bool ⊕ Fix)
      (fun j => match j.val with | .inl _ => .atom r | .inr i => by' i))).val)
    (live : k ∈ (t.eval (Sum.elim (probe three k true (fun _ => .neutral)) fixed)).val) :
    ∃ s : {s : Role // s ≠ m}, p = .atom s ∧ s.val = r.val := by
  classical
  let row (X Y : WinnerSet Role) := Sum.elim (fun b : Bool => if b then Y else X) fixed
  have cy (A B) : t.eval (row (WinnerSet.singleton r.val) A) =
      t.eval (row (WinnerSet.singleton r.val) B) := by
    apply (probe_loss_iff_cofactor_independent three t ht l (.inl true) _).1 lossY
    · rintro (b | j) h
      · cases b <;> simp_all [row]
      · rfl
    · rintro ⟨(b | j), hj⟩ a ha
      · cases b with
        | false => exact congrArg WinnerSet.singleton (Subtype.ext_iff.mp (Passive.atom.inj ha))
        | true => exact (hj rfl).elim
      · exact hby j a ha
  have cx (A B Y) (hY : ∀ a, p = .atom a → Y = WinnerSet.singleton a.val) :
      t.eval (row A Y) = t.eval (row B Y) := by
    apply (probe_loss_iff_cofactor_independent three t ht m (.inl false) _).1 lossX
    · rintro (b | j) h
      · cases b <;> simp_all [row]
      · rfl
    · rintro ⟨(b | j), hj⟩ a ha
      · cases b with
        | false => exact (hj rfl).elim
        | true => exact hY a ha
      · exact hbx j a ha
  let neutral := representative three k .neutral
  have noWinner {X Y : WinnerSet Role} (hX : k ∉ X.val) (hY : k ∉ Y.val) :
      k ∉ (t.eval (row X Y)).val := by
    intro hm
    obtain ⟨i, hi, _⟩ := (membership_iff_source three t ht _ k).1 hm
    rcases i with b | j
    · cases b <;> first | exact hX hi | exact hY hi
    · exact hk j hi
  have transfer (a : Passive k) (ha : ∀ s, p = .atom s →
      representative three k a = WinnerSet.singleton s.val) :
      ∃ v : {s : Role // s ≠ k}, a = .atom v ∧ v.val = r.val := by
    apply satellite_posted_at_hub_loss three t ht fixed k r.val hk a _ live cy
    rw [binary_probe_false]
    change k ∉ (t.eval (row (WinnerSet.singleton k) (representative three k a))).val
    rw [cx _ neutral _ ha]
    exact noWinner (representative_omits three k _) (representative_omits three k _)
  cases p with
  | neutral =>
    obtain ⟨v, hv, _⟩ := transfer .neutral (by simp)
    cases hv
  | atom s =>
    refine ⟨s, rfl, ?_⟩
    have corner (Y) (h : Y = WinnerSet.singleton s.val) (A B) :
        t.eval (row A Y) = t.eval (row B Y) :=
      cx A B Y (fun v hv => h.trans (congrArg WinnerSet.singleton
        (Subtype.ext_iff.mp (Passive.atom.inj hv))))
    by_cases hs : s.val = k
    · by_contra hr
      have hkr : k ≠ r.val := hs ▸ hr
      have hp : k ∈ (t.eval (row neutral (WinnerSet.singleton k))).val := by
        simpa only [binary_probe_true] using live
      rw [corner _ (congrArg WinnerSet.singleton hs.symm) _ (WinnerSet.singleton r.val),
        cy _ neutral] at hp
      exact noWinner (X := WinnerSet.singleton r.val) (fun h => hkr h) (representative_omits three k _) hp
    · obtain ⟨v, hv, he⟩ := transfer (.atom ⟨s.val, hs⟩) (by
        intro a ha
        exact congrArg WinnerSet.singleton (Subtype.ext_iff.mp (Passive.atom.inj ha)))
      exact (Subtype.ext_iff.mp (Passive.atom.inj hv)).trans he

/-- The star matching rule from three source observations. The satellite's
loss needs only the posting of the hub, and can be read by any observer
missing that posting. At the background of a hub loss it suffices that the
satellite is still live when the hub is neutral. -/
theorem star_loss_requires_reciprocal_posting {Fix : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (t : Term Role (Bool ⊕ Fix)) (ht : t.IsCore)
    (k l : Role) (r : {r : Role // r ≠ l}) (p : Passive k)
    (background : Fix → Passive k)
    (loss : k ∉ (t.eval (Sum.elim (probe three k false (fun _ => p))
      (fun j => representative three k (background j)))).val)
    (live : k ∈ (t.eval (Sum.elim (probe three k true (fun _ => .neutral))
      (fun j => representative three k (background j)))).val)
    (otherLoss : l ∉ (t.eval (probe three l (Sum.inl true : Bool ⊕ Fix)
      (fun j => match j.val with | .inl false => .atom r | _ => .neutral))).val) :
    ∃ s : {s : Role // s ≠ k}, p = .atom s ∧ s.val = r.val := by
  apply satellite_posted_at_hub_loss three t ht _ k r.val (fun j =>
    representative_omits three k (background j)) p loss live
  intro A B
  apply (probe_loss_iff_cofactor_independent three t ht l (.inl true) _).1 otherLoss
  · rintro (b | j) h
    · cases b <;> simp_all
    · rfl
  · rintro ⟨(b | j), hj⟩ a ha
    · cases b with
      | false => exact congrArg WinnerSet.singleton (Subtype.ext_iff.mp (Passive.atom.inj ha))
      | true => exact (hj rfl).elim
    · cases ha

end KFOL.Core.Sources
