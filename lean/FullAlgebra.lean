/-
Full-signature status preservation, singleton-or-pair countervaluations,
and intrinsic normalization. Internal role permutations use FullTerm from
Separation; no parallel term semantics or Mathlib dependency is introduced.
-/
import Separation

set_option autoImplicit false
namespace MinimalChoice

def SameStatus {α : Type} (A B : S α) : Prop :=
  ∀ r, A = atom r ↔ B = atom r

theorem sameStatus_refl {α : Type} (A : S α) : SameStatus A A :=
  fun _ => Iff.rfl

theorem sameStatus_symm {α : Type} {A B : S α} (h : SameStatus A B) :
    SameStatus B A := fun r => (h r).symm

@[simp] theorem permSet_identity {α : Type} (A : S α) :
    permSet RolePerm.identity A = A := by
  funext x
  apply propext
  simp [permSet, RolePerm.identity]

@[simp] theorem permSet_atom {α : Type} (p : RolePerm α) (r : α) :
    permSet p (atom r) = atom (p.apply r) := by
  funext x
  apply propext
  simp [permSet, atom, eq_comm]

theorem permSet_injective {α : Type} (p : RolePerm α) :
    Function.Injective (permSet p) := by
  intro A B he
  funext x
  apply propext
  constructor
  · intro hx
    have h : permSet p A (p.apply x) := ⟨x, hx, rfl⟩
    rw [he] at h
    obtain ⟨y, hy, hxy⟩ := h
    exact p.injective hxy ▸ hy
  · intro hx
    have h : permSet p B (p.apply x) := ⟨x, hx, rfl⟩
    rw [← he] at h
    obtain ⟨y, hy, hxy⟩ := h
    exact p.injective hxy ▸ hy

theorem permSet_eq_atom {α : Type} (p : RolePerm α) (A : S α) (r : α) :
    permSet p A = atom (p.apply r) ↔ A = atom r := by
  rw [← permSet_atom p r]
  exact ⟨fun h => permSet_injective p h, congrArg (permSet p)⟩

theorem permSet_ne {α : Type} (p : RolePerm α) (A : S α) (ha : NE A) :
    NE (permSet p A) := by
  obtain ⟨x, hx⟩ := ha
  exact ⟨p.apply x, x, hx, rfl⟩

theorem permSet_sub {α : Type} (p : RolePerm α) {A B : S α} (h : Sub A B) :
    Sub (permSet p A) (permSet p B) := by
  rintro y ⟨x, hx, he⟩
  exact ⟨x, h x hx, he⟩

@[simp] theorem permSet_join {α : Type} (p : RolePerm α) (A B : S α) :
    permSet p (join A B) = join (permSet p A) (permSet p B) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, hy | hy, he⟩
    · exact Or.inl ⟨y, hy, he⟩
    · exact Or.inr ⟨y, hy, he⟩
  · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
    · exact ⟨y, Or.inl hy, he⟩
    · exact ⟨y, Or.inr hy, he⟩

@[simp] theorem permSet_comp {α : Type} (p q : RolePerm α) (A : S α) :
    permSet (p.comp q) A = permSet p (permSet q A) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨q.apply x, ⟨x, hx, rfl⟩, he⟩
  · rintro ⟨z, ⟨x, hx, he⟩, hz⟩
    subst z
    exact ⟨x, hx, hz⟩

theorem sameStatus_perm {α : Type} (p : RolePerm α) (A B : S α)
    (h : SameStatus A B) : SameStatus (permSet p A) (permSet p B) := by
  intro r
  obtain ⟨s, rfl⟩ := p.surjective r
  rw [permSet_eq_atom, permSet_eq_atom]
  exact h s

theorem sameStatus_own {α : Type} (r : α) (A B C D : S α)
    (ha : NE A) (hb : NE B) (hc : NE C) (hd : NE D)
    (hac : SameStatus A C) (hbd : SameStatus B D) :
    SameStatus (own r A B) (own r C D) := by
  intro i
  by_cases hi : r = i
  · subst i
    rw [own_eq_owner_iff r A B ha hb, own_eq_owner_iff r C D hc hd]
    exact or_congr (hac r) (hbd r)
  · rw [own_eq_other_iff r i hi A B ha hb, own_eq_other_iff r i hi C D hc hd]
    exact and_congr (hac i) (hbd i)

theorem permSet_own {α : Type} (p : RolePerm α) (r : α) (A B : S α) :
    permSet p (own r A B) = own (p.apply r) (permSet p A) (permSet p B) := by
  classical
  have ha := permSet_eq_atom p A r
  have hb := permSet_eq_atom p B r
  by_cases h : A = atom r ∨ B = atom r
  · have hp : permSet p A = atom (p.apply r) ∨
        permSet p B = atom (p.apply r) := (or_congr ha hb).mpr h
    simp [own, h, hp]
  · have hp : ¬(permSet p A = atom (p.apply r) ∨
        permSet p B = atom (p.apply r)) := fun hh => h ((or_congr ha hb).mp hh)
    simp [own, h, hp]

theorem FullTerm.denote_ne {α β : Type} (t : FullTerm α β)
    (v : β → S α) (hv : ∀ j, NE (v j)) : NE (t.denote v) := by
  induction t with
  | win r => exact atom_ne r
  | var j => exact hv j
  | node r p q hp _ => exact own_ne r _ _ hp
  | rename p t ih => exact permSet_ne p _ ih

theorem FullTerm.sameStatus {α β : Type} (t : FullTerm α β)
    (v w : β → S α) (hv : ∀ j, NE (v j)) (hw : ∀ j, NE (w j))
    (h : ∀ j, SameStatus (v j) (w j)) : SameStatus (t.denote v) (t.denote w) := by
  induction t with
  | win r => exact sameStatus_refl _
  | var j => exact h j
  | node r p q hp hq =>
    exact sameStatus_own r _ _ _ _ (p.denote_ne v hv) (q.denote_ne v hv)
      (p.denote_ne w hw) (q.denote_ne w hw) hp hq
  | rename p t ih => exact sameStatus_perm p _ _ ih

/-- Shrinking inputs is monotone as long as their singleton statuses stay fixed. -/
theorem FullTerm.status_mono {α β : Type} (t : FullTerm α β)
    (v w : β → S α) (hv : ∀ j, NE (v j)) (hw : ∀ j, NE (w j))
    (hstatus : ∀ j, SameStatus (v j) (w j)) (hsub : ∀ j, Sub (w j) (v j)) :
    Sub (t.denote w) (t.denote v) := by
  classical
  induction t with
  | win r => exact fun _ h => h
  | var j => exact hsub j
  | rename p t ih => exact permSet_sub p ih
  | node r p q hp hq =>
    have ep := (p.sameStatus v w hv hw hstatus) r
    have eq := (q.sameStatus v w hv hw hstatus) r
    by_cases hc : p.denote v = atom r ∨ q.denote v = atom r
    · have hc' := (or_congr ep eq).mp hc
      simp only [FullTerm.denote, own, ite_eq_left hc, ite_eq_left hc']
      exact fun _ h => h
    · have hc' : ¬(p.denote w = atom r ∨ q.denote w = atom r) :=
        fun h => hc ((or_congr ep eq).mpr h)
      simp only [FullTerm.denote, own, ite_eq_right hc, ite_eq_right hc']
      exact fun i h => h.elim (fun h => Or.inl (hp i h)) (fun h => Or.inr (hq i h))

def Pinned {α β : Type} (v : β → S α) : Option (β × α) → Prop
  | none => True
  | some (j, a) => v j a

/-- A single input membership suffices to preserve any output membership
through every status-preserving change of the input environment. -/
theorem FullTerm.one_pin {α β : Type} (t : FullTerm α β)
    (v : β → S α) (hv : ∀ j, NE (v j)) (k : α) (hk : t.denote v k) :
    ∃ pin : Option (β × α), Pinned v pin ∧
      ∀ w, (∀ j, NE (w j)) → (∀ j, SameStatus (v j) (w j)) →
        Pinned w pin → t.denote w k := by
  classical
  induction t generalizing k with
  | win r => exact ⟨none, True.intro, fun _ _ _ _ => hk⟩
  | var j => exact ⟨some (j, k), hk, fun _ _ _ h => h⟩
  | rename p t ih =>
    obtain ⟨x, hx, he⟩ := hk
    obtain ⟨pin, hpin, hs⟩ := ih x hx
    exact ⟨pin, hpin, fun w hw hstatus hpin => ⟨x, hs w hw hstatus hpin, he⟩⟩
  | node r p q hp hq =>
    have transfer : ∀ w, (∀ j, NE (w j)) → (∀ j, SameStatus (v j) (w j)) →
        (p.denote v = atom r ∨ q.denote v = atom r ↔
         p.denote w = atom r ∨ q.denote w = atom r) := by
      intro w hw hstatus
      exact or_congr ((p.sameStatus v w hv hw hstatus) r)
        ((q.sameStatus v w hv hw hstatus) r)
    by_cases hc : p.denote v = atom r ∨ q.denote v = atom r
    · have hkr : k = r := by simpa [FullTerm.denote, own, hc, atom] using hk
      refine ⟨none, True.intro, ?_⟩
      intro w hw hstatus _
      have hc' := (transfer w hw hstatus).mp hc
      simp [FullTerm.denote, own, hc', atom, hkr]
    · have hmem : p.denote v k ∨ q.denote v k := by
        simpa only [FullTerm.denote, own, ite_eq_right hc, join] using hk
      rcases hmem with hmem | hmem
      · obtain ⟨pin, hpin, hs⟩ := hp k hmem
        refine ⟨pin, hpin, ?_⟩
        intro w hw hstatus hpinned
        have hc' := fun h => hc ((transfer w hw hstatus).mpr h)
        simp only [FullTerm.denote, own, ite_eq_right hc', join]
        exact Or.inl (hs w hw hstatus hpinned)
      · obtain ⟨pin, hpin, hs⟩ := hq k hmem
        refine ⟨pin, hpin, ?_⟩
        intro w hw hstatus hpinned
        have hc' := fun h => hc ((transfer w hw hstatus).mpr h)
        simp only [FullTerm.denote, own, ite_eq_right hc', join]
        exact Or.inr (hs w hw hstatus hpinned)

def Small {α : Type} (A : S α) : Prop := ∃ a b, A = join (atom a) (atom b)

theorem pair_refinement {α : Type} (A : S α) (ha : NE A) (a : α) (haa : A a) :
    ∃ B, NE B ∧ Small B ∧ Sub B A ∧ SameStatus A B ∧ B a := by
  classical
  rcases atom_or_multiple A ha with ⟨r, he⟩ | hm
  · subst A
    exact ⟨atom r, atom_ne r, ⟨r, r, by funext x; simp [join]⟩,
      (fun _ h => h), sameStatus_refl _, haa⟩
  · have hna : A ≠ atom a := by
      intro he
      exact multiple_not_sub_atom A hm a (fun x hx => he ▸ hx)
    obtain ⟨b, hb, hba⟩ := exists_outside a A ha hna
    let B := join (atom a) (atom b)
    have hbm : Multiple B := ⟨a, b, Ne.symm hba, Or.inl rfl, Or.inr rfl⟩
    refine ⟨B, ⟨a, Or.inl rfl⟩, ⟨a, b, rfl⟩, ?_, ?_, Or.inl rfl⟩
    · intro x hx
      rcases hx with hx | hx
      · exact hx ▸ haa
      · exact hx ▸ hb
    · intro r
      have hA : A ≠ atom r := fun he => multiple_not_sub_atom A hm r (fun x hx => he ▸ hx)
      have hB : B ≠ atom r := fun he => multiple_not_sub_atom B hbm r (fun x hx => he ▸ hx)
      simp [hA, hB]

theorem small_valuation {α β : Type} (v : β → S α) (hv : ∀ j, NE (v j))
    (pin : Option (β × α)) (hpin : Pinned v pin) :
    ∃ w : β → S α,
      (∀ j, NE (w j) ∧ Small (w j) ∧ Sub (w j) (v j) ∧ SameStatus (v j) (w j)) ∧
      Pinned w pin := by
  classical
  let base : β → α := fun j => Classical.choose (hv j)
  have hbase : ∀ j, v j (base j) := fun j => Classical.choose_spec (hv j)
  have make : ∀ a : β → α, (∀ j, v j (a j)) →
      ∃ w : β → S α,
        (∀ j, NE (w j) ∧ Small (w j) ∧ Sub (w j) (v j) ∧ SameStatus (v j) (w j)) ∧
        ∀ j, w j (a j) := by
    intro a ha
    have hx := fun j => pair_refinement (v j) (hv j) (a j) (ha j)
    let w := fun j => Classical.choose (hx j)
    refine ⟨w, fun j => ?_, fun j => (Classical.choose_spec (hx j)).2.2.2.2⟩
    have hh := Classical.choose_spec (hx j)
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  cases pin with
  | none =>
    obtain ⟨w, hw, _⟩ := make base hbase
    exact ⟨w, hw, True.intro⟩
  | some ja =>
    obtain ⟨j₀, a₀⟩ := ja
    let a := fun j => if j = j₀ then a₀ else base j
    have ha : ∀ j, v j (a j) := by
      intro j
      by_cases hj : j = j₀
      · subst j
        simpa [a, Pinned] using hpin
      · simpa [a, hj] using hbase j
    obtain ⟨w, hw, hwa⟩ := make a ha
    exact ⟨w, hw, by simpa [Pinned, a] using hwa j₀⟩

/-- The full singleton-or-pair countervaluation theorem, with role switches. -/
theorem FullTerm.pair_countervaluation {α β : Type} (left right : FullTerm α β)
    (v : β → S α) (hv : ∀ j, NE (v j)) (k : α)
    (hk : left.denote v k) (hn : ¬ right.denote v k) :
    ∃ w : β → S α, (∀ j, NE (w j) ∧ Small (w j)) ∧
      left.denote w k ∧ ¬ right.denote w k := by
  obtain ⟨pin, hpin, preserve⟩ := left.one_pin v hv k hk
  obtain ⟨w, hw, hpinned⟩ := small_valuation v hv pin hpin
  have hwn : ∀ j, NE (w j) := fun j => (hw j).1
  have hstatus := fun j => (hw j).2.2.2
  have hsub := fun j => (hw j).2.2.1
  refine ⟨w, fun j => ⟨(hw j).1, (hw j).2.1⟩,
    preserve w hwn hstatus hpinned, ?_⟩
  exact fun h => hn (right.status_mono v w hv hwn hstatus hsub k h)

def FullTerm.ValidEquation {α β : Type} (left right : FullTerm α β) : Prop :=
  ∀ v, (∀ j, NE (v j)) → left.denote v = right.denote v

theorem FullTerm.pair_tests_complete {α β : Type} (left right : FullTerm α β)
    (h : ∀ v, (∀ j, NE (v j) ∧ Small (v j)) → left.denote v = right.denote v) :
    left.ValidEquation right := by
  classical
  intro v hv
  funext k
  apply propext
  constructor
  · intro hk
    apply Classical.byContradiction
    intro hn
    obtain ⟨w, hw, hl, hr⟩ := left.pair_countervaluation right v hv k hk hn
    exact hr (h w hw ▸ hl)
  · intro hk
    apply Classical.byContradiction
    intro hn
    obtain ⟨w, hw, hr, hl⟩ := right.pair_countervaluation left v hv k hk hn
    exact hl ((h w hw).symm ▸ hr)

def FullTerm.HasWinner {α β : Type} : FullTerm α β → Prop
  | .win _ => True
  | .var _ => False
  | .node _ p q => p.HasWinner ∨ q.HasWinner
  | .rename _ t => t.HasWinner

/-- A syntactic winner leaves some constant contribution on every status cell. -/
theorem FullTerm.constant_on_cell {α β : Type} (t : FullTerm α β)
    (v : β → S α) (hv : ∀ j, NE (v j)) (ht : t.HasWinner) :
    ∃ k, ∀ w, (∀ j, NE (w j)) → (∀ j, SameStatus (v j) (w j)) → t.denote w k := by
  classical
  induction t with
  | win r => exact ⟨r, fun _ _ _ => rfl⟩
  | var j => exact False.elim ht
  | rename p t ih =>
    obtain ⟨k, hk⟩ := ih ht
    exact ⟨p.apply k, fun w hw hs => ⟨k, hk w hw hs, rfl⟩⟩
  | node r p q hp hq =>
    have transfer : ∀ w, (∀ j, NE (w j)) → (∀ j, SameStatus (v j) (w j)) →
        (p.denote v = atom r ∨ q.denote v = atom r ↔
         p.denote w = atom r ∨ q.denote w = atom r) := by
      intro w hw hs
      exact or_congr ((p.sameStatus v w hv hw hs) r) ((q.sameStatus v w hv hw hs) r)
    by_cases hc : p.denote v = atom r ∨ q.denote v = atom r
    · refine ⟨r, ?_⟩
      intro w hw hs
      have hh := (transfer w hw hs).mp hc
      simp [FullTerm.denote, own, hh, atom]
    · rcases ht with ht | ht
      · obtain ⟨k, hk⟩ := hp ht
        refine ⟨k, ?_⟩
        intro w hw hs
        have hn := fun hh => hc ((transfer w hw hs).mpr hh)
        simp only [FullTerm.denote, own, ite_eq_right hn, join]
        exact Or.inl (hk w hw hs)
      · obtain ⟨k, hk⟩ := hq ht
        refine ⟨k, ?_⟩
        intro w hw hs
        have hn := fun hh => hc ((transfer w hw hs).mpr hh)
        simp only [FullTerm.denote, own, ite_eq_right hn, join]
        exact Or.inr (hk w hw hs)

theorem sameStatus_multiple {α : Type} (A B : S α) (ha : Multiple A) (hb : Multiple B) :
    SameStatus A B := by
  intro r
  have hA : A ≠ atom r := fun he => multiple_not_sub_atom A ha r (fun _ hx => he ▸ hx)
  have hB : B ≠ atom r := fun he => multiple_not_sub_atom B hb r (fun _ hx => he ▸ hx)
  simp [hA, hB]

def FullTerm.Idempotent {α β : Type} (t : FullTerm α β) : Prop :=
  ∀ A : S α, NE A → t.denote (fun _ => A) = A

theorem FullTerm.idempotent_no_winner {α β : Type} (three : Three α)
    (t : FullTerm α β) (ht : t.Idempotent) : ¬t.HasWinner := by
  intro hw
  let top : S α := fun _ => True
  have hn : NE top := ⟨three.r, True.intro⟩
  have hm : Multiple top := ⟨three.r, three.s, three.rs, True.intro, True.intro⟩
  obtain ⟨k, hk⟩ := t.constant_on_cell (fun _ => top) (fun _ => hn) hw
  obtain ⟨a, b, hak, hbk, hab⟩ := three_others three k
  let A := join (atom a) (atom b)
  have ha : NE A := ⟨a, Or.inl rfl⟩
  have ham : Multiple A := ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
  have he := hk (fun _ => A) (fun _ => ha) (fun _ => sameStatus_multiple top A hm ham)
  rw [ht A ha] at he
  exact he.elim (fun h => hak h.symm) (fun h => hbk h.symm)

theorem permSet_multiple {α : Type} (p : RolePerm α) (A : S α) (ha : Multiple A) :
    Multiple (permSet p A) := by
  obtain ⟨a, b, hab, ha, hb⟩ := ha
  exact ⟨p.apply a, p.apply b, fun he => hab (p.injective he),
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩

theorem own_of_multiple {α : Type} (r : α) (A B : S α)
    (ha : Multiple A) (hb : Multiple B) : own r A B = join A B := by
  have hA : A ≠ atom r := fun he => multiple_not_sub_atom A ha r (fun _ hx => he ▸ hx)
  have hB : B ≠ atom r := fun he => multiple_not_sub_atom B hb r (fun _ hx => he ▸ hx)
  simp [own, hA, hB]

theorem FullTerm.multiple_without_winner {α β : Type} (t : FullTerm α β)
    (ht : ¬t.HasWinner) (v : β → S α) (hv : ∀ j, Multiple (v j)) :
    Multiple (t.denote v) := by
  induction t with
  | win r => exact False.elim (ht True.intro)
  | var j => exact hv j
  | rename p t ih => exact permSet_multiple p _ (ih ht)
  | node r p q hp hq =>
    have hpm := hp (fun h => ht (Or.inl h))
    have hqm := hq (fun h => ht (Or.inr h))
    simp only [FullTerm.denote, own_of_multiple r _ _ hpm hqm]
    obtain ⟨a, b, hab, ha, hb⟩ := hpm
    exact ⟨a, b, hab, Or.inl ha, Or.inl hb⟩

@[simp] theorem Source.denote_rename {α β : Type} (p : RolePerm α)
    (s : Source α β) (v : β → S α) :
    (s.rename p).denote v = permSet p (s.denote v) := by
  cases s <;> simp [Source.rename, Source.denote]

/-- On the all-ambiguous cell every leaf contribution survives. -/
theorem FullTerm.source_contributes {α β : Type} (t : FullTerm α β)
    (ht : ¬t.HasWinner) (v : β → S α) (hv : ∀ j, Multiple (v j)) :
    ∀ s ∈ t.sources, Sub (s.denote v) (t.denote v) := by
  induction t with
  | win r => exact False.elim (ht True.intro)
  | var j =>
    intro s hs
    have he : s = .input j .identity := by simpa [FullTerm.sources] using hs
    subst s
    simpa [Source.denote, FullTerm.denote] using (show Sub (v j) (v j) from fun _ h => h)
  | node r p q hp hq =>
    have hnp : ¬p.HasWinner := fun h => ht (Or.inl h)
    have hnq : ¬q.HasWinner := fun h => ht (Or.inr h)
    have hpm := p.multiple_without_winner hnp v hv
    have hqm := q.multiple_without_winner hnq v hv
    intro s hs i hi
    simp only [FullTerm.sources, List.mem_append] at hs
    simp only [FullTerm.denote, own_of_multiple r _ _ hpm hqm, join]
    exact hs.elim (fun h => Or.inl (hp hnp s h i hi)) (fun h => Or.inr (hq hnq s h i hi))
  | rename p t ih =>
    intro s hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    rw [Source.denote_rename]
    exact permSet_sub p (ih ht q hq)

theorem FullTerm.winner_source {α β : Type} (t : FullTerm α β) (r : α)
    (hr : Source.win r ∈ t.sources) : t.HasWinner := by
  induction t generalizing r with
  | win i => trivial
  | var j => simp [sources] at hr
  | node i p q hp hq =>
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl (hp r hr)
    · exact Or.inr (hq r hr)
  | rename p t ih =>
    obtain ⟨s, hs, he⟩ := List.mem_map.mp hr
    cases s with
    | win i => exact ih i hs
    | input j q => cases he

def Source.CleanUnder {α β : Type} (p : RolePerm α) : Source α β → Prop
  | .win _ => False
  | .input _ q => ∀ a, p.apply (q.apply a) = a

def FullTerm.CleanUnder {α β : Type} (p : RolePerm α) (t : FullTerm α β) : Prop :=
  ∀ s ∈ t.sources, s.CleanUnder p

theorem FullTerm.idempotent_clean {α β : Type} (three : Three α)
    (t : FullTerm α β) (ht : t.Idempotent) : t.CleanUnder .identity := by
  classical
  have hn := t.idempotent_no_winner three ht
  intro s hs
  cases s with
  | win r => exact hn (t.winner_source r hs)
  | input j p =>
    intro a
    change p.apply a = a
    apply Classical.byContradiction
    intro hpa
    obtain ⟨b, hba, hbp⟩ := third_outside (three_others three) a (p.apply a)
    let A := join (atom a) (atom b)
    have ha : NE A := ⟨a, Or.inl rfl⟩
    have ham : Multiple A := ⟨a, b, Ne.symm hba, Or.inl rfl, Or.inr rfl⟩
    have hsource : Source.denote (.input j p) (fun _ => A) (p.apply a) :=
      ⟨a, Or.inl rfl, rfl⟩
    have hp := t.source_contributes hn (fun _ => A) (fun _ => ham) _ hs _ hsource
    rw [ht A ha] at hp
    exact hp.elim hpa (fun h => hbp h.symm)

def FullTerm.erase {α β : Type} (p : RolePerm α) : FullTerm α β → Term α β
  | .win r => .win (p.apply r)
  | .var j => .var j
  | .node r left right => .node (p.apply r) (left.erase p) (right.erase p)
  | .rename q t => t.erase (p.comp q)

def Term.WinnerFree {α β : Type} : Term α β → Prop
  | .win _ => False
  | .var _ => True
  | .node _ left right => left.WinnerFree ∧ right.WinnerFree

theorem FullTerm.cleanUnder_no_winner {α β : Type} (t : FullTerm α β)
    (p : RolePerm α) (ht : t.CleanUnder p) : ¬t.HasWinner := by
  intro hw
  induction t generalizing p with
  | win r => exact ht (.win r) (by simp [sources])
  | var j => exact hw
  | node r left right hl hr =>
    rcases hw with hw | hw
    · exact hl p (fun s hs => ht s (List.mem_append_left _ hs)) hw
    · exact hr p (fun s hs => ht s (List.mem_append_right _ hs)) hw
  | rename q t ih =>
    apply ih (p.comp q) _ hw
    intro s hs
    have he := ht (s.rename q) (List.mem_map.mpr ⟨s, hs, rfl⟩)
    cases s with
    | win r => exact he
    | input j r => exact he

theorem FullTerm.erase_winnerFree {α β : Type} (t : FullTerm α β)
    (p : RolePerm α) (ht : ¬t.HasWinner) : (t.erase p).WinnerFree := by
  induction t generalizing p with
  | win r => exact False.elim (ht True.intro)
  | var j => trivial
  | node r left right hl hr =>
    exact ⟨hl p (fun h => ht (Or.inl h)), hr p (fun h => ht (Or.inr h))⟩
  | rename q t ih => exact ih (p.comp q) ht

theorem permSet_eq_self {α : Type} (p : RolePerm α) (h : ∀ a, p.apply a = a)
    (A : S α) : permSet p A = A := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, hy, he⟩
    rw [h y] at he
    exact he ▸ hy
  · intro hx
    exact ⟨x, hx, h x⟩

/-- The extraction transports owners and discards precisely the identity
permutations certified at the variable leaves. -/
theorem FullTerm.erase_correct {α β : Type} (t : FullTerm α β)
    (p : RolePerm α) (ht : t.CleanUnder p) (v : β → S α) :
    MinimalChoice.denote (t.erase p) v = permSet p (t.denote v) := by
  induction t generalizing p with
  | win r => exact False.elim (ht (.win r) (by simp [sources]))
  | var j =>
    have hh := ht (.input j .identity) (by simp [sources])
    exact (permSet_eq_self p hh (v j)).symm
  | node r left right hl hr =>
    have hleft : left.CleanUnder p := fun s hs => ht s (List.mem_append_left _ hs)
    have hright : right.CleanUnder p := fun s hs => ht s (List.mem_append_right _ hs)
    simp only [erase, MinimalChoice.denote, FullTerm.denote, permSet_own,
      hl p hleft, hr p hright]
  | rename q t ih =>
    have hc : t.CleanUnder (p.comp q) := by
      intro s hs
      have hh := ht (s.rename q) (List.mem_map.mpr ⟨s, hs, rfl⟩)
      cases s with
      | win r => exact hh
      | input j r => exact hh
    exact (ih (p.comp q) hc).trans (permSet_comp p q (t.denote v))

theorem Term.winnerFree_diagonal {α β : Type} (t : Term α β)
    (ht : t.WinnerFree) (A : S α) : denote t (fun _ => A) = A := by
  induction t with
  | win r => exact False.elim ht
  | var j => rfl
  | node r left right hl hr =>
    simp only [denote, hl ht.1, hr ht.2, own_idem]

/-- Full-signature idempotency is exactly absence of constant leaves and
identity accumulated role action at every input occurrence. -/
theorem FullTerm.idempotent_iff_clean {α β : Type} (three : Three α)
    (t : FullTerm α β) : t.Idempotent ↔ t.CleanUnder .identity := by
  constructor
  · exact t.idempotent_clean three
  · intro ht A _
    have hw := t.erase_winnerFree .identity (t.cleanUnder_no_winner .identity ht)
    have he := t.erase_correct .identity ht (fun _ => A)
    rw [permSet_identity] at he
    exact he.symm.trans ((t.erase .identity).winnerFree_diagonal hw A)

/-- Every idempotent operation in the full language has a constant-free,
switch-free expression with exactly the same semantics on all inputs. -/
theorem FullTerm.idempotent_extraction {α β : Type} (three : Three α)
    (t : FullTerm α β) (ht : t.Idempotent) :
    ∃ core : Term α β, core.WinnerFree ∧ ∀ v, MinimalChoice.denote core v = t.denote v := by
  have hc := t.idempotent_clean three ht
  refine ⟨t.erase .identity, t.erase_winnerFree .identity
    (t.cleanUnder_no_winner .identity hc), ?_⟩
  intro v
  simpa using t.erase_correct .identity hc v

def Term.full {α β : Type} : Term α β → FullTerm α β
  | .win r => .win r
  | .var j => .var j
  | .node r left right => .node r left.full right.full

@[simp] theorem Term.full_denote {α β : Type} (t : Term α β) (v : β → S α) :
    t.full.denote v = denote t v := by
  induction t <;> simp_all [full, FullTerm.denote, denote]

def FullTerm.union {α β : Type} (h : Three α) (left right : FullTerm α β) : FullTerm α β :=
  .node h.t (.node h.r left right) (.node h.s left right)

@[simp] theorem FullTerm.denote_union {α β : Type} (h : Three α)
    (left right : FullTerm α β) (v : β → S α) :
    (left.union h right).denote v = join (left.denote v) (right.denote v) := by
  simp only [union, FullTerm.denote]
  exact three_owner_join h.r h.s h.t h.rs h.rt h.st _ _

noncomputable def FullTerm.collect {α β : Type} (h : Three α) (roles : List α)
    (enabled : α → Prop) (piece : α → FullTerm α β) (base : FullTerm α β) : FullTerm α β := by
  classical
  exact match roles with
  | [] => base
  | i :: rest => if enabled i then (piece i).union h (collect h rest enabled piece base)
      else collect h rest enabled piece base

theorem FullTerm.denote_collect {α β : Type} (h : Three α) (roles : List α)
    (enabled : α → Prop) (piece : α → FullTerm α β) (base : FullTerm α β)
    (v : β → S α) (w : α) :
    (collect h roles enabled piece base).denote v w ↔
      base.denote v w ∨ ∃ i ∈ roles, enabled i ∧ (piece i).denote v w := by
  classical
  induction roles with
  | nil => simp [collect]
  | cons i rest ih =>
    by_cases hi : enabled i
    · simp only [collect, ite_eq_left hi, denote_union, join, ih]
      constructor
      · rintro (hp | hb | ⟨j, hj, he, hp⟩)
        · exact Or.inr ⟨i, by simp, hi, hp⟩
        · exact Or.inl hb
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, he, hp⟩
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inr (Or.inl hb)
        · rcases List.mem_cons.mp hj with hj | hj
          · subst j
            exact Or.inl hp
          · exact Or.inr (Or.inr ⟨j, hj, he, hp⟩)
    · simp only [collect, ite_eq_right hi, ih]
      constructor
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inl hb
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, he, hp⟩
      · rintro (hb | ⟨j, hj, he, hp⟩)
        · exact Or.inl hb
        · rcases List.mem_cons.mp hj with hj | hj
          · subst j
            exact False.elim (hi he)
          · exact Or.inr ⟨j, hj, he, hp⟩

noncomputable def transposeRole {α : Type} (a b x : α) : α := by
  classical
  exact if x = a then b else if x = b then a else x

theorem transposeRole_involutive {α : Type} (a b x : α) :
    transposeRole a b (transposeRole a b x) = x := by
  classical
  by_cases he : a = b
  · subst b
    by_cases hx : x = a <;> simp [transposeRole, hx]
  · by_cases ha : x = a
    · subst x
      simp [transposeRole, Ne.symm he]
    · by_cases hb : x = b
      · subst x
        simp [transposeRole, Ne.symm he]
      · simp [transposeRole, ha, hb]

noncomputable def RolePerm.swap {α : Type} (a b : α) : RolePerm α :=
  ⟨transposeRole a b,
   fun x y he => (transposeRole_involutive a b x).symm.trans
     ((congrArg (transposeRole a b) he).trans (transposeRole_involutive a b y)),
   fun y => ⟨transposeRole a b y, transposeRole_involutive a b y⟩⟩

@[simp] theorem RolePerm.swap_apply_left {α : Type} (a b : α) :
    (RolePerm.swap a b).apply a = b := by simp [swap, transposeRole]

theorem permSet_apply_iff {α : Type} (p : RolePerm α) (A : S α) (a : α) :
    permSet p A (p.apply a) ↔ A a := by
  constructor
  · rintro ⟨x, hx, he⟩
    exact p.injective he ▸ hx
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem Multiple.eq_pair_of_sub {α : Type} (A : S α) (a b : α)
    (hm : Multiple A) (hs : Sub A (join (atom a) (atom b))) :
    A = join (atom a) (atom b) := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hm
  have hxa := hs x hx
  have hya := hs y hy
  have ha : A a := by
    rcases hxa with h | h
    · exact h ▸ hx
    · rcases hya with hh | hh
      · exact hh ▸ hy
      · exact False.elim (hxy (h.trans hh.symm))
  have hb : A b := by
    rcases hxa with h | h
    · rcases hya with hh | hh
      · exact False.elim (hxy (h.trans hh.symm))
      · exact hh ▸ hy
    · exact h ▸ hx
  funext w
  apply propext
  exact ⟨hs w, fun h => h.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩

/-- A finite full-language term that supplies the missing role except
precisely on subsets of the selected pair. -/
theorem pair_expander {α : Type} (three : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (a b k : α) (hak : a ≠ k) (hbk : b ≠ k) :
    ∃ t : FullTerm α Unit,
      (∀ A, Sub A (t.denote (fun _ => A))) ∧
      (∀ A, t.denote (fun _ => A) k ↔ ¬Sub A (join (atom a) (atom b))) ∧
      (∀ A i, i ≠ k → t.denote (fun _ => A) i) := by
  classical
  let C : S α := fun i => i ≠ k
  obtain ⟨ground, hg⟩ := ground_realization three roles covers C ⟨a, hak⟩
  let enabled := fun i => i ≠ a ∧ i ≠ b ∧ i ≠ k
  let piece : α → FullTerm α Unit := fun i => .rename (.swap i k) (.var ())
  let base : FullTerm α Unit := (FullTerm.var ()).union three ground.full
  let t := FullTerm.collect three roles enabled piece base
  have formula : ∀ A i, t.denote (fun _ => A) i ↔
      (A i ∨ i ≠ k) ∨ ∃ j ∈ roles, enabled j ∧ permSet (.swap j k) A i := by
    intro A i
    have hf := FullTerm.denote_collect three roles enabled piece base (fun _ => A) i
    simpa [base, piece, FullTerm.denote, hg, C, join] using hf
  have at_k : ∀ A, t.denote (fun _ => A) k ↔
      A k ∨ ∃ j ∈ roles, enabled j ∧ A j := by
    intro A
    have hs : ∀ j, permSet (.swap j k) A k ↔ A j := by
      intro j
      simpa using permSet_apply_iff (.swap j k) A j
    simp only [formula, ne_eq, not_true_eq_false, or_false, hs]
  refine ⟨t, ?_, ?_, ?_⟩
  · exact fun A i hi => (formula A i).mpr (Or.inl (Or.inl hi))
  · intro A
    rw [at_k A]
    constructor
    · intro hm hsub
      rcases hm with hm | ⟨j, _, hj, hm⟩
      · exact (hsub k hm).elim (fun h => hak h.symm) (fun h => hbk h.symm)
      · exact (hsub j hm).elim hj.1 hj.2.1
    · intro hn
      apply Classical.byContradiction
      intro hm
      apply hn
      intro i hi
      by_cases ha : i = a
      · exact Or.inl ha
      by_cases hb : i = b
      · exact Or.inr hb
      by_cases hk : i = k
      · exact False.elim (hm (Or.inl (hk ▸ hi)))
      · exact False.elim (hm (Or.inr ⟨i, covers i, ⟨ha, hb, hk⟩, hi⟩))
  · exact fun A i hi => (formula A i).mpr (Or.inl (Or.inr hi))

def FullTerm.suppress {α β : Type} (roles : List α)
    (acc base : FullTerm α β) : FullTerm α β :=
  match roles with
  | [] => acc
  | r :: rest => .node r (suppress rest acc base) base

theorem FullTerm.denote_suppress {α β : Type} (roles : List α)
    (acc base : FullTerm α β) (v : β → S α) :
    (suppress roles acc base).denote v = resetFold roles (acc.denote v) (base.denote v) := by
  induction roles with
  | nil => rfl
  | cons r rest ih => simp only [suppress, FullTerm.denote, ih, resetFold]

def FullTerm.resetWith {α β : Type} (three : Three α) (roles : List α)
    (t base : FullTerm α β) : FullTerm α β :=
  suppress roles (base.union three t) base

@[simp] theorem FullTerm.denote_resetWith {α β : Type} (three : Three α) (roles : List α)
    (t base : FullTerm α β) (v : β → S α) :
    (t.resetWith three roles base).denote v = relativeReset roles (t.denote v) (base.denote v) := by
  simp [resetWith, denote_suppress, relativeReset]

theorem join_of_sub {α : Type} (A B : S α) (h : Sub A B) : join A B = B := by
  funext i
  apply propext
  exact ⟨fun hi => hi.elim (h i) id, Or.inr⟩

/-- Every particular pair has two genuine full-language terms agreeing
on every other nonempty input and disagreeing at that pair. -/
theorem FullTerm.pair_separator {α : Type} (three : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (a b : α) (hab : a ≠ b) :
    ∃ p q : FullTerm α Unit,
      (∀ A, NE A → A ≠ join (atom a) (atom b) →
        p.denote (fun _ => A) = q.denote (fun _ => A)) ∧
      p.denote (fun _ => join (atom a) (atom b)) ≠
        q.denote (fun _ => join (atom a) (atom b)) := by
  classical
  obtain ⟨k, hka, hkb⟩ := third_outside (three_others three) a b
  obtain ⟨f, hfsub, hfk, hfother⟩ :=
    pair_expander three roles covers a b k (Ne.symm hka) (Ne.symm hkb)
  let top : S α := fun _ => True
  obtain ⟨q₀, hq⟩ := ground_realization three roles covers top ⟨a, True.intro⟩
  let p := f.resetWith three roles (.var ())
  let q := q₀.full.resetWith three roles (.var ())
  have hp_atom : ∀ r, p.denote (fun _ => atom r) = atom r := by
    intro r
    simp only [p, FullTerm.denote_resetWith, FullTerm.denote]
    exact relativeReset_atom roles _ r (covers r)
  have hq_atom : ∀ r, q.denote (fun _ => atom r) = atom r := by
    intro r
    simp only [q, FullTerm.denote_resetWith, FullTerm.denote]
    exact relativeReset_atom roles _ r (covers r)
  have hp_mult : ∀ A, Multiple A → p.denote (fun _ => A) = f.denote (fun _ => A) := by
    intro A hm
    simp only [p, FullTerm.denote_resetWith, FullTerm.denote]
    rw [relativeReset_multiple roles _ A hm]
    exact join_of_sub _ _ (hfsub A)
  have hq_mult : ∀ A, Multiple A → q.denote (fun _ => A) = top := by
    intro A hm
    simp only [q, FullTerm.denote_resetWith, FullTerm.denote]
    rw [relativeReset_multiple roles _ A hm, Term.full_denote, hq, join_top]
  refine ⟨p, q, ?_, ?_⟩
  · intro A hn hne
    rcases atom_or_multiple A hn with ⟨r, he⟩ | hm
    · rw [he, hp_atom, hq_atom]
    · have hnsub : ¬Sub A (join (atom a) (atom b)) :=
        fun hs => hne (hm.eq_pair_of_sub A a b hs)
      have hftop : f.denote (fun _ => A) = top := by
        funext i
        apply propext
        constructor
        · exact fun _ => True.intro
        · intro _
          by_cases hi : i = k
          · subst i
            exact (hfk A).mpr hnsub
          · exact hfother A i hi
      rw [hp_mult A hm, hq_mult A hm, hftop]
  · let A := join (atom a) (atom b)
    have hm : Multiple A := ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
    intro he
    have hpk : p.denote (fun _ => A) k := by rw [he, hq_mult A hm]; trivial
    rw [hp_mult A hm] at hpk
    exact (hfk A).mp hpk (fun _ hi => hi)

def FullUnaryTestsComplete {α : Type} (D : S α → Prop) : Prop :=
  ∀ p q : FullTerm α Unit,
    (∀ A, NE A → D A → p.denote (fun _ => A) = q.denote (fun _ => A)) →
      p.ValidEquation q

theorem FullTerm.test_domain_necessary {α : Type} (three : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (D : S α → Prop) (hc : FullUnaryTestsComplete D) :
    (∀ i, D (atom i)) ∧ (∀ a b, a ≠ b → D (join (atom a) (atom b))) := by
  classical
  have hred : UnaryTestsComplete D := by
    intro p q h
    have hf := hc p.full q.full (by simpa using h)
    intro v hv
    simpa using hf v hv
  refine ⟨(MinimalChoice.test_domain_necessary three roles covers D hred).1, ?_⟩
  intro a b hab
  apply Classical.byContradiction
  intro hn
  obtain ⟨p, q, hpq, hne⟩ := pair_separator three roles covers a b hab
  have he := hc p q (by
    intro A ha hD
    exact hpq A ha (fun he => hn (he ▸ hD)))
  exact hne (he (fun _ => join (atom a) (atom b)) (fun _ => ⟨a, Or.inl rfl⟩))

def FullTestsComplete {α : Type} (D : S α → Prop) : Prop :=
  ∀ (β : Type) (left right : FullTerm α β),
    (∀ v, (∀ j, NE (v j)) → (∀ j, D (v j)) → left.denote v = right.denote v) →
      left.ValidEquation right

/-- The minimum full-signature test domain is exactly the singleton/pair
domain. Necessity already follows from unary equations. -/
theorem full_test_domain_iff {α : Type} (three : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (D : S α → Prop) :
    FullTestsComplete D ↔ ∀ A, Small A → D A := by
  constructor
  · intro hc
    have hu : FullUnaryTestsComplete D := by
      intro p q h
      apply hc Unit p q
      intro v hv hd
      have he := h (v ()) (hv ()) (hd ())
      have hvconst : (fun _ : Unit => v ()) = v := by funext j; cases j; rfl
      simpa only [hvconst] using he
    have hn := FullTerm.test_domain_necessary three roles covers D hu
    rintro A ⟨a, b, rfl⟩
    by_cases hab : a = b
    · subst b
      have he : join (atom a) (atom a) = atom a := by funext x; simp [join]
      exact he.symm ▸ hn.1 a
    · exact hn.2 a b hab
  · intro hd β left right he
    apply left.pair_tests_complete right
    intro v hv
    exact he v (fun j => (hv j).1) (fun j => hd (v j) (hv j).2)

/-- The small player quotients apply to every idempotent full-language term. -/
theorem FullTerm.idempotent_sameView {α β : Type} (three : Three α)
    (t : FullTerm α β) (ht : t.Idempotent) (k : α)
    (v w : β → S α) (hv : ∀ j, NE (v j)) (hw : ∀ j, NE (w j))
    (hs : ∀ j, SameView k (v j) (w j)) :
    SameView k (t.denote v) (t.denote w) := by
  obtain ⟨core, _, hc⟩ := t.idempotent_extraction three ht
  rw [← hc v, ← hc w]
  exact denote_sameView core k v w hv hw hs

end MinimalChoice

#print axioms MinimalChoice.FullTerm.pair_countervaluation
#print axioms MinimalChoice.FullTerm.pair_tests_complete
#print axioms MinimalChoice.FullTerm.idempotent_iff_clean
#print axioms MinimalChoice.FullTerm.idempotent_extraction
#print axioms MinimalChoice.FullTerm.pair_separator
#print axioms MinimalChoice.full_test_domain_iff
#print axioms MinimalChoice.FullTerm.idempotent_sameView
