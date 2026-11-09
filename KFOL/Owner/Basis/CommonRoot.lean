module

public import KFOL.Owner.Basis.Presentation

/-! Common-root semilattices and join-preserving unary actions in every
arbitrary model of the explicitly listed forty native identities. -/

@[expose] public section

namespace KFOL.Owner.FiniteBasis

universe u

namespace Laws

variable {M : Type u} {f : M → M → M} {h : M → M → M → M} (laws : Laws f h)

include laws

/-- The first six displayed equations, in the shared reset-law interface. -/
theorem reset_laws : Reset.Laws f :=
  ⟨laws.R1, laws.R2, laws.R3, laws.R4, laws.R5, laws.R6⟩

@[instance_reducible] def fiberSup (r : M) : Max (RootFiber f r) where
  max x y := ⟨f x y, by simpa only [y.property] using laws.reset_laws.e8 x.val y.val r⟩

/-- Same-root reset is a join in every model; the order is constructed from
this operation and is local to the fixed root's subtype. -/
@[instance_reducible] def fiberSemilattice (r : M) : SemilatticeSup (RootFiber f r) := by
  let _ := laws.fiberSup r
  apply SemilatticeSup.mk'
  · intro x y
    exact Subtype.ext (laws.reset_laws.comm_of_fixed x.property y.property)
  · intro x y z
    exact Subtype.ext (laws.reset_laws.assoc_of_fixed x.property y.property).symm
  · intro x
    exact Subtype.ext (laws.R1 x)

@[instance_reducible] def fiberOrderBot (r : M) : letI := laws.fiberSemilattice r; OrderBot (RootFiber f r) := by
  let _ := laws.fiberSemilattice r
  refine { bot := ⟨r, laws.R1 r⟩, bot_le := ?_ }
  intro x
  apply Subtype.ext
  change f r x = x
  simpa only [x.property] using laws.reset_laws.e11 r x.val

/-- Every primitive F action maps the common-root fiber to itself. -/
def action (r a b : M) (x : RootFiber f r) : RootFiber f r :=
  ⟨h r (f x a) b, laws.h_root r (f x a) b⟩

/-- Primitive actions preserve binary joins, hence are monotone. Bottom need
not be preserved: its image supplies the action's constant contributions. -/
def actionHom (r a b : M) :
    letI := laws.fiberSemilattice r; SupHom (RootFiber f r) (RootFiber f r) := by
  let _ := laws.fiberSemilattice r
  refine ⟨laws.action r a b, ?_⟩
  intro x y
  apply Subtype.ext
  change h r (f (f x.val y.val) a) b = f (h r (f x.val a) b) (h r (f y.val a) b)
  simpa only [x.property, y.property, laws.h_root] using laws.F_join r a b x.val y.val

@[simp] theorem action_idem (r a b : M) (x : RootFiber f r) :
    laws.action r a b (laws.action r a b x) = laws.action r a b x := by
  apply Subtype.ext
  exact (by simpa only [action, x.property] using laws.F_idem r a b x.val)

theorem action_band (r a b c d : M) (x : RootFiber f r) :
    laws.action r a b (laws.action r c d (laws.action r a b x)) =
      laws.action r a b (laws.action r c d x) := by
  apply Subtype.ext
  exact (by simpa only [action, x.property] using laws.F_band r a b c d x.val)

theorem action_contract (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    ∀ x : RootFiber f r, laws.action r a b x ≤ laws.action r a b ⊥ ⊔ x := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  intro x
  apply Subtype.ext
  change f (h r (f x.val a) b) (f (h r (f r a) b) x.val) = f (h r (f r a) b) x.val
  have hjoin : f (f (h r (f r a) b) x.val) r = f (h r (f r a) b) x.val := by
    simpa only [x.property] using laws.reset_laws.e8 (h r (f r a) b) x.val r
  simpa only [x.property, laws.h_root, hjoin] using laws.F_contract r a b x.val

/-- Outermost-first action words. This definition contains no semantic
guards or realizability condition. -/
def word (r : M) (letters : List (M × M)) (x : RootFiber f r) : RootFiber f r :=
  letters.foldr (fun p y => laws.action r p.1 p.2 y) x

@[simp] theorem word_nil (r : M) (x : RootFiber f r) : laws.word r [] x = x := rfl
@[simp] theorem word_cons (r a b : M) (rest : List (M × M)) (x : RootFiber f r) :
    laws.word r ((a, b) :: rest) x = laws.action r a b (laws.word r rest x) := rfl

theorem word_append (r : M) (left right : List (M × M)) (x : RootFiber f r) :
    laws.word r (left ++ right) x = laws.word r left (laws.word r right x) := by
  induction left with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, word_cons, ih]

/-- A primitive repeated action may be deleted across an arbitrary word. -/
theorem action_word_action (r a b : M) (rest : List (M × M)) (x : RootFiber f r) :
    laws.action r a b (laws.word r rest (laws.action r a b x)) =
      laws.action r a b (laws.word r rest x) := by
  induction rest with
  | nil => exact laws.action_idem r a b x
  | cons p rest ih =>
    obtain ⟨c, d⟩ := p
    change laws.action r a b (laws.action r c d (laws.word r rest (laws.action r a b x))) = _
    rw [← laws.action_band r a b c d (laws.word r rest (laws.action r a b x)), ih,
      laws.action_band]
    rfl

/-- If a letter occurs in a word, appending it changes no value. -/
theorem word_action_of_mem (r a b : M) (letters : List (M × M)) (hab : (a, b) ∈ letters)
    (x : RootFiber f r) : laws.word r letters (laws.action r a b x) = laws.word r letters x := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hab
  simp only [word_append, word_cons, laws.action_word_action]

/-- Every word whose letters are already present is absorbed on the right. -/
theorem word_absorb (r : M) (left right : List (M × M))
    (hsub : ∀ p ∈ right, p ∈ left) (x : RootFiber f r) :
    laws.word r left (laws.word r right x) = laws.word r left x := by
  induction right with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    change laws.word r left (laws.action r a b (laws.word r rest x)) = _
    rw [laws.word_action_of_mem r a b left (hsub _ (List.mem_cons_self ..))]
    exact ih (fun p hp => hsub p (List.mem_cons_of_mem _ hp))

/-- Word actions satisfy the left-regular-band identity at every argument. -/
theorem word_band (r : M) (left middle : List (M × M)) (x : RootFiber f r) :
    laws.word r left (laws.word r middle (laws.word r left x)) =
      laws.word r left (laws.word r middle x) := by
  rw [← laws.word_append, laws.word_absorb r (left ++ middle) left
    (fun p hp => List.mem_append_left _ hp), laws.word_append]

theorem word_sup (r : M) (letters : List (M × M)) :
    letI := laws.fiberSemilattice r
    ∀ x y : RootFiber f r, laws.word r letters (x ⊔ y) = laws.word r letters x ⊔ laws.word r letters y := by
  let _ := laws.fiberSemilattice r
  intro x y
  induction letters with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [word_cons, ih]
    exact map_sup (laws.actionHom r a b) _ _

theorem word_mono (r : M) (letters : List (M × M)) :
    letI := laws.fiberSemilattice r; Monotone (laws.word r letters) := by
  let _ := laws.fiberSemilattice r
  exact OrderHomClass.monotone (show SupHom (RootFiber f r) (RootFiber f r) from
    ⟨laws.word r letters, laws.word_sup r letters⟩)

/-- Every action word is contractive up to its value at bottom. -/
theorem word_contract (r : M) (letters : List (M × M)) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    ∀ x : RootFiber f r, laws.word r letters x ≤ laws.word r letters ⊥ ⊔ x := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  intro x
  induction letters with
  | nil => exact le_sup_right
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    change laws.action r a b (laws.word r rest x) ≤ laws.action r a b (laws.word r rest ⊥) ⊔ x
    have hm := OrderHomClass.monotone (laws.actionHom r a b)
    have hb : laws.action r a b ⊥ ≤ laws.action r a b (laws.word r rest ⊥) := hm bot_le
    calc
      _ ≤ laws.action r a b (laws.word r rest ⊥ ⊔ x) := hm ih
      _ = laws.action r a b (laws.word r rest ⊥) ⊔ laws.action r a b x := map_sup (laws.actionHom r a b) _ _
      _ ≤ laws.action r a b (laws.word r rest ⊥) ⊔ (laws.action r a b ⊥ ⊔ x) :=
        sup_le_sup_left (laws.action_contract r a b x) _
      _ ≤ laws.action r a b (laws.word r rest ⊥) ⊔ x :=
        sup_le le_sup_left (sup_le (hb.trans le_sup_left) le_sup_right)

/-- G is the diagonal primitive action. -/
theorem action_diagonal (r a : M) (x : RootFiber f r) :
    (laws.action r a a x).val = f (f x.val a) r := by
  exact (by simpa only [action, x.property] using (laws.G_def r a x.val).symm)

/-- K is the primitive action whose first index is the common root. -/
theorem action_root (r a : M) (x : RootFiber f r) :
    (laws.action r r a x).val = h r x.val a := by
  dsimp [action]
  rw [x.property]

theorem action_absorb_diagonal (r a b : M) (x : RootFiber f r) :
    laws.action r a b (laws.action r a a x) = laws.action r a b x := by
  apply Subtype.ext
  change h r (f (laws.action r a a x).val a) b = h r (f x.val a) b
  rw [laws.action_diagonal]
  simpa only [x.property] using laws.F_Ga r a b x.val

theorem action_absorb_root_left (r a b : M) (x : RootFiber f r) :
    laws.action r a b (laws.action r r a x) = laws.action r a b x := by
  apply Subtype.ext
  change h r (f (laws.action r r a x).val a) b = h r (f x.val a) b
  rw [laws.action_root]
  simpa only [x.property] using laws.F_Ka r a b x.val

theorem action_absorb_root_right (r a b : M) (x : RootFiber f r) :
    laws.action r a b (laws.action r r b x) = laws.action r a b x := by
  apply Subtype.ext
  change h r (f (laws.action r r b x).val a) b = h r (f x.val a) b
  rw [laws.action_root]
  simpa only [x.property] using laws.F_Kb r a b x.val

theorem action_root_root (r : M) (x : RootFiber f r) : laws.action r r r x = x := by
  apply Subtype.ext
  rw [laws.action_root]
  simpa only [x.property] using laws.K_root r x.val

/-- Projected variables supply the constants c_a of the word calculus. -/
def constant (r a : M) : RootFiber f r := ⟨f a r, laws.R3 a r⟩

theorem action_zero (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    (laws.action r a b ⊥).val = h r a b := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  exact laws.F_zero r a b

theorem action_constant_left (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.action r a b (laws.constant r a) = laws.action r a b ⊥ := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  apply Subtype.ext
  exact laws.F_ca r a b

theorem action_constant_right (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.action r a b (laws.constant r b) = laws.action r a b ⊥ := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  apply Subtype.ext
  exact laws.F_cb r a b

/-- First-index ambiguity tests make their G action redundant. -/
theorem word_diagonal (r a : M) (letters : List (M × M))
    (ha : a = r ∨ ∃ b, (a, b) ∈ letters) (x : RootFiber f r) :
    laws.word r letters (laws.action r a a x) = laws.word r letters x := by
  rcases ha with rfl | ⟨b, hab⟩
  · rw [laws.action_root_root]
  · calc
      _ = laws.word r letters (laws.action r a b (laws.action r a a x)) :=
        (laws.word_action_of_mem r a b letters hab _).symm
      _ = laws.word r letters (laws.action r a b x) := by rw [laws.action_absorb_diagonal]
      _ = laws.word r letters x := laws.word_action_of_mem r a b letters hab x

/-- Either index's non-owner test makes its K action redundant. -/
theorem word_root (r b : M) (letters : List (M × M))
    (hb : b = r ∨ (∃ c, (b, c) ∈ letters) ∨ ∃ c, (c, b) ∈ letters) (x : RootFiber f r) :
    laws.word r letters (laws.action r r b x) = laws.word r letters x := by
  rcases hb with rfl | ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [laws.action_root_root]
  · calc
      _ = laws.word r letters (laws.action r b c (laws.action r r b x)) :=
        (laws.word_action_of_mem r b c letters hc _).symm
      _ = laws.word r letters (laws.action r b c x) := by rw [laws.action_absorb_root_left]
      _ = laws.word r letters x := laws.word_action_of_mem r b c letters hc x
  · calc
      _ = laws.word r letters (laws.action r c b (laws.action r r b x)) :=
        (laws.word_action_of_mem r c b letters hc _).symm
      _ = laws.word r letters (laws.action r c b x) := by rw [laws.action_absorb_root_right]
      _ = laws.word r letters x := laws.word_action_of_mem r c b letters hc x

/-- Any index previously tested by a word has no new constant contribution. -/
theorem word_constant (r b : M) (letters : List (M × M))
    (hb : b = r ∨ (∃ c, (b, c) ∈ letters) ∨ ∃ c, (c, b) ∈ letters) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.word r letters (laws.constant r b) = laws.word r letters ⊥ := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  rcases hb with rfl | ⟨c, hc⟩ | ⟨c, hc⟩
  · have he : laws.constant b b = (⊥ : RootFiber f b) := Subtype.ext (laws.R1 b)
    rw [he]
  · calc
      _ = laws.word r letters (laws.action r b c (laws.constant r b)) :=
        (laws.word_action_of_mem r b c letters hc _).symm
      _ = laws.word r letters (laws.action r b c ⊥) := by rw [laws.action_constant_left]
      _ = laws.word r letters ⊥ := laws.word_action_of_mem r b c letters hc _
  · calc
      _ = laws.word r letters (laws.action r c b (laws.constant r b)) :=
        (laws.word_action_of_mem r c b letters hc _).symm
      _ = laws.word r letters (laws.action r c b ⊥) := by rw [laws.action_constant_right]
      _ = laws.word r letters ⊥ := laws.word_action_of_mem r c b letters hc _

theorem action_capture (r a b : M) (x : RootFiber f r) :
    laws.action r a a (laws.action r r b (laws.action r a b x)) =
      laws.action r a a (laws.action r r b x) := by
  apply Subtype.ext
  rw [laws.action_diagonal, laws.action_diagonal, laws.action_root, laws.action_root]
  change f (f (h r (h r (f x.val a) b) b) a) r = f (f (h r x.val b) a) r
  simpa only [x.property] using laws.capture r a b x.val

theorem action_weak (r a b : M) (x : RootFiber f r) :
    laws.action r a a (laws.action r a b x) = laws.action r a a (laws.action r r b x) := by
  apply Subtype.ext
  rw [laws.action_diagonal, laws.action_diagonal, laws.action_root]
  change f (f (h r (f x.val a) b) a) r = f (f (h r x.val b) a) r
  simpa only [x.property] using laws.weak_gate r a b x.val

/-- A word captures every action whose two tests it already imposes. -/
theorem word_capture (r a b : M) (letters : List (M × M))
    (ha : a = r ∨ ∃ c, (a, c) ∈ letters)
    (hb : b = r ∨ (∃ c, (b, c) ∈ letters) ∨ ∃ c, (c, b) ∈ letters) (x : RootFiber f r) :
    laws.word r letters (laws.action r a b x) = laws.word r letters x := by
  calc
    _ = laws.word r letters (laws.action r a a (laws.action r r b (laws.action r a b x))) := by
      rw [laws.word_diagonal r a letters ha, laws.word_root r b letters hb]
    _ = laws.word r letters (laws.action r a a (laws.action r r b x)) := by rw [laws.action_capture]
    _ = laws.word r letters x := by rw [laws.word_diagonal r a letters ha, laws.word_root r b letters hb]

/-- If its first test is present, an action reduces to its companion test. -/
theorem word_weak (r a b : M) (letters : List (M × M))
    (ha : a = r ∨ ∃ c, (a, c) ∈ letters) (x : RootFiber f r) :
    laws.word r letters (laws.action r a b x) = laws.word r letters (laws.action r r b x) := by
  calc
    _ = laws.word r letters (laws.action r a a (laws.action r a b x)) :=
      (laws.word_diagonal r a letters ha _).symm
    _ = laws.word r letters (laws.action r a a (laws.action r r b x)) := by rw [laws.action_weak]
    _ = laws.word r letters (laws.action r r b x) := laws.word_diagonal r a letters ha _

theorem action_terminal (r j t : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.action r r t (laws.action r j t ⊥) = laws.action r r t (laws.constant r j) := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  apply Subtype.ext
  rw [laws.action_root, laws.action_root, laws.action_zero]
  exact laws.terminal r j t

/-- A terminal companion already tested by P contributes no separate source. -/
theorem word_terminal (r j t : M) (letters : List (M × M))
    (ht : (t = r ∨ (∃ c, (t, c) ∈ letters) ∨ ∃ c, (c, t) ∈ letters) ∨ t = j) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.word r letters (laws.action r j t ⊥) = laws.word r letters (laws.constant r j) := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  rcases ht with ht | rfl
  · calc
      _ = laws.word r letters (laws.action r r t (laws.action r j t ⊥)) :=
        (laws.word_root r t letters ht _).symm
      _ = laws.word r letters (laws.action r r t (laws.constant r j)) := by rw [laws.action_terminal]
      _ = laws.word r letters (laws.constant r j) := laws.word_root r t letters ht _
  · have he : laws.action r t t ⊥ = laws.constant r t := by
      apply Subtype.ext
      exact (laws.action_zero r t t).trans (laws.h_minor r t)
    rw [he]

/-- A primitive constant is bounded by the two projected source constants. -/
theorem action_zero_le_constants (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.action r a b ⊥ ≤ laws.constant r a ⊔ laws.constant r b := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  apply Subtype.ext
  have hjoin : f (f (f a r) (f b r)) r = f (f a r) (f b r) := by
    simpa only [laws.R3] using laws.reset_laws.e8 (f a r) (f b r) r
  change f (h r (f r a) b) (f (f a r) (f b r)) = f (f a r) (f b r)
  rw [laws.F_zero]
  simpa only [laws.R3, laws.h_root, hjoin] using laws.terminal_bound r a b

/-- Either source can supply the full pair when its companion test is added. -/
theorem action_zero_le_tested_constant (r a b : M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.action r a b ⊥ ≤ laws.action r r b (laws.constant r a) := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  apply Subtype.ext
  change f (h r (f r a) b) (h r (f (f a r) r) b) = h r (f (f a r) r) b
  rw [laws.R3, laws.F_zero]
  simpa only [laws.h_root] using laws.terminal_weak r a b

end Laws
end KFOL.Owner.FiniteBasis
