/- Generic semantic certificates for the raw-pair hardness reductions.
Native reduction assembly and polynomial size are proved in the paper. -/
import Fragments
set_option autoImplicit false
namespace MinimalChoice.SmallFragments
open ResetCalculus
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def ownedFold {α : Type} (a : α) : List (S α) → S α → S α
  | [], base => base
  | x :: xs, base => own a x (ownedFold a xs base)

theorem ownedFold_ne {α : Type} (a : α) (xs : List (S α)) (base : S α)
    (hb : NE base) (hx : ∀ x ∈ xs, NE x) : NE (ownedFold a xs base) := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    exact own_ne a x _ (hx x (by simp))

theorem ownedFold_eq_owner {α : Type} (a : α) (xs : List (S α)) (base : S α)
    (hb : NE base) (hx : ∀ x ∈ xs, NE x) :
    ownedFold a xs base = atom a ↔ base = atom a ∨ ∃ x ∈ xs, x = atom a := by
  induction xs with
  | nil => simp [ownedFold]
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, NE y := fun y hy => hx y (by simp [hy])
    rw [ownedFold, own_eq_owner_iff a x _ (hx x (by simp)) (ownedFold_ne a xs base hb ht), ih ht]
    simp only [List.mem_cons]
    grind

theorem ownedFold_eq_other {α : Type} (a r : α) (har : a ≠ r)
    (xs : List (S α)) (base : S α) (hb : NE base) (hx : ∀ x ∈ xs, NE x) :
    ownedFold a xs base = atom r ↔ base = atom r ∧ ∀ x ∈ xs, x = atom r := by
  induction xs with
  | nil => simp [ownedFold]
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, NE y := fun y hy => hx y (by simp [hy])
    rw [ownedFold, own_eq_other_iff a r har x _ (hx x (by simp))
      (ownedFold_ne a xs base hb ht), ih ht]
    simp only [List.forall_mem_cons, and_left_comm]

theorem ownedFold_union {α : Type} (a : α) (xs : List (S α)) (base : S α)
    (hne : NE base) (hxs : ∀ x ∈ xs, NE x)
    (hb : base ≠ atom a) (hx : ∀ x ∈ xs, x ≠ atom a) :
    ownedFold a xs base = unions xs base := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, y ≠ atom a := fun y hy => hx y (by simp [hy])
    have htne : ∀ y ∈ xs, NE y := fun y hy => hxs y (by simp [hy])
    have hn : ownedFold a xs base ≠ atom a := by
      intro he
      rcases (ownedFold_eq_owner a xs base hne htne).mp he with he | ⟨y, hy, he⟩
      · exact hb he
      · exact ht y hy he
    simp only [ownedFold, own, hx x (by simp), hn, or_self, ↓reduceIte, unions]
    rw [ih htne ht]

/-- The common absorption argument for raw choice with union, and for
raw choice with a second owner after excluding that owner's collapse. -/
theorem raw_absorption {α : Type} (a : α) (pairs : List (S α × S α))
    (clauses : List (S α)) (M W : S α) (hm : NE M)
    (hpair : ∃ pair, pair ∈ pairs)
    (hp : ∀ pair ∈ pairs, NE pair.1 ∧ NE pair.2)
    (hc : ∀ C ∈ clauses, NE C ∧ Sub C W)
    (hlogic : (∀ C ∈ clauses, C ≠ atom a) →
      ∃ pair ∈ pairs, pair.1 ≠ atom a ∧ pair.2 ≠ atom a) :
    Sub (ownedFold a clauses M)
      (unions (pairs.map (fun pair => own a M (own a pair.1 pair.2))) W) := by
  let R := unions (pairs.map (fun pair => own a M (own a pair.1 pair.2))) W
  have hWR : Sub W R := fun w hw => (unions_mem _ W w).mpr (Or.inl hw)
  have hMR : M ≠ atom a → (∀ C ∈ clauses, C ≠ atom a) → Sub M R := by
    intro hma hcs w hmw
    obtain ⟨pair, hmem, hp1, hp2⟩ := hlogic hcs
    have hn : own a pair.1 pair.2 ≠ atom a := by
      intro he
      rcases (own_eq_owner_iff a _ _ (hp pair hmem).1 (hp pair hmem).2).mp he with he | he
      · exact hp1 he
      · exact hp2 he
    apply (unions_mem _ W w).mpr
    refine Or.inr ⟨own a M (own a pair.1 pair.2), List.mem_map.mpr ⟨pair, hmem, rfl⟩, ?_⟩
    exact own_left_sub a M _ hn w hmw
  by_cases he : ownedFold a clauses M = atom a
  · intro w h
    have hwa : w = a := by
      have hh : atom a w := by rw [← he]; exact h
      exact hh
    subst w
    rcases (ownedFold_eq_owner a clauses M hm (fun C hC => (hc C hC).1)).mp he with hma | ⟨C, hC, hCa⟩
    · obtain ⟨pair, hmem⟩ := hpair
      apply (unions_mem _ W a).mpr
      refine Or.inr ⟨own a M (own a pair.1 pair.2), List.mem_map.mpr ⟨pair, hmem, rfl⟩, ?_⟩
      rw [hma]
      exact (own_mem_owner a _ _).mpr (Or.inl rfl)
    · exact hWR a ((hc C hC).2 a (hCa.symm ▸ (rfl : atom a a)))
  · have hn := mt (ownedFold_eq_owner a clauses M hm (fun C hC => (hc C hC).1)).mpr he
    have hma : M ≠ atom a := fun h => hn (Or.inl h)
    have hcs : ∀ C ∈ clauses, C ≠ atom a := fun C hC h => hn (Or.inr ⟨C, hC, h⟩)
    rw [ownedFold_union a clauses M hm (fun C hC => (hc C hC).1) hma hcs]
    intro w h
    rcases (unions_mem clauses M w).mp h with h | ⟨C, hC, h⟩
    · exact hMR hma hcs w h
    · exact hWR w ((hc C hC).2 w h)

/-- The separate absorption law needed for the second raw owner. -/
theorem raw_second_owner {α : Type} (b : α) (A R : S α)
    (hA : A ≠ atom b) (hR : R ≠ atom b) (hs : Sub A R) : own b A R = R := by
  simp only [own, hA, hR, or_self, ↓reduceIte]
  funext w
  apply propext
  exact ⟨fun h => h.elim (hs w) id, Or.inr⟩

theorem ownedFold_guard_witness {α : Type} (a : α) (xs : List (S α)) (T : S α)
    (hx : ∀ x ∈ xs, NE x) (ht : NE T) (hxs : xs ≠ [])
    (hc : Multiple (ownedFold a xs T)) :
    ∃ x ∈ xs, Multiple (own a x T) := by
  have hn : ownedFold a xs T ≠ atom a := fun he => not_multiple_atom a (he ▸ hc)
  have hn' := mt (ownedFold_eq_owner a xs T ht hx).mpr hn
  have hta : T ≠ atom a := fun h => hn' (Or.inl h)
  have hxa : ∀ x ∈ xs, x ≠ atom a := fun x hh he => hn' (Or.inr ⟨x, hh, he⟩)
  rw [ownedFold_union a xs T ht hx hta hxa] at hc
  rcases atom_or_multiple T ht with ⟨r, hr⟩ | hm
  · subst T
    obtain ⟨x, hh, hxr⟩ := (unions_multiple_atom xs r hx).mp hc
    refine ⟨x, hh, ?_⟩
    have ha : atom r ≠ atom a := hta
    simp only [own, hxa x hh, ha, or_self, ↓reduceIte]
    exact (guard_multiple x r (hx x hh)).mpr hxr
  · have hex : ∃ x, x ∈ xs := by
      cases xs with
      | nil => exact False.elim (hxs rfl)
      | cons x xs => exact ⟨x, by simp⟩
    obtain ⟨x, hh⟩ := hex
    refine ⟨x, hh, ?_⟩
    simp only [own, hxa x hh, hta, or_self, ↓reduceIte]
    exact multiple_mono (fun _ h => Or.inr h) hm

/-- Transfer of UNSAT to the raw owned-choice guards next to reset. -/
theorem owned_guard_logic {α β : Type} (a : α) (F : List (List (Lit β)))
    (P N : β → S α) (T : S α) (ht : NE T)
    (hp : ∀ i, NE (P i)) (hn : ∀ i, NE (N i))
    (hne : ∀ clause ∈ F, clause ≠ []) (hu : ∀ v, ¬ Sat F v)
    (hc : ∀ clause ∈ F, Multiple (ownedFold a
      (clause.map (fun l => if l.2 then P l.1 else N l.1)) T)) :
    ∃ i, Multiple (own a (P i) T) ∧ Multiple (own a (N i) T) := by
  apply unsat_rails F (fun i => Multiple (own a (P i) T))
    (fun i => Multiple (own a (N i) T)) hu
  intro clause hh
  have hs : ∀ x ∈ clause.map (fun l => if l.2 then P l.1 else N l.1), NE x := by
    intro x hm
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hm
    cases l.2 <;> simp [hp, hn]
  have hnil : clause.map (fun l => if l.2 then P l.1 else N l.1) ≠ [] := by
    simpa using hne clause hh
  obtain ⟨x, hm, hx⟩ := ownedFold_guard_witness a _ T hs ht hnil (hc clause hh)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  refine ⟨l, hl, ?_⟩
  cases hb : l.2 <;> simpa [hb] using hx

#print axioms raw_absorption
#print axioms ownedFold_eq_other
#print axioms owned_guard_logic
end MinimalChoice.SmallFragments
