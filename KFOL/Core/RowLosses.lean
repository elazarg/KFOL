module

public import KFOL.Core.BichainRecognition
public import KFOL.Core.SourceLosses

/-! # Losses of the operation of rows

The capped baseline of a family of marked rows has a system of losses: a
selector fails to supply only under the cap, and a row input fails to supply
on the code of a row marking it, with the fixed inputs of that row at their
atoms, and on the two endpoint codes. Hence the prime guards of the operation
are the minimal sets of postings meeting these losses, whether or not the
operation is a term operation.
-/

@[expose] public section

namespace KFOL.Recognition

universe u w

variable {Role : Type u}

open WinnerSet Core.Sources

section Lists

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool)

omit [Fintype Z] [DecidableEq Z] in
theorem mem_lossCap (q : Inp Z W × Role) :
    q ∈ (lossCap three : List (Inp Z W × Role)) ↔ ∃ x : Option W, q = (.inr x, three 0) := by
  simp only [lossCap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  exact exists_congr fun x => eq_comm

omit [DecidableEq Z] in
theorem mem_lossX (q : Inp Z W × Role) :
    q ∈ lossX three X ↔ (∃ u : Z, q = (.inl u, three 2)) ∨
      ∃ x : Option W, endP X x = true ∧ q = (.inr x, three 2) := by
  simp only [lossX, List.mem_append, List.mem_map, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and]
  exact or_congr (exists_congr fun u => eq_comm)
    (exists_congr fun x => and_congr_right fun _ => eq_comm)

omit [DecidableEq Z] in
theorem mem_lossY (q : Inp Z W × Role) :
    q ∈ lossY three Y ↔ (∃ u : Z, q = (.inl u, three 1)) ∨
      ∃ x : Option W, endP Y x = false ∧ q = (.inr x, three 1) := by
  simp only [lossY, List.mem_append, List.mem_map, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and, Bool.not_eq_eq_eq_not, Bool.not_true]
  exact or_congr (exists_congr fun u => eq_comm)
    (exists_congr fun x => and_congr_right fun _ => eq_comm)

theorem mem_lossRow (z : Z) (q : Inp Z W × Role) :
    q ∈ lossRow three rows z ↔
      (∃ u : Z, q = (.inl u, if u = z then three 1 else three 2)) ∨
      (∃ x : Option W, rowP rows z x = .b ∧ q = (.inr x, three 1)) ∨
      ∃ x : Option W, rowP rows z x = .c ∧ q = (.inr x, three 2) := by
  simp only [lossRow, List.mem_append, List.mem_map, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and, decide_eq_true_eq, or_assoc]
  exact or_congr (exists_congr fun u => eq_comm)
    (or_congr (exists_congr fun x => and_congr_right fun _ => eq_comm)
      (exists_congr fun x => and_congr_right fun _ => eq_comm))

theorem mem_losses_inl (u : Z) (z : List (Inp Z W × Role)) :
    z ∈ losses three rows X Y (.inl u) ↔ z = lossCap three := by
  simp [losses]

theorem mem_losses_inr (x : Option W) (z : List (Inp Z W × Role)) :
    z ∈ losses three rows X Y (.inr x) ↔
      (endP X x = false ∧ z = lossX three X) ∨ (endP Y x = true ∧ z = lossY three Y) ∨
      ∃ z' : Z, rowP rows z' x = .possible ∧ z = lossRow three rows z' := by
  simp only [losses, List.mem_append, List.mem_map, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and, decide_eq_true_eq, or_assoc]
  refine or_congr ?_ (or_congr ?_ (exists_congr fun z' => and_congr_right fun _ => eq_comm))
  · cases endP X x <;> simp
  · cases endP Y x <;> simp

omit [Fintype Z] [DecidableEq Z] in
theorem posted_lossCap (k : Role) (v : Inp Z W → WinnerSet Role) :
    Posted (lossCap three : List (Inp Z W × Role)) k v ↔
      three 0 ≠ k ∧ ∀ x : Option W, v (.inr x) = singleton (three 0) := by
  constructor
  · intro h
    exact ⟨(h _ ((mem_lossCap three _).2 ⟨none, rfl⟩)).1,
      fun x => (h _ ((mem_lossCap three _).2 ⟨x, rfl⟩)).2⟩
  · rintro ⟨h1, h2⟩ q hq
    obtain ⟨x, rfl⟩ := (mem_lossCap three q).1 hq
    exact ⟨h1, h2 x⟩

omit [DecidableEq Z] in
theorem posted_lossX (k : Role) (v : Inp Z W → WinnerSet Role) :
    Posted (lossX three X) k v ↔
      (∀ u : Z, three 2 ≠ k ∧ v (.inl u) = singleton (three 2)) ∧
      ∀ x : Option W, endP X x = true → three 2 ≠ k ∧ v (.inr x) = singleton (three 2) := by
  constructor
  · intro h
    exact ⟨fun u => h _ ((mem_lossX three X _).2 (Or.inl ⟨u, rfl⟩)),
      fun x hx => h _ ((mem_lossX three X _).2 (Or.inr ⟨x, hx, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ q hq
    rcases (mem_lossX three X q).1 hq with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩
    · exact h1 u
    · exact h2 x hx

omit [DecidableEq Z] in
theorem posted_lossY (k : Role) (v : Inp Z W → WinnerSet Role) :
    Posted (lossY three Y) k v ↔
      (∀ u : Z, three 1 ≠ k ∧ v (.inl u) = singleton (three 1)) ∧
      ∀ x : Option W, endP Y x = false → three 1 ≠ k ∧ v (.inr x) = singleton (three 1) := by
  constructor
  · intro h
    exact ⟨fun u => h _ ((mem_lossY three Y _).2 (Or.inl ⟨u, rfl⟩)),
      fun x hx => h _ ((mem_lossY three Y _).2 (Or.inr ⟨x, hx, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ q hq
    rcases (mem_lossY three Y q).1 hq with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩
    · exact h1 u
    · exact h2 x hx

theorem posted_lossRow (z : Z) (k : Role) (v : Inp Z W → WinnerSet Role) :
    Posted (lossRow three rows z) k v ↔
      (three 1 ≠ k ∧ v (.inl z) = singleton (three 1)) ∧
      (∀ u : Z, u ≠ z → three 2 ≠ k ∧ v (.inl u) = singleton (three 2)) ∧
      (∀ x : Option W, rowP rows z x = .b → three 1 ≠ k ∧ v (.inr x) = singleton (three 1)) ∧
      ∀ x : Option W, rowP rows z x = .c → three 2 ≠ k ∧ v (.inr x) = singleton (three 2) := by
  constructor
  · intro h
    refine ⟨?_, fun u hu => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simpa using h _ ((mem_lossRow three rows z _).2 (Or.inl ⟨z, rfl⟩))
    · simpa [hu] using h _ ((mem_lossRow three rows z _).2 (Or.inl ⟨u, rfl⟩))
    · exact h _ ((mem_lossRow three rows z _).2 (Or.inr (Or.inl ⟨x, hx, rfl⟩)))
    · exact h _ ((mem_lossRow three rows z _).2 (Or.inr (Or.inr ⟨x, hx, rfl⟩)))
  · rintro ⟨h1, h2, h3, h4⟩ q hq
    rcases (mem_lossRow three rows z q).1 hq with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · by_cases hu : u = z
      · subst hu
        simpa using h1
      · simpa [hu] using h2 u hu
    · exact h3 x hx
    · exact h4 x hx

theorem not_posted_losses_inr (x : Option W) (k : Role) (v : Inp Z W → WinnerSet Role) :
    (∀ z ∈ losses three rows X Y (.inr x), ¬Posted z k v) ↔
      (endP X x = false → ¬Posted (lossX three X) k v) ∧
      (endP Y x = true → ¬Posted (lossY three Y) k v) ∧
      ∀ z : Z, rowP rows z x = .possible → ¬Posted (lossRow three rows z) k v := by
  constructor
  · intro h
    exact ⟨fun hx => h _ ((mem_losses_inr three rows X Y x _).2 (Or.inl ⟨hx, rfl⟩)),
      fun hx => h _ ((mem_losses_inr three rows X Y x _).2 (Or.inr (Or.inl ⟨hx, rfl⟩))),
      fun z hz => h _ ((mem_losses_inr three rows X Y x _).2 (Or.inr (Or.inr ⟨z, hz, rfl⟩)))⟩
  · rintro ⟨h1, h2, h3⟩ z hz
    rcases (mem_losses_inr three rows X Y x z).1 hz with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨z', hz', rfl⟩
    · exact h1 hx
    · exact h2 hx
    · exact h3 z' hz'

end Lists

section Supply

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)
  (v : Inp Z W → WinnerSet Role) {k : Role} {x : Option W}

omit [Fintype Z] [DecidableEq Z] [Fintype W] in
/-- The selectors are not all atoms of the two owners, or two are at the
second owner and one at the third, or they form one of the three codes. -/
theorem selector_cases :
    (∃ u : Z, v (.inl u) ≠ singleton (three 1) ∧ v (.inl u) ≠ singleton (three 2)) ∨
    (∃ z u2 u3 : Z, u2 ≠ z ∧ v (.inl z) = singleton (three 1) ∧
      v (.inl u2) = singleton (three 1) ∧ v (.inl u3) = singleton (three 2)) ∨
    (∀ u : Z, v (.inl u) = singleton (three 1)) ∨
    (∀ u : Z, v (.inl u) = singleton (three 2)) ∨
    ∃ z : Z, v (.inl z) = singleton (three 1) ∧
      ∀ u : Z, u ≠ z → v (.inl u) = singleton (three 2) := by
  classical
  by_cases hjunk : ∃ u : Z, v (.inl u) ≠ singleton (three 1) ∧ v (.inl u) ≠ singleton (three 2)
  · exact Or.inl hjunk
  have hatom : ∀ u : Z, v (.inl u) = singleton (three 1) ∨ v (.inl u) = singleton (three 2) := by
    intro u
    by_contra h
    exact hjunk ⟨u, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  by_cases hsomeb : ∃ z : Z, v (.inl z) = singleton (three 1)
  · obtain ⟨z, hz⟩ := hsomeb
    by_cases hsecond : ∃ u : Z, u ≠ z ∧ v (.inl u) = singleton (three 1)
    · obtain ⟨u2, hu2, hv2⟩ := hsecond
      by_cases hsomec : ∃ u3 : Z, v (.inl u3) = singleton (three 2)
      · obtain ⟨u3, hv3⟩ := hsomec
        exact Or.inr (Or.inl ⟨z, u2, u3, hu2, hz, hv2, hv3⟩)
      · exact Or.inr (Or.inr (Or.inl fun u =>
          (hatom u).resolve_right fun h => hsomec ⟨u, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z, hz, fun u hu =>
        (hatom u).resolve_left fun h => hsecond ⟨u, hu, h⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl fun u =>
      (hatom u).resolve_left fun h => hsomeb ⟨u, h⟩)))

variable (hx : k ∈ (v (.inr x)).val)
include hx

theorem supply_junk (u : Z) (hu1 : v (.inl u) ≠ singleton (three 1))
    (hu2 : v (.inl u) ≠ singleton (three 2)) :
    k ∈ ((baseline three rows X Y z₀).eval v).val :=
  (mem_baseline three rows X Y z₀ v k).2
    (Or.inr (Or.inl ⟨(u, x), mem_choice_left (mem_choice_left hx hu1) hu2⟩))

theorem supply_two (z u2 u3 : Z) (hu2 : u2 ≠ z) (hz : v (.inl z) = singleton (three 1))
    (hv2 : v (.inl u2) = singleton (three 1)) (hv3 : v (.inl u3) = singleton (three 2)) :
    k ∈ ((baseline three rows X Y z₀).eval v).val := by
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hbc : (singleton (three 1) : WinnerSet Role) ≠ singleton (three 2) :=
    fun h => h12 (singleton_inj.1 h)
  refine (mem_baseline three rows X Y z₀ v k).2 (Or.inr (Or.inr (Or.inl ⟨(z, u2, u3, x), ?_⟩)))
  have e : u2T three (z, u2, u3, x) = (.choice (three 1) (.choice (three 2)
      (.choice (three 2) (.var (.inr x)) (.var (.inl z))) (.var (.inl u2)))
      (.var (.inl u3)) : Term Role (Inp Z W)) := by
    simp [u2T, Ne.symm hu2]
  rw [e]
  refine mem_choice_left (mem_choice_left (mem_choice_left hx ?_) ?_) ?_
  · exact fun h => hbc (hz.symm.trans h)
  · exact fun h => hbc (hv2.symm.trans h)
  · exact fun h => hbc.symm (hv3.symm.trans h)

theorem supply_Y (hall : ∀ u : Z, v (.inl u) = singleton (three 1)) (i₀ : Option W)
    (hi₀ : endP Y i₀ = false)
    (hne : endP Y x = true → v (.inr i₀) ≠ singleton (three 1)) :
    k ∈ ((baseline three rows X Y z₀).eval v).val := by
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hbc : (singleton (three 1) : WinnerSet Role) ≠ singleton (three 2) :=
    fun h => h12 (singleton_inj.1 h)
  refine (mem_baseline three rows X Y z₀ v k).2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(x, i₀), ?_⟩)))))
  have hnc : ∀ u ∈ (Finset.univ : Finset Z).toList,
      v (.inl u) ≠ singleton (three 2) := fun u _ => by
    rw [hall u]; exact hbc
  by_cases hx' : endP Y x = false
  · have e : kyT three Y z₀ (x, i₀) = KY three (.var (.inr x)) := by simp [kyT, hx']
    rw [e]
    exact foldSel_supply _ _ _ _ _ hx hnc
  · have hx'' : endP Y x = true := by simpa using hx'
    have e : kyT three Y z₀ (x, i₀) =
        KY three (.choice (three 1) (.var (.inr x)) (.var (.inr i₀))) := by
      simp [kyT, hx'', hi₀]
    rw [e]
    exact foldSel_supply _ _ _ _ _ (mem_choice_left hx (hne hx'')) hnc

theorem supply_X (hall : ∀ u : Z, v (.inl u) = singleton (three 2)) (i₀ : Option W)
    (hi₀ : endP X i₀ = true)
    (hne : endP X x = false → v (.inr i₀) ≠ singleton (three 2)) :
    k ∈ ((baseline three rows X Y z₀).eval v).val := by
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hbc : (singleton (three 1) : WinnerSet Role) ≠ singleton (three 2) :=
    fun h => h12 (singleton_inj.1 h)
  refine (mem_baseline three rows X Y z₀ v k).2
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨(x, i₀), ?_⟩))))
  have hnb : ∀ u ∈ (Finset.univ : Finset Z).toList,
      v (.inl u) ≠ singleton (three 1) := fun u _ => by
    rw [hall u]; exact hbc.symm
  by_cases hx' : endP X x = true
  · have e : kxT three X z₀ (x, i₀) = KX three (.var (.inr x)) := by simp [kxT, hx']
    rw [e]
    exact foldSel_supply _ _ _ _ _ hx hnb
  · have hx'' : endP X x = false := by simpa using hx'
    have e : kxT three X z₀ (x, i₀) =
        KX three (.choice (three 2) (.var (.inr x)) (.var (.inr i₀))) := by
      simp [kxT, hx'', hi₀]
    rw [e]
    exact foldSel_supply _ _ _ _ _ (mem_choice_left hx (hne hx'')) hnb

theorem supply_row (z : Z) (hz : v (.inl z) = singleton (three 1))
    (hoth : ∀ u : Z, u ≠ z → v (.inl u) = singleton (three 2))
    (h : rowP rows z x ≠ .possible ∨ ∃ i : Option W,
      (rowP rows z i = .b ∧ v (.inr i) ≠ singleton (three 1)) ∨
      (rowP rows z i = .c ∧ v (.inr i) ≠ singleton (three 2))) :
    k ∈ ((baseline three rows X Y z₀).eval v).val := by
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hbc : (singleton (three 1) : WinnerSet Role) ≠ singleton (three 2) :=
    fun h => h12 (singleton_inj.1 h)
  have supply : ∀ y : Term Role (Inp Z W), k ∈ (y.eval v).val →
      k ∈ ((Kz three z y).eval v).val := fun y hy =>
    foldSel_supply _ _ _ _ _ (mem_choice_left hy fun h => hbc (hz.symm.trans h))
      (fun u hu => by
        rw [hoth u (Finset.ne_of_mem_erase (Finset.mem_toList.1 hu))]
        exact hbc.symm)
  have kz : ∀ q, k ∈ ((kzT three rows z₀ q).eval v).val →
      k ∈ ((baseline three rows X Y z₀).eval v).val := fun q h =>
    (mem_baseline three rows X Y z₀ v k).2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h⟩))))))
  by_cases hx' : rowP rows z x = .possible
  · obtain ⟨i, hi | hi⟩ := h.resolve_left fun hn => hn hx'
    · refine kz (z, x, i) ?_
      have e : kzT three rows z₀ (z, x, i) =
          Kz three z (.choice (three 1) (.var (.inr x)) (.var (.inr i))) := by
        simp [kzT, hx', hi.1]
      rw [e]
      exact supply _ (mem_choice_left hx hi.2)
    · refine kz (z, x, i) ?_
      have e : kzT three rows z₀ (z, x, i) =
          Kz three z (.choice (three 2) (.var (.inr x)) (.var (.inr i))) := by
        simp [kzT, hx', hi.1]
      rw [e]
      exact supply _ (mem_choice_left hx hi.2)
  · refine kz (z, x, x) ?_
    have e : kzT three rows z₀ (z, x, x) = Kz three z (.var (.inr x)) := by
      simp [kzT, hx']
    rw [e]
    exact supply _ hx

end Supply

section Main

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Nontrivial Z] [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)

/-- **Losses of the operation of rows.** The capped baseline is supplied by
its inputs, and each input fails exactly on its listed losses. -/
theorem target_lossSystem (hX : ∃ j : W, X j = true) :
    LossSystem (target three rows X Y z₀) (losses three rows X Y) where
  mem_iff := by
    classical
    have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
    have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
    have hbc : (WinnerSet.singleton (three 1) : WinnerSet Role) ≠ WinnerSet.singleton (three 2) :=
      fun h => h12 (singleton_inj.1 h)
    intro v k
    have mem := mem_baseline three rows X Y z₀ v k
    constructor
    · intro hk
      by_cases hcap : ∀ x : Option W, v (.inr x) = WinnerSet.singleton (three 0)
      · have ht : target three rows X Y z₀ v = WinnerSet.singleton (three 0) := by
          simp only [target, hcap, implies_true, ↓reduceIte]
        rw [ht] at hk
        obtain rfl : k = three 0 := hk
        refine ⟨.inr none, by rw [hcap none]; exact Set.mem_singleton _, ?_⟩
        rw [not_posted_losses_inr]
        refine ⟨fun _ hp => ?_, fun h => (by cases h), fun z hz => (by cases hz)⟩
        obtain ⟨j, hj⟩ := hX
        have h := ((posted_lossX three X _ v).1 hp).2 (some j) hj
        exact h02 (singleton_inj.1 ((hcap (some j)).symm.trans h.2))
      · have ht : target three rows X Y z₀ v = (baseline three rows X Y z₀).eval v := by
          simp only [target, hcap, ↓reduceIte]
        rw [ht] at hk
        by_cases hs : ∃ u : Z, k ∈ (v (.inl u)).val
        · obtain ⟨u, hu⟩ := hs
          refine ⟨.inl u, hu, fun z hz hp => ?_⟩
          rw [(mem_losses_inl three rows X Y u z).1 hz] at hp
          exact hcap ((posted_lossCap three k v).1 hp).2
        · by_contra hno
          have blocked : ∀ x : Option W, k ∈ (v (.inr x)).val →
              (endP X x = false ∧ Posted (lossX three X) k v) ∨
              (endP Y x = true ∧ Posted (lossY three Y) k v) ∨
              ∃ z : Z, rowP rows z x = .possible ∧ Posted (lossRow three rows z) k v := by
            intro x hx
            by_contra hnb
            refine hno ⟨.inr x, hx, ?_⟩
            rw [not_posted_losses_inr]
            exact ⟨fun h hp => hnb (Or.inl ⟨h, hp⟩), fun h hp => hnb (Or.inr (Or.inl ⟨h, hp⟩)),
              fun z hz hp => hnb (Or.inr (Or.inr ⟨z, hz, hp⟩))⟩
          obtain ⟨j, hj, -⟩ := (membership_iff_source three _
            (baseline_isCore three rows X Y z₀) v k).1 hk
          cases j with
          | inl u => exact hs ⟨u, hj⟩
          | inr x₀ =>
            rcases blocked x₀ hj with ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨z, -, hp⟩
            · obtain ⟨h1, h2⟩ := (posted_lossX three X k v).1 hp
              have hkc : k = three 2 := baseline_sub_X three rows X Y z₀ v
                (fun u => (h1 u).2) (fun x hx => (h2 x hx).2) hk
              exact (h1 z₀).1 hkc.symm
            · obtain ⟨h1, h2⟩ := (posted_lossY three Y k v).1 hp
              have hkb : k = three 1 := baseline_sub_Y three rows X Y z₀ v
                (fun u => (h1 u).2) (fun x hx => (h2 x hx).2) hk
              exact (h1 z₀).1 hkb.symm
            · obtain ⟨h1, h2, h3, h4⟩ := (posted_lossRow three rows z k v).1 hp
              obtain ⟨u', hu'⟩ := exists_ne z
              have hfree : ∀ x, rowP rows z x ≠ .possible →
                  (v (.inr x)).val ⊆ {k' | k' ≠ k} := by
                intro x hxz k' hk' hkk
                obtain rfl : k' = k := hkk
                rcases blocked x hk' with ⟨-, hp'⟩ | ⟨-, hp'⟩ | ⟨z', hz', hp'⟩
                · have h := ((posted_lossX three X _ v).1 hp').1 z
                  exact hbc (h1.2.symm.trans h.2)
                · have h := ((posted_lossY three Y _ v).1 hp').1 u'
                  exact hbc (h.2.symm.trans (h2 u' hu').2)
                · have h := ((posted_lossRow three rows z' _ v).1 hp').1
                  by_cases e : z' = z
                  · subst e
                    exact hxz hz'
                  · exact hbc (h.2.symm.trans (h2 z' e).2)
              exact baseline_sub_row three rows X Y z₀ z v {k' | k' ≠ k} h1.1 (h2 u' hu').1
                h1.2 (fun u hu => (h2 u hu).2) (fun x hx => (h3 x hx).2)
                (fun x hx => (h4 x hx).2) hfree hk rfl
    · rintro ⟨j, hj, hz⟩
      by_cases hcap : ∀ x : Option W, v (.inr x) = WinnerSet.singleton (three 0)
      · have ht : target three rows X Y z₀ v = WinnerSet.singleton (three 0) := by
          simp only [target, hcap, implies_true, ↓reduceIte]
        rw [ht]
        cases j with
        | inl u =>
          by_contra hne
          refine hz (lossCap three) ((mem_losses_inl three rows X Y u _).2 rfl)
            ((posted_lossCap three k v).2 ⟨fun h => hne ?_, hcap⟩)
          rw [← h]
          exact Set.mem_singleton _
        | inr x =>
          rw [hcap x] at hj
          exact hj
      · have ht : target three rows X Y z₀ v = (baseline three rows X Y z₀).eval v := by
          simp only [target, hcap, ↓reduceIte]
        rw [ht]
        cases j with
        | inl u => exact mem.2 (Or.inl ⟨u, hj⟩)
        | inr x =>
          rw [not_posted_losses_inr] at hz
          obtain ⟨hzX, hzY, hzR⟩ := hz
          rcases selector_cases three v with ⟨u, hu1, hu2⟩ |
            ⟨z, u2, u3, hu2, hz1, hv2, hv3⟩ | hall | hall | ⟨z, hz1, hoth⟩
          · exact supply_junk three rows X Y z₀ v hj u hu1 hu2
          · exact supply_two three rows X Y z₀ v hj z u2 u3 hu2 hz1 hv2 hv3
          · by_cases hkb : k = three 1
            · exact mem.2 (Or.inl ⟨z₀, by rw [hall z₀, hkb]; exact Set.mem_singleton _⟩)
            by_cases hxY : endP Y x = true
            · have hnp := hzY hxY
              rw [posted_lossY] at hnp
              have hex : ∃ i, endP Y i = false ∧ v (.inr i) ≠ WinnerSet.singleton (three 1) := by
                by_contra hc
                push Not at hc
                exact hnp ⟨fun u => ⟨Ne.symm hkb, hall u⟩, fun i hi => ⟨Ne.symm hkb, hc i hi⟩⟩
              obtain ⟨i, hi, hne⟩ := hex
              exact supply_Y three rows X Y z₀ v hj hall i hi (fun _ => hne)
            · have hxY' : endP Y x = false := by simpa using hxY
              exact supply_Y three rows X Y z₀ v hj hall x hxY' (fun h => absurd h hxY)
          · by_cases hkc : k = three 2
            · exact mem.2 (Or.inl ⟨z₀, by rw [hall z₀, hkc]; exact Set.mem_singleton _⟩)
            by_cases hxX : endP X x = true
            · exact supply_X three rows X Y z₀ v hj hall x hxX
                (fun h => by rw [hxX] at h; cases h)
            · have hxX' : endP X x = false := by simpa using hxX
              have hnp := hzX hxX'
              rw [posted_lossX] at hnp
              have hex : ∃ i, endP X i = true ∧ v (.inr i) ≠ WinnerSet.singleton (three 2) := by
                by_contra hc
                push Not at hc
                exact hnp ⟨fun u => ⟨Ne.symm hkc, hall u⟩, fun i hi => ⟨Ne.symm hkc, hc i hi⟩⟩
              obtain ⟨i, hi, hne⟩ := hex
              exact supply_X three rows X Y z₀ v hj hall i hi (fun _ => hne)
          · by_cases hkb : k = three 1
            · exact mem.2 (Or.inl ⟨z, by rw [hz1, hkb]; exact Set.mem_singleton _⟩)
            by_cases hkc : k = three 2
            · obtain ⟨u', hu'⟩ := exists_ne z
              exact mem.2 (Or.inl ⟨u', by rw [hoth u' hu', hkc]; exact Set.mem_singleton _⟩)
            by_cases hxz : rowP rows z x = .possible
            · have hnp := hzR z hxz
              rw [posted_lossRow] at hnp
              have hex : ∃ i, (rowP rows z i = .b ∧ v (.inr i) ≠ WinnerSet.singleton (three 1)) ∨
                  (rowP rows z i = .c ∧ v (.inr i) ≠ WinnerSet.singleton (three 2)) := by
                by_contra hc
                refine hnp ⟨⟨Ne.symm hkb, hz1⟩, fun u hu => ⟨Ne.symm hkc, hoth u hu⟩,
                  fun i hi => ⟨Ne.symm hkb, ?_⟩, fun i hi => ⟨Ne.symm hkc, ?_⟩⟩
                · by_contra hne
                  exact hc ⟨i, Or.inl ⟨hi, hne⟩⟩
                · by_contra hne
                  exact hc ⟨i, Or.inr ⟨hi, hne⟩⟩
              exact supply_row three rows X Y z₀ v hj z hz1 hoth (Or.inr hex)
            · exact supply_row three rows X Y z₀ v hj z hz1 hoth (Or.inl hxz)
  off_source := by
    rintro (u | x) z hz q hq
    · rw [(mem_losses_inl three rows X Y u z).1 hz] at hq
      obtain ⟨y, rfl⟩ := (mem_lossCap three q).1 hq
      exact fun h => by cases h
    · rcases (mem_losses_inr three rows X Y x z).1 hz with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨z', hz', rfl⟩
      · rcases (mem_lossX three X q).1 hq with ⟨u, rfl⟩ | ⟨y, hy, rfl⟩
        · exact fun h => by cases h
        · intro h
          obtain rfl : y = x := Sum.inr.inj h
          rw [hx] at hy
          cases hy
      · rcases (mem_lossY three Y q).1 hq with ⟨u, rfl⟩ | ⟨y, hy, rfl⟩
        · exact fun h => by cases h
        · intro h
          obtain rfl : y = x := Sum.inr.inj h
          rw [hx] at hy
          cases hy
      · rcases (mem_lossRow three rows z' q).1 hq with ⟨u, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
        · exact fun h => by cases h
        · intro h
          obtain rfl : y = x := Sum.inr.inj h
          rw [hz'] at hy
          cases hy
        · intro h
          obtain rfl : y = x := Sum.inr.inj h
          rw [hz'] at hy
          cases hy
  functional := by
    rintro (u | x) z hz q hq q' hq' hqq
    · rw [(mem_losses_inl three rows X Y u z).1 hz] at hq hq'
      obtain ⟨y, rfl⟩ := (mem_lossCap three q).1 hq
      obtain ⟨y', rfl⟩ := (mem_lossCap three q').1 hq'
      rfl
    · rcases (mem_losses_inr three rows X Y x z).1 hz with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨z', -, rfl⟩
      · rcases (mem_lossX three X q).1 hq with ⟨u, rfl⟩ | ⟨y, -, rfl⟩ <;>
          rcases (mem_lossX three X q').1 hq' with ⟨u', rfl⟩ | ⟨y', -, rfl⟩ <;> rfl
      · rcases (mem_lossY three Y q).1 hq with ⟨u, rfl⟩ | ⟨y, -, rfl⟩ <;>
          rcases (mem_lossY three Y q').1 hq' with ⟨u', rfl⟩ | ⟨y', -, rfl⟩ <;> rfl
      · rcases (mem_lossRow three rows z' q).1 hq with ⟨u, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
          rcases (mem_lossRow three rows z' q').1 hq' with
            ⟨u', rfl⟩ | ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
        · obtain rfl : u = u' := Sum.inl.inj hqq
          rfl
        · cases hqq
        · cases hqq
        · cases hqq
        · rfl
        · obtain rfl : y = y' := Sum.inr.inj hqq
          rw [hy] at hy'
          cases hy'
        · cases hqq
        · obtain rfl : y = y' := Sum.inr.inj hqq
          rw [hy] at hy'
          cases hy'
        · rfl

omit [Nontrivial Z] in
/-- An input has at most two losses besides those of the rows marking it. -/
theorem length_losses_le (j : Inp Z W) :
    (losses three rows X Y j).length ≤ 2 + match j with
      | .inl _ => 0
      | .inr x => (Finset.univ.filter fun z : Z => rowP rows z x = .possible).card := by
  classical
  cases j with
  | inl u => simp [losses]
  | inr x =>
    have e : ((Finset.univ : Finset Z).toList.filter fun z =>
        decide (rowP rows z x = .possible)).length =
        (Finset.univ.filter fun z : Z => rowP rows z x = .possible).card := by
      rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _)]
      congr 1
      ext z
      simp
    simp only [losses, List.length_append, List.length_map, e]
    cases endP X x <;> cases endP Y x <;> simp

end Main

end KFOL.Recognition
