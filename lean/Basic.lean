/-
Small role-owned choice: generic extensional algebra and single-use bounds.
No Mathlib dependency. See the paper (main.tex) for the SPE interpretation and the
mathematical correspondence between syntax occurrences and context paths.
-/

import Std
set_option autoImplicit false
namespace MinimalChoice
abbrev S (α : Type) := α → Prop
def atom {α : Type} (r : α) : S α := fun x => x = r
def join {α : Type} (A B : S α) : S α := fun x => A x ∨ B x
noncomputable def own {α : Type} (r : α) (A B : S α) : S α := by
  classical
  exact if A = atom r ∨ B = atom r then atom r else join A B

theorem atom_inj {α : Type} {r s : α} : atom r = atom s ↔ r = s := by
  constructor
  · intro h
    have hx : atom r r := rfl
    rw [h] at hx
    exact hx
  · intro h
    subst s
    rfl

theorem own_idem {α : Type} (r : α) (A : S α) : own r A A = A := by
  classical
  unfold own
  split
  · rename_i h
    rcases h with h | h <;> exact h.symm
  · funext x
    apply propext
    exact ⟨fun h => h.elim id id, Or.inl⟩

theorem own_comm {α : Type} (r : α) (A B : S α) :
    own r A B = own r B A := by
  classical
  by_cases h : A = atom r ∨ B = atom r
  · have h' : B = atom r ∨ A = atom r := h.symm
    simp [own, h, h']
  · have h' : ¬(B = atom r ∨ A = atom r) := fun e => h e.symm
    simp only [own, ite_eq_right h, ite_eq_right h']
    funext x
    apply propext
    exact Or.comm

theorem join_atom_of_mem {α : Type} (r : α) (A : S α) (h : A r) :
    join (atom r) A = A := by
  funext x
  apply propext
  constructor
  · intro hx
    rcases hx with hx | hx
    · change x = r at hx
      subst x
      exact h
    · exact hx
  · exact Or.inr

theorem own_atom_join {α : Type} (r t : α) (hrt : r ≠ t)
    (A : S α) (h : A r) : own t (atom r) A = A := by
  classical
  have h1 : atom r ≠ atom t := fun e => hrt (atom_inj.mp e)
  have h2 : A ≠ atom t := by
    intro e
    have ht : atom t r := e ▸ h
    exact hrt ht
  simpa [own, h1, h2] using join_atom_of_mem r A h

theorem three_owner_join {α : Type} (r s t : α)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (A B : S α) :
    own t (own r A B) (own s A B) = join A B := by
  classical
  by_cases hr : A = atom r ∨ B = atom r
  · by_cases hs : A = atom s ∨ B = atom s
    · rcases hr with ha | hb
      · rcases hs with hc | hd
        · exact False.elim (hrs (atom_inj.mp (ha.symm.trans hc)))
        · rw [ha, hd]
          simp [own, atom_inj, hrs, Ne.symm hrs, hrt, hst]
      · rcases hs with hc | hd
        · rw [hc, hb]
          simp [own, atom_inj, hrs, Ne.symm hrs, hrt, hst]
          funext x
          apply propext
          exact Or.comm
        · exact False.elim (hrs (atom_inj.mp (hb.symm.trans hd)))
    · have hm : join A B r := by
        rcases hr with ha | hb
        · exact Or.inl (ha ▸ (rfl : atom r r))
        · exact Or.inr (hb ▸ (rfl : atom r r))
      rw [show own r A B = atom r from by simp [own, hr]]
      rw [show own s A B = join A B from by simp [own, hs]]
      exact own_atom_join r t hrt (join A B) hm
  · by_cases hs : A = atom s ∨ B = atom s
    · have hm : join A B s := by
        rcases hs with ha | hb
        · exact Or.inl (ha ▸ (rfl : atom s s))
        · exact Or.inr (hb ▸ (rfl : atom s s))
      rw [show own r A B = join A B from by simp [own, hr]]
      rw [show own s A B = atom s from by simp [own, hs]]
      rw [own_comm]
      exact own_atom_join s t hst (join A B) hm
    · rw [show own r A B = join A B from by simp [own, hr]]
      rw [show own s A B = join A B from by simp [own, hs]]
      exact own_idem t (join A B)
def NE {α : Type} (A : S α) : Prop := ∃ x, A x
def Sub {α : Type} (A B : S α) : Prop := ∀ x, A x → B x

theorem atom_ne {α : Type} (r : α) : NE (atom r) := ⟨r, rfl⟩

theorem own_left_sub {α : Type} (r : α) (A B : S α)
    (hB : B ≠ atom r) : Sub A (own r A B) := by
  classical
  unfold own
  split
  · rename_i h
    rcases h with h | h
    · intro x hx
      exact h ▸ hx
    · exact False.elim (hB h)
  · intro x hx
    exact Or.inl hx

theorem eq_atom_of_ne_sub {α : Type} (r : α) (A : S α)
    (hne : NE A) (hsub : Sub A (atom r)) : A = atom r := by
  funext x
  apply propext
  constructor
  · exact hsub x
  · intro hx
    rcases hne with ⟨y, hy⟩
    have hyr : y = r := hsub y hy
    change x = r at hx
    subst y
    subst x
    exact hy

theorem exists_outside {α : Type} (r : α) (A : S α)
    (hne : NE A) (hnot : A ≠ atom r) : ∃ k, A k ∧ k ≠ r := by
  classical
  apply Classical.byContradiction
  intro h
  apply hnot
  apply eq_atom_of_ne_sub r A hne
  intro k hk
  change k = r
  apply Classical.byContradiction
  intro hkr
  exact h ⟨k, hk, hkr⟩

abbrev Frame (α : Type) := α × (S α → S α)
noncomputable def path {α : Type} (p : List (Frame α)) (A B : S α) : S α :=
  match p with
  | [] => A
  | (r, g) :: rest => path rest (own r A (g B)) B

def Live {α : Type} (p : List (Frame α)) (B : S α) : Prop :=
  ∀ f ∈ p, f.2 B ≠ atom f.1

theorem live_or_constant {α : Type} (p : List (Frame α)) (B : S α) :
    Live p B ∨ ∃ C, ∀ A, path p A B = C := by
  classical
  induction p with
  | nil =>
    left
    intro f hf
    simp at hf
  | cons f rest ih =>
    rcases f with ⟨r, g⟩
    rcases ih with hl | ⟨C, hc⟩
    · by_cases h : g B = atom r
      · right
        refine ⟨path rest (atom r) B, ?_⟩
        intro A
        simp [path, own, h]
      · left
        intro f hf
        rcases List.mem_cons.mp hf with he | he
        · subst f
          exact h
        · exact hl f he
    · right
      exact ⟨C, fun A => hc (own r A (g B))⟩

theorem live_inflates {α : Type} (p : List (Frame α)) (B : S α)
    (hl : Live p B) (A : S α) : Sub A (path p A B) := by
  induction p generalizing A with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    rcases f with ⟨r, g⟩
    have hfirst : g B ≠ atom r := hl (r, g) (by simp)
    have hrest : Live rest B := fun f hf => hl f (List.mem_cons_of_mem _ hf)
    intro x hx
    exact ih hrest (own r A (g B)) x (own_left_sub r A (g B) hfirst x hx)

theorem live_of_union {α : Type} (p : List (Frame α))
    (hrep : ∀ A B, NE A → NE B → path p A B = join A B)
    (r k : α) (hkr : k ≠ r) : Live p (atom r) := by
  rcases live_or_constant p (atom r) with hl | ⟨C, hc⟩
  · exact hl
  · exfalso
    have e : path p (atom r) (atom r) = path p (atom k) (atom r) :=
      (hc (atom r)).trans (hc (atom k)).symm
    rw [hrep _ _ (atom_ne r) (atom_ne r), hrep _ _ (atom_ne k) (atom_ne r)] at e
    have bad := congrArg (fun V : S α => V k) e
    simp [join, atom, hkr] at bad

theorem third_outside {α : Type}
    (others : ∀ r : α, ∃ u v, u ≠ r ∧ v ≠ r ∧ u ≠ v)
    (r k : α) : ∃ j, j ≠ r ∧ j ≠ k := by
  classical
  rcases others r with ⟨u, v, hur, hvr, huv⟩
  by_cases h : u = k
  · exact ⟨v, hvr, fun e => huv (h.trans e.symm)⟩
  · exact ⟨u, hur, h⟩

/-- Every nonempty side function is allowed, so the bound is stronger than
    nondefinability for syntactic game contexts. -/
theorem no_single_use_union {α : Type} (base : α)
    (others : ∀ r : α, ∃ u v, u ≠ r ∧ v ≠ r ∧ u ≠ v)
    (p : List (Frame α))
    (hsides : ∀ f ∈ p, ∀ B, NE B → NE (f.2 B)) :
    ¬ (∀ A B, NE A → NE B → path p A B = join A B) := by
  intro hrep
  cases p with
  | nil =>
    rcases others base with ⟨k, _, hkr, _, _⟩
    have e := hrep (atom base) (atom k) (atom_ne base) (atom_ne k)
    have bad := congrArg (fun V : S α => V k) e
    simp [path, join, atom, hkr] at bad
  | cons f rest =>
    rcases f with ⟨r, g⟩
    rcases others r with ⟨k₀, _, hk₀r, _, _⟩
    have hl := live_of_union ((r, g) :: rest) hrep r k₀ hk₀r
    have hg : g (atom r) ≠ atom r := hl (r, g) (by simp)
    have hgne : NE (g (atom r)) := hsides (r, g) (by simp) (atom r) (atom_ne r)
    rcases exists_outside r (g (atom r)) hgne hg with ⟨k, hk, hkr⟩
    rcases third_outside others r k with ⟨j, hjr, hjk⟩
    have haj : atom j ≠ atom r := fun e => hjr (atom_inj.mp e)
    have hmem : own r (atom j) (g (atom r)) k := by
      simpa [own, haj, hg, join, atom, Ne.symm hjk] using hk
    have hrest : Live rest (atom r) :=
      fun f hf => hl f (List.mem_cons_of_mem _ hf)
    have hout : path ((r, g) :: rest) (atom j) (atom r) k :=
      live_inflates rest (atom r) hrest (own r (atom j) (g (atom r))) k hmem
    rw [hrep _ _ (atom_ne j) (atom_ne r)] at hout
    rcases hout with h | h
    · exact hjk h.symm
    · exact hkr h
theorem common_sub {α : Type} (r : α) (X A B : S α)
    (hA : Sub X A) (hB : Sub X B) : Sub X (own r A B) := by
  classical
  unfold own
  split
  · rename_i h
    rcases h with h | h
    · intro x hx
      exact h ▸ hA x hx
    · intro x hx
      exact h ▸ hB x hx
  · intro x hx
    exact Or.inl (hA x hx)

inductive Unary (α : Type) where
  | input
  | const (A : S α)
  | node (r : α) (left right : Unary α)

noncomputable def eval {α : Type} (u : Unary α) (A : S α) : S α :=
  match u with
  | .input => A
  | .const C => C
  | .node r left right => own r (eval left A) (eval right A)

def Constant {α : Type} (f : S α → S α) : Prop := ∃ C, ∀ A, f A = C
def Extensive {α : Type} (f : S α → S α) : Prop := ∀ A, Sub A (f A)

theorem unary_constant_or_extensive {α : Type} (u : Unary α) :
    Constant (eval u) ∨ Extensive (eval u) := by
  classical
  induction u with
  | input => exact Or.inr (fun _ _ h => h)
  | const C => exact Or.inl ⟨C, fun _ => rfl⟩
  | node r left right ihl ihr =>
    rcases ihl with ⟨C, hC⟩ | hl
    · rcases ihr with ⟨D, hD⟩ | hr
      · left
        exact ⟨own r C D, fun A => by simp only [eval, hC A, hD A]⟩
      · by_cases hc : C = atom r
        · left
          exact ⟨atom r, fun A => by simp [eval, hC A, hc, own]⟩
        · right
          intro A x hx
          have he : own r (eval left A) (eval right A) =
              own r (eval right A) C := by rw [hC A, own_comm]
          change own r (eval left A) (eval right A) x
          rw [he]
          exact own_left_sub r (eval right A) C hc x (hr A x hx)
    · rcases ihr with ⟨D, hD⟩ | hr
      · by_cases hd : D = atom r
        · left
          exact ⟨atom r, fun A => by simp [eval, hD A, hd, own]⟩
        · right
          intro A x hx
          change own r (eval left A) (eval right A) x
          rw [hD A]
          exact own_left_sub r (eval left A) D hd x (hl A x hx)
      · right
        intro A
        exact common_sub r A (eval left A) (eval right A) (hl A) (hr A)

def Multiple {α : Type} (A : S α) : Prop := ∃ u v, u ≠ v ∧ A u ∧ A v

theorem multiple_not_sub_atom {α : Type} (A : S α) (hA : Multiple A)
    (r : α) : ¬ Sub A (atom r) := by
  intro h
  rcases hA with ⟨u, v, huv, hu, hv⟩
  exact huv ((h u hu).trans (h v hv).symm)

theorem ambiguity_unobservable_by_unique_winner {α : Type}
    (u : Unary α) (A B : S α) (hA : Multiple A) (hB : Multiple B) (r : α) :
    eval u A = atom r ↔ eval u B = atom r := by
  rcases unary_constant_or_extensive u with ⟨C, hC⟩ | he
  · rw [hC A, hC B]
  · have hnA : eval u A ≠ atom r := by
      intro h
      exact multiple_not_sub_atom A hA r (h ▸ he A)
    have hnB : eval u B ≠ atom r := by
      intro h
      exact multiple_not_sub_atom B hB r (h ▸ he B)
    exact ⟨fun h => False.elim (hnA h), fun h => False.elim (hnB h)⟩

/-- The upper half of the unary normal-form classification. The finite
    parameter count and synthesis of every row are proved in the paper (main.tex). -/
def Regular {α : Type} (f : S α → S α) : Prop :=
  ∃ C, Extensive f ∧
    (∀ A, Multiple A → f A = join A C) ∧
    (∀ i, Sub (f (atom i)) (join (atom i) C))

theorem own_sub_join {α : Type} (r : α) (A B : S α) :
    Sub (own r A B) (join A B) := by
  classical
  unfold own
  split
  · rename_i h
    rcases h with h | h
    · intro x hx
      exact Or.inl (h.symm ▸ hx)
    · intro x hx
      exact Or.inr (h.symm ▸ hx)
  · exact fun _ hx => hx

theorem extensive_not_atom {α : Type} (f : S α → S α)
    (hf : Extensive f) (A : S α) (hA : Multiple A) (r : α) :
    f A ≠ atom r := by
  intro he
  exact multiple_not_sub_atom A hA r (he ▸ hf A)

theorem regular_const_node {α : Type} (r : α) (C : S α)
    (f : S α → S α) (hf : Regular f) :
    Constant (fun A => own r (f A) C) ∨ Regular (fun A => own r (f A) C) := by
  classical
  by_cases hc : C = atom r
  · left
    exact ⟨atom r, fun A => by simp [own, hc]⟩
  · right
    rcases hf with ⟨D, he, hm, hs⟩
    refine ⟨join D C, ?_, ?_, ?_⟩
    · intro A x hx
      exact own_left_sub r (f A) C hc x (he A x hx)
    · intro A hA
      have hn := extensive_not_atom f he A hA r
      have hnot : ¬ (f A = atom r ∨ C = atom r) := fun h => h.elim hn hc
      have ho : own r (f A) C = join (f A) C := by
        simp only [own, ite_eq_right hnot]
      change own r (f A) C = join A (join D C)
      rw [ho, hm A hA]
      funext x
      apply propext
      simp only [join, or_assoc]
    · intro i x hx
      have h := own_sub_join r (f (atom i)) C x hx
      rcases h with h | h
      · rcases hs i x h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem regular_node {α : Type} (r : α) (f g : S α → S α)
    (hf : Regular f) (hg : Regular g) : Regular (fun A => own r (f A) (g A)) := by
  rcases hf with ⟨C, he, hm, hs⟩
  rcases hg with ⟨D, ke, km, ks⟩
  refine ⟨join C D, ?_, ?_, ?_⟩
  · intro A
    exact common_sub r A (f A) (g A) (he A) (ke A)
  · intro A hA
    have hn := extensive_not_atom f he A hA r
    have kn := extensive_not_atom g ke A hA r
    have hnot : ¬ (f A = atom r ∨ g A = atom r) := fun h => h.elim hn kn
    simp only [own, ite_eq_right hnot, hm A hA, km A hA]
    funext x
    apply propext
    simp only [join]
    constructor <;> intro h <;> grind
  · intro i x hx
    rcases own_sub_join r (f (atom i)) (g (atom i)) x hx with h | h
    · rcases hs i x h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases ks i x h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem unary_normal_form_upper {α : Type} (u : Unary α) :
    Constant (eval u) ∨ Regular (eval u) := by
  induction u with
  | input =>
    right
    refine ⟨(fun _ => False), (fun _ _ h => h), ?_, ?_⟩
    · intro A _
      funext x
      apply propext
      simp [eval, join]
    · intro i x hx
      exact Or.inl hx
  | const C => exact Or.inl ⟨C, fun _ => rfl⟩
  | node r left right ihl ihr =>
    rcases ihl with ⟨C, hC⟩ | hl
    · rcases ihr with ⟨D, hD⟩ | hr
      · exact Or.inl ⟨own r C D, fun A => by simp only [eval, hC A, hD A]⟩
      · have hh : eval (.node r left right) =
            (fun A => own r (eval right A) C) := by
          funext A
          simp only [eval, hC A, own_comm]
        rw [hh]
        exact regular_const_node r C (eval right) hr
    · rcases ihr with ⟨D, hD⟩ | hr
      · have hh : eval (.node r left right) =
            (fun A => own r (eval left A) D) := by
          funext A
          simp only [eval, hD A]
        rw [hh]
        exact regular_const_node r D (eval left) hl
      · exact Or.inr (regular_node r (eval left) (eval right) hl hr)

/-! Full public trees and whole-player unilateral deviations. -/

inductive Tree (α : Type) where
  | leaf (winner : α)
  | node (owner : α) (left right : Tree α)

inductive Profile {α : Type} : Tree α → Type where
  | leaf (w : α) : Profile (.leaf w)
  | node {left right : Tree α} (r : α) (action : Bool)
      (p : Profile left) (q : Profile right) : Profile (.node r left right)

def winner {α : Type} {g : Tree α} (p : Profile g) : α :=
  match p with
  | .leaf w => w
  | .node _ action left right => if action then winner right else winner left

inductive Change {α : Type} (i : α) :
    {g : Tree α} → Profile g → Profile g → Prop where
  | leaf (w : α) : Change i (.leaf w) (.leaf w)
  | node {left right : Tree α} {r : α} {a b : Bool}
      {p p' : Profile left} {q q' : Profile right}
      (root : r ≠ i → a = b) (l : Change i p p') (h : Change i q q') :
      Change i (.node r a p q) (.node r b p' q')

theorem change_refl {α : Type} {g : Tree α} (i : α) (p : Profile g) :
    Change i p p := by
  induction p with
  | leaf w => exact Change.leaf w
  | node r action left right ihl ihr =>
    exact Change.node (fun _ => rfl) ihl ihr

def Nash {α : Type} {g : Tree α} (p : Profile g) : Prop :=
  ∀ i, ∀ q : Profile g, Change i p q → winner q = i → winner p = i

def SPE {α : Type} {g : Tree α} (p : Profile g) : Prop :=
  match p with
  | .leaf _ => True
  | .node r action left right =>
      Nash (.node r action left right) ∧ SPE left ∧ SPE right

theorem spe_nash {α : Type} {g : Tree α} {p : Profile g} (hp : SPE p) :
    Nash p := by
  cases p with
  | leaf w =>
    intro i q _ hq
    cases q
    exact hq
  | node r action left right => exact hp.1

def LocallyOptimal {α : Type} {left right : Tree α} (r : α) (a : Bool)
    (p : Profile left) (q : Profile right) : Prop :=
  (winner p = r ∨ winner q = r) → winner (.node r a p q) = r

theorem spe_node_iff {α : Type} {left right : Tree α} (r : α) (a : Bool)
    (p : Profile left) (q : Profile right) :
    SPE (.node r a p q) ↔ SPE p ∧ SPE q ∧ LocallyOptimal r a p q := by
  classical
  constructor
  · rintro ⟨hn, hp, hq⟩
    refine ⟨hp, hq, ?_⟩
    intro h
    rcases h with h | h
    · apply hn r (.node r false p q)
      · exact Change.node (fun hne => False.elim (hne rfl))
          (change_refl r p) (change_refl r q)
      · exact h
    · apply hn r (.node r true p q)
      · exact Change.node (fun hne => False.elim (hne rfl))
          (change_refl r p) (change_refl r q)
      · exact h
  · rintro ⟨hp, hq, hl⟩
    refine ⟨?_, hp, hq⟩
    intro i deviation hc hw
    cases deviation with
    | node _ b p' q' =>
      cases hc with
      | node hroot hleft hright =>
        by_cases he : r = i
        · cases he
          cases b with
          | false =>
            have h : winner p = r := spe_nash hp r p' hleft hw
            exact hl (Or.inl h)
          | true =>
            have h : winner q = r := spe_nash hq r q' hright hw
            exact hl (Or.inr h)
        · have hab : a = b := hroot he
          subst b
          cases a with
          | false => exact spe_nash hp i p' hleft hw
          | true => exact spe_nash hq i q' hright hw

theorem exists_spe {α : Type} (g : Tree α) : ∃ p : Profile g, SPE p := by
  classical
  induction g with
  | leaf w => exact ⟨.leaf w, True.intro⟩
  | node r left right ihl ihr =>
    rcases ihl with ⟨p, hp⟩
    rcases ihr with ⟨q, hq⟩
    by_cases h : winner p = r
    · refine ⟨.node r false p q, (spe_node_iff r false p q).mpr ⟨hp, hq, ?_⟩⟩
      intro _
      exact h
    · refine ⟨.node r true p q, (spe_node_iff r true p q).mpr ⟨hp, hq, ?_⟩⟩
      rintro (h' | h')
      · exact False.elim (h h')
      · exact h'

def winners {α : Type} (g : Tree α) : S α :=
  fun i => ∃ p : Profile g, SPE p ∧ winner p = i

theorem winners_ne {α : Type} (g : Tree α) : NE (winners g) := by
  rcases exists_spe g with ⟨p, hp⟩
  exact ⟨winner p, p, hp, rfl⟩

theorem winners_leaf {α : Type} (r : α) : winners (.leaf r) = atom r := by
  funext i
  apply propext
  constructor
  · rintro ⟨p, _, h⟩
    cases p
    exact h.symm
  · intro h
    exact ⟨.leaf r, True.intro, h.symm⟩

theorem winner_of_singleton {α : Type} {g : Tree α} (r : α)
    (he : winners g = atom r) (p : Profile g) (hp : SPE p) : winner p = r := by
  have hm : winners g (winner p) := ⟨p, hp, rfl⟩
  rw [he] at hm
  exact hm

theorem exists_spe_losing {α : Type} (g : Tree α) (r : α)
    (he : winners g ≠ atom r) : ∃ p : Profile g, SPE p ∧ winner p ≠ r := by
  rcases exists_outside r (winners g) (winners_ne g) he with ⟨i, hi, hir⟩
  rcases hi with ⟨p, hp, hw⟩
  exact ⟨p, hp, fun h => hir (hw.symm.trans h)⟩

theorem winners_node {α : Type} (r : α) (left right : Tree α) :
    winners (.node r left right) = own r (winners left) (winners right) := by
  classical
  by_cases h : winners left = atom r ∨ winners right = atom r
  · rw [show own r (winners left) (winners right) = atom r from by simp [own, h]]
    funext i
    apply propext
    constructor
    · rintro ⟨profile, hp, hw⟩
      cases profile with
      | node _ action p q =>
        rcases (spe_node_iff r action p q).mp hp with ⟨hl, hr, ho⟩
        have hwin : winner (.node r action p q) = r := by
          rcases h with h | h
          · exact ho (Or.inl (winner_of_singleton r h p hl))
          · exact ho (Or.inr (winner_of_singleton r h q hr))
        exact hw.symm.trans hwin
    · intro hir
      change i = r at hir
      subst i
      rcases exists_spe left with ⟨p, hp⟩
      rcases exists_spe right with ⟨q, hq⟩
      rcases h with h | h
      · have hw := winner_of_singleton r h p hp
        refine ⟨.node r false p q, ?_, hw⟩
        exact (spe_node_iff r false p q).mpr ⟨hp, hq, fun _ => hw⟩
      · have hw := winner_of_singleton r h q hq
        refine ⟨.node r true p q, ?_, hw⟩
        exact (spe_node_iff r true p q).mpr ⟨hp, hq, fun _ => hw⟩
  · rw [show own r (winners left) (winners right) =
        join (winners left) (winners right) from by simp [own, h]]
    have hl : winners left ≠ atom r := fun e => h (Or.inl e)
    have hr : winners right ≠ atom r := fun e => h (Or.inr e)
    funext i
    apply propext
    constructor
    · rintro ⟨profile, hp, hw⟩
      cases profile with
      | node _ action p q =>
        rcases (spe_node_iff r action p q).mp hp with ⟨hP, hQ, _⟩
        cases action with
        | false => exact Or.inl ⟨p, hP, hw⟩
        | true => exact Or.inr ⟨q, hQ, hw⟩
    · rintro (hi | hi)
      · rcases hi with ⟨p, hp, hw⟩
        rcases exists_spe_losing right r hr with ⟨q, hq, hlose⟩
        refine ⟨.node r false p q, ?_, hw⟩
        apply (spe_node_iff r false p q).mpr
        refine ⟨hp, hq, ?_⟩
        rintro (hwin | hwin)
        · exact hwin
        · exact False.elim (hlose hwin)
      · rcases hi with ⟨q, hq, hw⟩
        rcases exists_spe_losing left r hl with ⟨p, hp, hlose⟩
        refine ⟨.node r true p q, ?_, hw⟩
        apply (spe_node_iff r true p q).mpr
        refine ⟨hp, hq, ?_⟩
        rintro (hwin | hwin)
        · exact False.elim (hlose hwin)
        · exact hwin

def neutralTree {α : Type} (r s t : α) (G H : Tree α) : Tree α :=
  .node t (.node r G H) (.node s G H)

theorem neutralTree_winners {α : Type} (r s t : α)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (G H : Tree α) :
    winners (neutralTree r s t G H) = join (winners G) (winners H) := by
  simp only [neutralTree, winners_node]
  exact three_owner_join r s t hrs hrt hst (winners G) (winners H)

/-- Reuse the same full component profiles in both syntactic copies.
    SPE still permits unrestricted ordinary whole-player deviations. -/
def uniformProfile {α : Type} {G H : Tree α} (r s t : α)
    (a b c : Bool) (p : Profile G) (q : Profile H) :
    Profile (neutralTree r s t G H) :=
  .node t a (.node r b p q) (.node s c p q)

theorem uniformProfile_spe {α : Type} {G H : Tree α} (r s t : α)
    (a b c : Bool) (p : Profile G) (q : Profile H) :
    SPE (uniformProfile r s t a b c p q) ↔
      SPE p ∧ SPE q ∧ SPE (uniformProfile r s t a b c
        (.leaf (winner p)) (.leaf (winner q))) := by
  have hleft : SPE (Profile.leaf (winner p)) := True.intro
  have hright : SPE (Profile.leaf (winner q)) := True.intro
  unfold uniformProfile
  unfold neutralTree at *
  rw [spe_node_iff, spe_node_iff, spe_node_iff,
    spe_node_iff, spe_node_iff, spe_node_iff]
  simp only [LocallyOptimal, winner]
  constructor <;> intro h <;> grind

theorem uniformProfile_winner {α : Type} {G H : Tree α} (r s t : α)
    (a b c : Bool) (p : Profile G) (q : Profile H) :
    winner (uniformProfile r s t a b c p q) =
      winner (uniformProfile r s t a b c (.leaf (winner p)) (.leaf (winner q))) := by
  simp only [uniformProfile, winner]

/-- For each fixed pair of component SPE profiles, uniform copies achieve
    exactly their two winners. No information-set constraint is introduced. -/
theorem uniform_copies_winners {α : Type} {G H : Tree α} (r s t : α)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (p : Profile G) (q : Profile H) (hp : SPE p) (hq : SPE q) (i : α) :
    (∃ a b c, SPE (uniformProfile r s t a b c p q) ∧
      winner (uniformProfile r s t a b c p q) = i) ↔
      i = winner p ∨ i = winner q := by
  have he := neutralTree_winners r s t hrs hrt hst
    (.leaf (winner p)) (.leaf (winner q))
  rw [winners_leaf, winners_leaf] at he
  have hi : winners (neutralTree r s t (.leaf (winner p)) (.leaf (winner q))) i ↔
      i = winner p ∨ i = winner q := by
    rw [he]
    rfl
  constructor
  · rintro ⟨a, b, c, hs, hw⟩
    apply hi.mp
    refine ⟨uniformProfile r s t a b c (.leaf (winner p)) (.leaf (winner q)),
      ((uniformProfile_spe r s t a b c p q).mp hs).2.2, ?_⟩
    exact (uniformProfile_winner r s t a b c p q).symm.trans hw
  · intro hw
    rcases hi.mpr hw with ⟨profile, hs, hwin⟩
    cases profile with
    | node _ a left right =>
      cases left with
      | node _ b first second =>
        cases first
        cases second
        cases right with
        | node _ c first second =>
          cases first
          cases second
          refine ⟨a, b, c, ?_, ?_⟩
          · exact (uniformProfile_spe r s t a b c p q).mpr ⟨hp, hq, hs⟩
          · exact (uniformProfile_winner r s t a b c p q).trans hwin

#print axioms winners_node
#print axioms neutralTree_winners
#print axioms uniform_copies_winners
#print axioms three_owner_join
#print axioms no_single_use_union
#print axioms ambiguity_unobservable_by_unique_winner
#print axioms unary_normal_form_upper
end MinimalChoice
