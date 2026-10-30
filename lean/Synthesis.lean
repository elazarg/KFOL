/-
Constructive syntax witnesses for every unary normal form. Only singleton
leaves and owned choices occur in the terms; arbitrary set constants are
not added as constructors. The development uses a finite list covering all
roles, so no Mathlib finiteness infrastructure is required.
-/
import Perspectives

set_option autoImplicit false
namespace MinimalChoice

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Three (α : Type) where
  r : α
  s : α
  t : α
  rs : r ≠ s
  rt : r ≠ t
  st : s ≠ t

def joinTerm {α β : Type} (h : Three α) (left right : Term α β) : Term α β :=
  .node h.t (.node h.r left right) (.node h.s left right)

theorem denote_joinTerm {α β : Type} (h : Three α) (left right : Term α β)
    (v : β → S α) : denote (joinTerm h left right) v =
      join (denote left v) (denote right v) := by
  simp only [joinTerm, denote]
  exact three_owner_join h.r h.s h.t h.rs h.rt h.st _ _

noncomputable def collect {α β : Type} (h : Three α) (roles : List α)
    (enabled : α → Prop) (piece : α → Term α β) (base : Term α β) : Term α β := by
  classical
  exact match roles with
  | [] => base
  | i :: rest => if enabled i then joinTerm h (piece i) (collect h rest enabled piece base)
      else collect h rest enabled piece base

theorem denote_collect {α β : Type} (h : Three α) (roles : List α)
    (enabled : α → Prop) (piece : α → Term α β) (base : Term α β)
    (v : β → S α) (w : α) :
    denote (collect h roles enabled piece base) v w ↔
      denote base v w ∨ ∃ i ∈ roles, enabled i ∧ denote (piece i) v w := by
  classical
  induction roles with
  | nil => simp [collect]
  | cons i rest ih =>
    by_cases hi : enabled i
    · simp only [collect, ite_eq_left hi, denote_joinTerm, join, ih]
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

theorem ground_realization {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (C : S α) (hC : NE C) :
    ∃ p : Term α Unit, ∀ v, denote p v = C := by
  rcases hC with ⟨base, hb⟩
  refine ⟨collect h roles C (fun i => .win i) (.win base), ?_⟩
  intro v
  funext w
  apply propext
  rw [denote_collect]
  constructor
  · rintro (hw | ⟨i, _, hi, hw⟩)
    · change w = base at hw
      subst w
      exact hb
    · change w = i at hw
      subst w
      exact hi
  · intro hw
    exact Or.inr ⟨w, covers w, hw, rfl⟩

theorem own_extend_multiple {α : Type} (r : α) (A C : S α) (hA : Multiple A) :
    own r (join A C) A = join A C := by
  classical
  have ha : A ≠ atom r := by
    intro he
    apply multiple_not_sub_atom A hA r
    intro x hx
    rw [he] at hx
    exact hx
  have hac : join A C ≠ atom r := by
    intro he
    apply multiple_not_sub_atom A hA r
    intro x hx
    have hm : join A C x := Or.inl hx
    rw [he] at hm
    exact hm
  have hn : ¬ (join A C = atom r ∨ A = atom r) := fun e => e.elim hac ha
  simp only [own, ite_eq_right hn]
  funext x
  apply propext
  simp only [join]
  constructor
  · rintro ((ha | hc) | ha)
    · exact Or.inl ha
    · exact Or.inr hc
    · exact Or.inl ha
  · exact Or.inl

noncomputable def gate {α : Type} (h : Three α) (roles : List α)
    (k : α) (allow : α → Prop) : Term α Unit := by
  classical
  exact match roles with
  | [] => joinTerm h (.var ()) (.win k)
  | i :: rest => if i ≠ k ∧ ¬ allow i then
      .node i (gate h rest k allow) (.var ()) else gate h rest k allow

theorem gate_multiple {α : Type} (h : Three α) (roles : List α)
    (k : α) (allow : α → Prop) (A : S α) (hA : Multiple A) :
    denote (gate h roles k allow) (fun _ => A) = join A (atom k) := by
  classical
  induction roles with
  | nil => exact denote_joinTerm h (.var ()) (.win k) (fun _ => A)
  | cons i rest ih =>
    by_cases hi : i ≠ k ∧ ¬ allow i
    · simp only [gate, ite_eq_left hi, denote, ih]
      exact own_extend_multiple i A (atom k) hA
    · simpa only [gate, ite_eq_right hi] using ih

theorem gate_atom {α : Type} (h : Three α) (roles : List α)
    (k : α) (allow : α → Prop) (j : α) :
    denote (gate h roles k allow) (fun _ => atom j) =
      if j = k ∨ allow j ∨ j ∉ roles then join (atom j) (atom k) else atom j := by
  classical
  induction roles with
  | nil => simp [gate, denote_joinTerm, denote]
  | cons i rest ih =>
    by_cases hi : i ≠ k ∧ ¬ allow i
    · by_cases hj : j = i
      · subst j
        simp [gate, hi, denote, own]
      · have hm : denote (gate h rest k allow) (fun _ => atom j) j := by
          rw [ih]
          split
          · exact Or.inl rfl
          · exact rfl
        have he : own i (denote (gate h rest k allow) (fun _ => atom j)) (atom j) =
            denote (gate h rest k allow) (fun _ => atom j) := by
          rw [own_comm]
          exact own_atom_join j i hj _ hm
        simp only [gate, ite_eq_left hi, denote]
        rw [he, ih]
        simp [List.mem_cons, hj]
    · simp only [gate, ite_eq_right hi, ih]
      by_cases hj : j = i
      · subst j
        have he : i = k ∨ allow i := by
          by_cases hik : i = k
          · exact Or.inl hik
          · exact Or.inr (Classical.byContradiction (fun hn => hi ⟨hik, hn⟩))
        rcases he with he | he
        · simp [he]
        · simp [he]
      · simp [List.mem_cons, hj]

theorem gate_atom_full {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (k : α) (allow : α → Prop) (j : α) :
    denote (gate h roles k allow) (fun _ => atom j) =
      if j = k ∨ allow j then join (atom j) (atom k) else atom j := by
  rw [gate_atom]
  simp only [covers j, not_true_eq_false, or_false]

noncomputable def synthesize {α : Type} (h : Three α) (roles : List α)
    (C : S α) (E : α → S α) : Term α Unit :=
  collect h roles C (fun k => gate h roles k (fun i => E i k)) (.var ())

theorem synthesis_multiple {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (C : S α) (E : α → S α)
    (A : S α) (hA : Multiple A) :
    denote (synthesize h roles C E) (fun _ => A) = join A C := by
  funext w
  apply propext
  unfold synthesize
  rw [denote_collect]
  constructor
  · rintro (hw | ⟨i, _, hi, hw⟩)
    · exact Or.inl hw
    · rw [gate_multiple h roles i _ A hA] at hw
      rcases hw with hw | hw
      · exact Or.inl hw
      · change w = i at hw
        subst w
        exact Or.inr hi
  · rintro (hw | hw)
    · exact Or.inl hw
    · refine Or.inr ⟨w, covers w, hw, ?_⟩
      rw [gate_multiple h roles w _ A hA]
      exact Or.inr rfl

theorem synthesis_atom {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (C : S α) (E : α → S α)
    (hE : ∀ i w, E i w → C w) (j : α) :
    denote (synthesize h roles C E) (fun _ => atom j) = join (atom j) (E j) := by
  funext w
  apply propext
  unfold synthesize
  rw [denote_collect]
  constructor
  · rintro (hw | ⟨i, _, hi, hw⟩)
    · exact Or.inl hw
    · rw [gate_atom_full h roles covers i (fun j => E j i) j] at hw
      by_cases he : j = i ∨ E j i
      · rw [ite_eq_left he] at hw
        rcases hw with hw | hw
        · exact Or.inl hw
        · change w = i at hw
          subst w
          rcases he with he | he
          · exact Or.inl he.symm
          · exact Or.inr he
      · rw [ite_eq_right he] at hw
        exact Or.inl hw
  · rintro (hw | hw)
    · exact Or.inl hw
    · refine Or.inr ⟨w, covers w, hE j w hw, ?_⟩
      rw [gate_atom_full h roles covers w (fun j => E j w) j,
        ite_eq_left (Or.inr hw)]
      exact Or.inr rfl

/-- Full generic synthesis. Rows may contain their own role; the union
    already supplies it. Thus only the containment E_i subset C is needed. -/
theorem unary_synthesis {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (C : S α) (E : α → S α)
    (hE : ∀ i w, E i w → C w) :
    ∃ p : Term α Unit,
      (∀ i, denote p (fun _ => atom i) = join (atom i) (E i)) ∧
      (∀ A, Multiple A → denote p (fun _ => A) = join A C) := by
  exact ⟨synthesize h roles C E, synthesis_atom h roles covers C E hE,
    synthesis_multiple h roles covers C E⟩

/-- Every nonempty set is either a singleton or genuinely ambiguous. -/
theorem atom_or_multiple {α : Type} (A : S α) (hA : NE A) :
    (∃ i, A = atom i) ∨ Multiple A := by
  classical
  by_cases h : ∃ i, A = atom i
  · exact Or.inl h
  · rcases hA with ⟨i, hi⟩
    have hn : A ≠ atom i := fun he => h ⟨i, he⟩
    rcases exists_outside i A ⟨i, hi⟩ hn with ⟨j, hj, hji⟩
    exact Or.inr ⟨i, j, Ne.symm hji, hi, hj⟩

/-- In particular, the unary lower-bound witness adding k only on
    ambiguous inputs is a term of the original singleton-leaf language. -/
theorem ambiguity_adder {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (k : α) :
    ∃ p : Term α Unit,
      (∀ i, denote p (fun _ => atom i) = atom i) ∧
      (∀ A, Multiple A → denote p (fun _ => A) = join A (atom k)) := by
  rcases unary_synthesis h roles covers (atom k) (fun _ _ => False)
    (fun _ _ h => False.elim h) with ⟨p, hp, hm⟩
  refine ⟨p, ?_, hm⟩
  intro i
  rw [hp i]
  funext w
  apply propext
  simp only [join, or_false]

theorem join_top {α : Type} (A : S α) : join A (fun _ => True) = (fun _ => True) := by
  funext w
  apply propext
  simp only [join, or_true]

theorem singleton_separator {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (i k : α) (hki : k ≠ i) :
    ∃ p : Term α Unit,
      (∀ A, NE A → A ≠ atom i → denote p (fun _ => A) = (fun _ => True)) ∧
      ¬ denote p (fun _ => atom i) k := by
  let E : α → S α := fun j w => if j = i then w ≠ k else True
  rcases unary_synthesis h roles covers (fun _ => True) E
    (fun _ _ _ => True.intro) with ⟨p, hp, hm⟩
  refine ⟨p, ?_, ?_⟩
  · intro A hA hAi
    rcases atom_or_multiple A hA with ⟨j, hj⟩ | hA
    · have hji : j ≠ i := by
        intro he
        exact hAi (hj.trans (congrArg atom he))
      rw [hj, hp j]
      have he : E j = (fun _ => True) := by simp [E, hji]
      rw [he]
      exact join_top (atom j)
    · rw [hm A hA]
      exact join_top A
  · rw [hp i]
    simp [join, atom, E, hki]

theorem three_others {α : Type} (h : Three α) (k : α) :
    ∃ a b, a ≠ k ∧ b ≠ k ∧ a ≠ b := by
  classical
  by_cases hr : h.r = k
  · subst k
    exact ⟨h.s, h.t, Ne.symm h.rs, Ne.symm h.rt, h.st⟩
  · by_cases hs : h.s = k
    · subst k
      exact ⟨h.r, h.t, h.rs, Ne.symm h.st, h.rt⟩
    · exact ⟨h.r, h.s, hr, hs, h.rs⟩

/-- Unary separation is necessary for complete tests at any arity. -/
def UnaryTestsComplete {α : Type} (D : S α → Prop) : Prop :=
  ∀ p q : Term α Unit,
    (∀ A, NE A → D A → denote p (fun _ => A) = denote q (fun _ => A)) →
      ValidEquation p q

/-- The difficult direction of the exact test-domain characterization,
    now derived from explicit terms rather than abstract set functions. -/
theorem test_domain_necessary {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (D : S α → Prop) (hc : UnaryTestsComplete D) :
    (∀ i, D (atom i)) ∧
      (∀ k, ∃ F, D F ∧ NE F ∧ Multiple F ∧ ¬ F k) := by
  classical
  constructor
  · intro i
    apply Classical.byContradiction
    intro hn
    rcases three_others h i with ⟨k, _, hki, _, _⟩
    rcases singleton_separator h roles covers i k hki with ⟨p, hp, hpk⟩
    rcases ground_realization h roles covers (fun _ => True)
      ⟨i, True.intro⟩ with ⟨q, hq⟩
    have he : ValidEquation p q := hc p q (by
      intro A hA hD
      have hAi : A ≠ atom i := by intro he; rw [he] at hD; exact hn hD
      rw [hp A hA hAi, hq])
    have heq := he (fun _ => atom i) (fun _ => atom_ne i)
    have hm : denote p (fun _ => atom i) k := by
      rw [heq, hq]
      exact True.intro
    exact hpk hm
  · intro k
    apply Classical.byContradiction
    intro hn
    rcases ambiguity_adder h roles covers k with ⟨p, hp, hm⟩
    have he : ValidEquation p (.var ()) := hc p (.var ()) (by
      intro A hAn hD
      change denote p (fun _ => A) = A
      rcases atom_or_multiple A hAn with ⟨i, hi⟩ | hA
      · rw [hi]
        exact hp i
      · have hk : A k := Classical.byContradiction (fun hk => hn ⟨A, hD, hAn, hA, hk⟩)
        rw [hm A hA]
        funext w
        apply propext
        constructor
        · rintro (hw | hw)
          · exact hw
          · change w = k at hw
            subst w
            exact hk
        · exact Or.inl)
    rcases three_others h k with ⟨a, b, hak, hbk, hab⟩
    let F := join (atom a) (atom b)
    have hFn : NE F := ⟨a, Or.inl rfl⟩
    have hFm : Multiple F := ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
    have hf := he (fun _ => F) (fun _ => hFn)
    change denote p (fun _ => F) = F at hf
    rw [hm F hFm] at hf
    have hk : join F (atom k) k := Or.inr rfl
    rw [hf] at hk
    rcases hk with hk | hk
    · exact hak hk.symm
    · exact hbk hk.symm

def instantiate {α β : Type} (t : Term α β) (games : β → Tree α) : Tree α :=
  match t with
  | .win i => .leaf i
  | .var j => games j
  | .node r left right => .node r (instantiate left games) (instantiate right games)

/-- Synthesis terms have the existing full-strategy SPE interpretation. -/
theorem winners_instantiate {α β : Type} (t : Term α β) (games : β → Tree α) :
    winners (instantiate t games) = denote t (fun j => winners (games j)) := by
  induction t with
  | win i => exact winners_leaf i
  | var j => rfl
  | node r left right hl hr =>
    simp only [instantiate, denote, winners_node, hl, hr]

theorem every_winner_set_realized {α : Type} (h : Three α) (roles : List α)
    (covers : ∀ i, i ∈ roles) (C : S α) (hC : NE C) :
    ∃ game : Tree α, winners game = C := by
  rcases ground_realization h roles covers C hC with ⟨p, hp⟩
  refine ⟨instantiate p (fun _ => .leaf h.r), ?_⟩
  rw [winners_instantiate, hp]

#print axioms ground_realization
#print axioms gate_multiple
#print axioms gate_atom_full
#print axioms unary_synthesis
#print axioms ambiguity_adder
#print axioms singleton_separator
#print axioms test_domain_necessary
#print axioms winners_instantiate
#print axioms every_winner_set_realized
end MinimalChoice
