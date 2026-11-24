module

public import KFOL.Definitions.QuantifiedRecognition

/-! # Three separated slots in a quantified CNF

The original quantifier order is preserved. Two existential copies of every
variable follow the original prefix, and two binary clause pairs enforce
the equalities. -/

@[expose] public section
namespace KFOL.Bichain.Quantified.ThreeSlot

abbrev Lit := ℕ × Bool
abbrev Clause := List Lit

/-- Slot zero uses the original variable, the next two slots use its copies. -/
def slot (F : Formula) (j : ℕ) : Fin 3 :=
  if j ≤ F.n then 0 else if j ≤ 2 * F.n then 1 else 2

def shift (offset : ℕ) (l : Lit) : Lit := (offset + l.1, l.2)

def distribute (n : ℕ) : Clause → Clause
  | [] => []
  | [a] => [a]
  | a :: b :: rest => a :: shift n b :: rest.map (shift (2*n))

def equalities (i j : ℕ) : List Clause :=
  [[(i,false), (j,true)], [(i,true), (j,false)]]

def links (n : ℕ) : List Clause :=
  (List.range n).flatMap fun k =>
    equalities (k+1) (n+(k+1)) ++ equalities (k+1) (2*n+(k+1))

def translate (F : Formula) : Formula where
  n := 3 * F.n
  ex i := if i ≤ F.n then F.ex i else true
  cls := F.cls.map (distribute F.n) ++ links F.n

def holds (α : ℕ → Bool) (C : Clause) : Prop := ∃ l ∈ C, α l.1 = l.2

private theorem holds_cons (α : ℕ → Bool) (a : Lit) (as : Clause) :
    holds α (a :: as) ↔ α a.1 = a.2 ∨ holds α as := by simp [holds]

private theorem holds_equalities (α : ℕ → Bool) (i j : ℕ) :
    (∀ C ∈ equalities i j, holds α C) ↔ α i = α j := by
  have nil : holds α [] ↔ False := by simp [holds]
  cases hi : α i <;> cases hj : α j <;> simp [equalities, holds_cons, nil, hi, hj]

private theorem holds_links (n : ℕ) (α : ℕ → Bool) :
    (∀ C ∈ links n, holds α C) ↔ ∀ j, 1 ≤ j → j ≤ n →
      α j = α (n+j) ∧ α j = α (2*n+j) := by
  constructor
  · intro all j pos lim
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have mem : k ∈ List.range n := List.mem_range.mpr (by omega)
    refine ⟨(holds_equalities α _ _).mp ?_, (holds_equalities α _ _).mp ?_⟩
    · intro C hc
      exact all C (List.mem_flatMap.mpr ⟨k,mem,List.mem_append_left _ hc⟩)
    · intro C hc
      exact all C (List.mem_flatMap.mpr ⟨k,mem,List.mem_append_right _ hc⟩)
  · intro eq C hc
    obtain ⟨k,hk,cm⟩ := List.mem_flatMap.mp hc
    have lim := List.mem_range.mp hk
    obtain ⟨first, second⟩ := eq (k+1) (by omega) (by omega)
    exact (List.mem_append.mp cm).elim
      ((holds_equalities α _ _).mpr first C) ((holds_equalities α _ _).mpr second C)

private theorem holds_distribute (F : Formula) (α : ℕ → Bool) (C : Clause)
    (wf : ∀ l ∈ C, 1 ≤ l.1 ∧ l.1 ≤ F.n)
    (agree : ∀ j, 1 ≤ j → j ≤ F.n → α j = α (F.n+j) ∧ α j = α (2*F.n+j)) :
    holds α (distribute F.n C) ↔ holds α C := by
  cases C with
  | nil => rfl
  | cons a C =>
    cases C with
    | nil => rfl
    | cons b tail =>
      have wb := wf b (by simp)
      have same : holds α (tail.map (shift (2*F.n))) ↔ holds α tail := by
        constructor
        · rintro ⟨i,mem,hit⟩
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
          have wj := wf j (by simp [hj])
          exact ⟨j,hj,(agree j.1 wj.1 wj.2).2.trans hit⟩
        · rintro ⟨j,hj,hit⟩
          have wj := wf j (by simp [hj])
          exact ⟨shift (2*F.n) j,List.mem_map.mpr ⟨j,hj,rfl⟩,(agree j.1 wj.1 wj.2).2.symm.trans hit⟩
      simp only [distribute, holds_cons, shift, same, ← (agree b.1 wb.1 wb.2).1]

/-- The enlarged matrix holds exactly when the input matrix holds and all
three blocks of variables give agreeing answers. -/
theorem matrix_iff (F : Formula) (wf : F.WF) (α : ℕ → Bool) :
    Matrix (translate F) α ↔ Matrix F α ∧
      ∀ j, 1 ≤ j → j ≤ F.n → α j = α (F.n+j) ∧ α j = α (2*F.n+j) := by
  change (∀ C ∈ F.cls.map (distribute F.n) ++ links F.n, holds α C) ↔ _
  constructor
  · intro h
    have eq := (holds_links F.n α).mp (fun C hc => h C (List.mem_append_right _ hc))
    refine ⟨?_,eq⟩
    intro C hc
    apply (holds_distribute F α C (wf C hc) eq).mp
    exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨C,hc,rfl⟩))
  · rintro ⟨hm,eq⟩ C hc
    rcases List.mem_append.mp hc with C1 | C2
    · obtain ⟨D,hd,rfl⟩ := List.mem_map.mp C1
      exact (holds_distribute F α D (wf D hd) eq).mpr (hm D hd)
    · exact (holds_links F.n α).mpr eq C C2

/-- An existential suffix can choose exactly the assignment on its own stages. -/
theorem sat_exists_tail (F : Formula) (k i : ℕ) (α : ℕ → Bool)
    (ex : ∀ j, i < j → j ≤ i+k → F.ex j = true) :
    sat F k i α ↔ ∃ β, (∀ j, j ≤ i ∨ i+k < j → β j = α j) ∧ Matrix F β := by
  induction k generalizing i α with
  | zero =>
    constructor
    · intro h
      exact ⟨α,fun _ _ => rfl,h⟩
    · rintro ⟨β,agree,h⟩
      have equality : β = α := funext fun j => agree j (by omega)
      exact equality ▸ h
  | succ k ih =>
    have ex1 := ex (i+1) (by omega) (by omega)
    have later : ∀ j, i+1 < j → j ≤ i+1+k → F.ex j = true :=
      fun j lo up => ex j (by omega) (by omega)
    rw [sat, ite_eq_left ex1]
    constructor
    · rintro ⟨v,h⟩
      obtain ⟨β,agree,mat⟩ := (ih (i+1) (Function.update α (i+1) v) later).mp h
      refine ⟨β,?_,mat⟩
      intro j bound
      have unequal : j ≠ i+1 := by omega
      exact (agree j (by omega)).trans (Function.update_of_ne unequal _ _)
    · rintro ⟨β,agree,mat⟩
      refine ⟨β (i+1),(ih (i+1) _ later).mpr ⟨β,?_,mat⟩⟩
      intro j bound
      by_cases eq : j = i+1
      · simp [eq]
      · rw [Function.update_of_ne eq]
        exact agree j (by omega)

private theorem matrix_congr (F : Formula) (wf : F.WF) (α β : ℕ → Bool)
    (agree : ∀ j, 1 ≤ j → j ≤ F.n → α j = β j) : Matrix F α ↔ Matrix F β := by
  have atClause (C : Clause) (hc : C ∈ F.cls) (l : Lit) (hl : l ∈ C) :
      α l.1 = β l.1 := agree _ (wf C hc l hl).1 (wf C hc l hl).2
  constructor
  · intro h C hc
    obtain ⟨l,hl,hit⟩ := h C hc
    exact ⟨l,hl,(atClause C hc l hl).symm.trans hit⟩
  · intro h C hc
    obtain ⟨l,hl,hit⟩ := h C hc
    exact ⟨l,hl,(atClause C hc l hl).trans hit⟩

private theorem after_prefix (F : Formula) (wf : F.WF) (α : ℕ → Bool) :
    sat (translate F) (2*F.n) F.n α ↔ Matrix F α := by
  rw [sat_exists_tail]
  · constructor
    · rintro ⟨β,agree,mat⟩
      exact (matrix_congr F wf β α (fun j _ hj => agree j (Or.inl hj))).mp ((matrix_iff F wf β).mp mat).1
    · intro mat
      let β (j : ℕ) := if F.n < j ∧ j ≤ 2*F.n then α (j-F.n)
        else if 2*F.n < j ∧ j ≤ 3*F.n then α (j-2*F.n) else α j
      have fixed (j : ℕ) (hj : j ≤ F.n ∨ F.n+2*F.n < j) : β j = α j := by
        simp [β, show ¬ (F.n < j ∧ j ≤ 2*F.n) by omega,
          show ¬ (2*F.n < j ∧ j ≤ 3*F.n) by omega]
      refine ⟨β,fixed,(matrix_iff F wf β).mpr ⟨?_,?_⟩⟩
      · exact (matrix_congr F wf β α (fun j _ hj => fixed j (Or.inl hj))).mpr mat
      · intro j pos lim
        have h1 : F.n < F.n+j ∧ F.n+j ≤ 2*F.n := by omega
        have h2 : 2*F.n < 2*F.n+j ∧ 2*F.n+j ≤ 3*F.n := by omega
        have n1 : ¬ (F.n < 2*F.n+j ∧ 2*F.n+j ≤ 2*F.n) := by omega
        rw [fixed j (Or.inl lim)]
        simp [β,h1,h2,n1]
  · intro j lo _
    simp [translate, show ¬ j ≤ F.n by omega]

private theorem prefix_iff (F : Formula) (wf : F.WF) (k i : ℕ) (total : i+k = F.n) (α : ℕ → Bool) :
    sat (translate F) (k+2*F.n) i α ↔ sat F k i α := by
  induction k generalizing i α with
  | zero =>
    have e : i = F.n := by omega
    subst i
    simpa only [Nat.zero_add,sat] using after_prefix F wf α
  | succ k ih =>
    rw [show k+1+2*F.n = (k+2*F.n)+1 by omega, sat, sat]
    have h : (translate F).ex (i+1) = F.ex (i+1) := by
      simp [translate, show i+1 ≤ F.n by omega]
    rw [h]
    cases e : F.ex (i+1) with
    | false => exact forall_congr' (fun s => ih (i+1) (by omega) (Function.update α (i+1) s))
    | true => exact exists_congr (fun s => ih (i+1) (by omega) (Function.update α (i+1) s))

/-- Appending existential copies after all original quantifiers preserves truth,
including for arbitrary initial values assigned outside the prefix. -/
theorem sat_translate_iff (F : Formula) (wf : F.WF) (α : ℕ → Bool) :
    sat (translate F) (translate F).n 0 α ↔ sat F F.n 0 α := by
  have size : (translate F).n = F.n+2*F.n := by change 3*F.n = _; omega
  rw [size]
  exact prefix_iff F wf F.n 0 (by omega) α

private theorem valid_distribute (F : Formula) (C : Clause)
    (valid : ∀ l ∈ C, 1 ≤ l.1 ∧ l.1 ≤ F.n) :
    ∀ l ∈ distribute F.n C, 1 ≤ l.1 ∧ l.1 ≤ 3*F.n := by
  intro l hl
  cases C with
  | nil => simp [distribute] at hl
  | cons a tail =>
    cases tail with
    | nil =>
      have eq : l = a := by simpa [distribute] using hl
      have := valid a (by simp)
      rw [eq]
      omega
    | cons b rest =>
      simp only [distribute, List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | rfl | ⟨k,hk,rfl⟩
      · have := valid l (by simp)
        omega
      · have := valid b (by simp)
        simp only [shift]
        omega
      · have := valid k (by simp [hk])
        simp only [shift]
        omega

private theorem mem_equalities {C : Clause} {i j : ℕ} (hc : C ∈ equalities i j) :
    C = [(i,false),(j,true)] ∨ C = [(i,true),(j,false)] := by simpa [equalities] using hc

/-- The fresh variables all lie within the enlarged quantified prefix. -/
theorem wf_translate (F : Formula) (wf : F.WF) : (translate F).WF := by
  intro C hc l hl
  change C ∈ F.cls.map (distribute F.n) ++ links F.n at hc
  change 1 ≤ l.1 ∧ l.1 ≤ 3*F.n
  rcases List.mem_append.mp hc with common | added
  · obtain ⟨D,hd,rfl⟩ := List.mem_map.mp common
    exact valid_distribute F D (wf _ hd) _ hl
  · obtain ⟨k,hk,mem⟩ := List.mem_flatMap.mp added
    have := List.mem_range.mp hk
    rcases List.mem_append.mp mem with side | side <;> rcases mem_equalities side with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;>
      dsimp <;> omega

private theorem original_slot (F : Formula) (j : ℕ) (lim : j ≤ F.n) : slot F j = 0 := by
  simp [slot,lim]

private theorem first_slot (F : Formula) (j : ℕ) (pos : 1 ≤ j) (lim : j ≤ F.n) :
    slot F (F.n+j) = 1 := by
  simp [slot, show ¬ F.n+j ≤ F.n by omega, show F.n+j ≤ 2*F.n by omega]

private theorem second_slot (F : Formula) (j : ℕ) (pos : 1 ≤ j) :
    slot F (2*F.n+j) = 2 := by
  simp [slot, show ¬ 2*F.n+j ≤ F.n by omega, show ¬ 2*F.n+j ≤ 2*F.n by omega]

private theorem pair_slots (F : Formula) (p q : Lit) (different : slot F p.1 ≠ slot F q.1) :
    ∀ u ∈ [p,q], ∀ v ∈ [p,q], slot F u.1 = slot F v.1 → u = v := by
  intro u hu v hv same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all [Ne.symm different]

private theorem distributed_slots (F : Formula) (C : Clause)
    (valid : ∀ l ∈ C, 1 ≤ l.1 ∧ l.1 ≤ F.n) (short : C.length ≤ 3) :
    ∀ p ∈ distribute F.n C, ∀ q ∈ distribute F.n C,
      slot F p.1 = slot F q.1 → p = q := by
  match C with
  | [] => simp [distribute]
  | [a] => simp [distribute]
  | a::b::tail =>
    have a0 := original_slot F a.1 (valid a (by simp)).2
    have b1 := first_slot F b.1 (valid b (by simp)).1 (valid b (by simp)).2
    cases tail with
    | nil => exact pair_slots F a (shift F.n b) (by simp [shift,a0,b1])
    | cons c rest =>
      have noRest : rest = [] := by
        have size : rest.length = 0 := by simpa using short
        exact List.length_eq_zero_iff.mp size
      subst rest
      have c2 := second_slot F c.1 (valid c (by simp)).1
      intro p hp q hq same
      simp only [distribute, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hp hq
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        simp_all [shift]

/-- Equal slots identify the entire signed literal within each translated
clause, including the clauses linking the copies. -/
theorem clause_slot_unique (F : Formula) (wf : F.WF) (short : ∀ C ∈ F.cls, C.length ≤ 3) :
    ∀ C ∈ (translate F).cls, ∀ p ∈ C, ∀ q ∈ C, slot F p.1 = slot F q.1 → p = q := by
  intro C hc
  rcases List.mem_append.mp hc with common | added
  · obtain ⟨D,hd,rfl⟩ := List.mem_map.mp common
    exact distributed_slots F D (wf D hd) (short D hd)
  · obtain ⟨k,hk,mem⟩ := List.mem_flatMap.mp added
    have bound := List.mem_range.mp hk
    have a := original_slot F (k+1) (by omega)
    have b := first_slot F (k+1) (by omega) (by omega)
    have c := second_slot F (k+1) (by omega)
    rcases List.mem_append.mp mem with side | side <;> rcases mem_equalities side with rfl | rfl <;>
      apply pair_slots <;> simp [a,b,c]

/-- The clause accessor used by the rectangle construction also has the
slot property beyond its list, where it returns the empty clause. -/
theorem getD_slot_unique (F : Formula) (wf : F.WF) (short : ∀ C ∈ F.cls, C.length ≤ 3)
    (k : ℕ) : ∀ p ∈ (translate F).cls.getD k [], ∀ q ∈ (translate F).cls.getD k [],
      slot F p.1 = slot F q.1 → p = q := by
  by_cases h : k < (translate F).cls.length
  · rw [List.getD_eq_getElem _ _ h]
    exact clause_slot_unique F wf short _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp

private theorem links_length (n : ℕ) : (links n).length = 4*n := by
  unfold links
  -- Each member of the range contributes two binary pairs.
  have four (xs : List ℕ) : (xs.flatMap (fun i =>
      equalities (i+1) (n+(i+1)) ++ equalities (i+1) (2*n+(i+1)))).length = 4*xs.length := by
    induction xs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, equalities]
      simp
      omega
  simpa using four (List.range n)

/-- The translation triples the prefix and adds four binary clauses per variable. -/
theorem size (F : Formula) :
    (translate F).n = 3*F.n ∧ (translate F).cls.length = F.cls.length + 4*F.n := by
  simp [translate, links_length]

end KFOL.Bichain.Quantified.ThreeSlot
