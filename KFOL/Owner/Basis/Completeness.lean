module

public import KFOL.Owner.Basis.WordNormalForm
public import KFOL.Owner.Basis.WordAbsorption

/-! Minimal four-state valuations extract first-occurrence word witnesses.
These are proof valuations, not definitions of validity or derivability. -/

@[expose] public section

namespace KFOL.Owner.FiniteBasis

universe v

private noncomputable def testVal {Var : Type v} (j : Var) (A N : Set Var) (i : Var) : Four := by
  classical
  exact if i = j then .winning else if i ∈ A then .ambiguous else if i ∈ N then .other else .owner

private theorem testVal_winning {Var : Type v} (j : Var) (A N : Set Var) (i : Var) :
    testVal j A N i = .winning ↔ i = j := by
  classical
  by_cases hi : i = j <;> by_cases hA : i ∈ A <;> by_cases hN : i ∈ N <;> simp [testVal, hi, hA, hN]

private theorem testVal_ambiguous {Var : Type v} (j : Var) (A N : Set Var) (i : Var) :
    testVal j A N i = .ambiguous ↔ i ≠ j ∧ i ∈ A := by
  classical
  by_cases hi : i = j <;> by_cases hA : i ∈ A <;> by_cases hN : i ∈ N <;> simp [testVal, hi, hA, hN]

private theorem testVal_not_owner {Var : Type v} (j : Var) (A N : Set Var) (hAN : A ⊆ N) (i : Var) :
    testVal j A N i ≠ .owner ↔ i ∈ N ∨ i = j := by
  classical
  by_cases hi : i = j <;> by_cases hA : i ∈ A <;> by_cases hN : i ∈ N <;>
    first | exact False.elim (hN (hAN hA)) | simp [testVal, hi, hA, hN]

private def fourWord {Var : Type v} (r : Four) (v : Var → Four) (W : List (Var × Var)) : Four :=
  (four_laws.word r (W.map (fun p => (v p.1, v p.2))) ⟨r, law_R1 r⟩).val

private theorem fourWord_nil {Var : Type v} (r : Four) (v : Var → Four) : fourWord r v [] = r := rfl
private theorem fourWord_cons {Var : Type v} (r : Four) (v : Var → Four) (a b : Var) (W : List (Var × Var)) :
    fourWord r v ((a, b) :: W) = Four.guarded r (Four.reset (fourWord r v W) (v a)) (v b) := rfl

private theorem four_action_winning (x a b : Four) :
    Four.guarded .ambiguous (Four.reset x a) b = .winning ↔
      a ≠ .owner ∧ b ≠ .owner ∧ (a = .winning ∨ b = .winning ∨ (a = .ambiguous ∧ x = .winning)) := by
  cases x <;> cases a <;> cases b <;> decide

/-- A winning word at a minimal marker valuation has a first source
occurrence whose earlier letters require only the supplied tests. -/
private theorem first_witness_of_winning {Var : Type v} (j : Var) (A N : Set Var) (hAN : A ⊆ N)
    (W : List (Var × Var)) (hw : fourWord .ambiguous (testVal j A N) W = .winning) :
    ∃ Q : List (Var × Var), ∃ t : Var, ∃ rest : List (Var × Var),
      (W = Q ++ (j, t) :: rest ∨ W = Q ++ (t, j) :: rest) ∧
      (∀ p ∈ Q, p.1 ∈ A ∧ p.2 ∈ N) ∧ (t ∈ N ∨ t = j) := by
  classical
  induction W with
  | nil =>
    change Four.ambiguous = Four.winning at hw
    cases hw
  | cons p W ih =>
    obtain ⟨a, b⟩ := p
    rw [fourWord_cons, four_action_winning] at hw
    have haN := (testVal_not_owner j A N hAN a).mp hw.1
    have hbN := (testVal_not_owner j A N hAN b).mp hw.2.1
    by_cases ha : a = j
    · subst a
      exact ⟨[], b, W, Or.inl rfl, by simp, hbN⟩
    · by_cases hb : b = j
      · subst b
        exact ⟨[], a, W, Or.inr rfl, by simp, haN⟩
      · have hrest : testVal j A N a = .ambiguous ∧ fourWord .ambiguous (testVal j A N) W = .winning := by
          rcases hw.2.2 with h | h | h
          · exact False.elim (ha ((testVal_winning j A N a).mp h))
          · exact False.elim (hb ((testVal_winning j A N b).mp h))
          · exact h
        have haA := ((testVal_ambiguous j A N a).mp hrest.1).2
        have hbN' := hbN.resolve_right hb
        obtain ⟨Q, t, rest, hQ, htests, ht⟩ := ih hrest.2
        refine ⟨(a, b) :: Q, t, rest, ?_, ?_, ht⟩
        · rcases hQ with hQ | hQ
          · exact Or.inl (congrArg (List.cons (a, b)) hQ)
          · exact Or.inr (congrArg (List.cons (a, b)) hQ)
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨haA, hbN'⟩
          · exact htests p hp

private theorem prefix_winning {Var : Type v} (j : Var) (A N : Set Var) (hAN : A ⊆ N) (hj : j ∉ A)
    (P W : List (Var × Var)) (hP : ∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ N)
    (hW : fourWord .ambiguous (testVal j A N) W = .winning) :
    fourWord .ambiguous (testVal j A N) (P ++ W) = .winning := by
  induction P with
  | nil => exact hW
  | cons p P ih =>
    obtain ⟨a, b⟩ := p
    rw [List.cons_append, fourWord_cons, four_action_winning]
    have haA := (hP (a, b) (List.mem_cons_self ..)).1
    have hbN := (hP (a, b) (List.mem_cons_self ..)).2
    have ha : a ≠ j := fun he => hj (he ▸ haA)
    refine ⟨(testVal_not_owner j A N hAN a).mpr (Or.inl (hAN haA)),
      (testVal_not_owner j A N hAN b).mpr (Or.inl hbN), Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · exact (testVal_ambiguous j A N a).mpr ⟨ha, haA⟩
    · exact ih (fun p hp => hP p (List.mem_cons_of_mem _ hp))

private theorem reset_winning_fixed (x y : Four) (hy : Four.reset y .ambiguous = y) :
    Four.reset x y = .winning ↔ x = .winning ∨ y = .winning := by
  cases x <;> cases y <;> simp_all [Four.reset]

private theorem wordsValue_winning {Var : Type v} (v : Var → Four) (language : List (List (Var × Var))) :
    (four_laws.wordsValue .ambiguous v language).val = .winning ↔
      ∃ W ∈ language, fourWord .ambiguous v W = .winning := by
  let _ := four_laws.fiberSemilattice .ambiguous
  let _ := four_laws.fiberOrderBot .ambiguous
  induction language with
  | nil => simp only [Laws.wordsValue_nil, List.not_mem_nil, false_and, exists_false]; decide
  | cons W rest ih =>
    rw [Laws.wordsValue_cons]
    change Four.reset (fourWord .ambiguous v W) (four_laws.wordsValue .ambiguous v rest).val = .winning ↔ _
    rw [reset_winning_fixed _ _ (four_laws.wordsValue .ambiguous v rest).property]
    constructor
    · rintro (hW | hrest)
      · exact ⟨W, List.mem_cons_self .., hW⟩
      · obtain ⟨Q, hQ, hwin⟩ := ih.mp hrest
        exact ⟨Q, List.mem_cons_of_mem _ hQ, hwin⟩
    · rintro ⟨Q, hQ, hwin⟩
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact Or.inl hwin
      · exact Or.inr (ih.mpr ⟨Q, hQ, hwin⟩)

private theorem frame_winning {Var : Type v} (j k : Var) (A N : Set Var) (hAN : A ⊆ N)
    (hk : k ∈ N ∨ k = j) (rest : List (Var × Var)) :
    fourWord .ambiguous (testVal j A N) ((j, k) :: rest) = .winning ∧
      fourWord .ambiguous (testVal j A N) ((k, j) :: rest) = .winning := by
  have hjW := (testVal_winning j A N j).mpr rfl
  have hjN := (testVal_not_owner j A N hAN j).mpr (Or.inr rfl)
  have hkN := (testVal_not_owner j A N hAN k).mpr hk
  constructor
  · rw [fourWord_cons, four_action_winning]
    exact ⟨hjN, hkN, Or.inl hjW⟩
  · rw [fourWord_cons, four_action_winning]
    exact ⟨hkN, hjN, Or.inr (Or.inl hjW)⟩

/-- Semantic containment supplies a source-free covering prefix with exactly
the prerequisite inclusions required by generic two-source absorption. -/
private theorem covering_witness {Var : Type v} (r j k : Var) (P rest : List (Var × Var))
    (lower upper : List (List (Var × Var)))
    (hword : P ++ (j, k) :: rest ∈ lower ∨ P ++ (k, j) :: rest ∈ lower)
    (hj : ¬(j = r ∨ (∃ c, (j, c) ∈ P) ∨ ∃ c, (c, j) ∈ P))
    (hsemantic : ∀ v : Var → Four,
      (four_laws.wordsValue .ambiguous v lower).val = .winning →
        (four_laws.wordsValue .ambiguous v upper).val = .winning) :
    ∃ Q : List (Var × Var), ∃ t : Var, ∃ suffix : List (Var × Var),
      (Q ++ (j, t) :: suffix ∈ upper ∨ Q ++ (t, j) :: suffix ∈ upper) ∧
      (∀ p ∈ Q, p.1 = r ∨ ∃ c, (p.1, c) ∈ P) ∧
      (∀ p ∈ Q, (p.2 = r ∨ (∃ c, (p.2, c) ∈ P) ∨ ∃ c, (c, p.2) ∈ P) ∨ p.2 = k) ∧
      ((t = r ∨ (∃ c, (t, c) ∈ P) ∨ ∃ c, (c, t) ∈ P) ∨ t = k ∨ t = j) := by
  classical
  let A : Set Var := {x | x = r ∨ ∃ c, (x, c) ∈ P}
  let N₀ : Set Var := {x | x = r ∨ (∃ c, (x, c) ∈ P) ∨ ∃ c, (c, x) ∈ P}
  let N : Set Var := N₀ ∪ {k}
  have hAN₀ : A ⊆ N₀ := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
  have hAN : A ⊆ N := fun _ hx => Or.inl (hAN₀ hx)
  have hjA : j ∉ A := fun hx => hj (hAN₀ hx)
  have hP : ∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ N := by
    intro p hp
    exact ⟨Or.inr ⟨p.2, hp⟩, Or.inl (Or.inr (Or.inr ⟨p.1, hp⟩))⟩
  have hframes := frame_winning j k A N hAN (Or.inl (Or.inr rfl)) rest
  have hlower : (four_laws.wordsValue .ambiguous (testVal j A N) lower).val = .winning := by
    apply (wordsValue_winning _ lower).mpr
    rcases hword with hword | hword
    · exact ⟨_, hword, prefix_winning j A N hAN hjA P _ hP hframes.1⟩
    · exact ⟨_, hword, prefix_winning j A N hAN hjA P _ hP hframes.2⟩
  obtain ⟨W, hW, hwin⟩ := (wordsValue_winning _ upper).mp (hsemantic _ hlower)
  obtain ⟨Q, t, suffix, hQ, htests, ht⟩ := first_witness_of_winning j A N hAN W hwin
  refine ⟨Q, t, suffix, ?_, ?_, ?_, ?_⟩
  · rcases hQ with hQ | hQ
    · exact Or.inl (hQ ▸ hW)
    · exact Or.inr (hQ ▸ hW)
  · intro p hp
    exact (htests p hp).1
  · intro p hp
    exact (htests p hp).2
  · rcases ht with (ht | ht) | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ht)

end KFOL.Owner.FiniteBasis

namespace KFOL.Owner.FiniteBasis.Laws

universe u v

variable {M : Type u} {f : M → M → M} {h : M → M → M → M} (laws : FiniteBasis.Laws f h)

private theorem wordValue_le_wordsValue {Var : Type v} (r : M) (v : Var → M)
    (W : List (Var × Var)) (language : List (List (Var × Var))) (hW : W ∈ language) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.word r (W.map (fun p => (v p.1, v p.2))) ⊥ ≤ laws.wordsValue r v language := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  induction language with
  | nil => exact False.elim (List.not_mem_nil hW)
  | cons Q language ih =>
    rw [laws.wordsValue_cons]
    rcases List.mem_cons.mp hW with rfl | hW
    · exact le_sup_left
    · exact (ih hW).trans le_sup_right

private theorem witness_le_wordsValue {Var : Type v} (r : M) (v : Var → M)
    (j t : Var) (Q suffix : List (Var × Var)) (upper : List (List (Var × Var)))
    (hQ : Q ++ (j, t) :: suffix ∈ upper ∨ Q ++ (t, j) :: suffix ∈ upper) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.word r (Q.map (fun p => (v p.1, v p.2))) (laws.action r (v j) (v t) ⊥) ≤ laws.wordsValue r v upper := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  have hd (a b : Var) (hmem : Q ++ (a, b) :: suffix ∈ upper) :
      laws.word r (Q.map (fun p => (v p.1, v p.2))) (laws.action r (v a) (v b) ⊥) ≤ laws.wordsValue r v upper := by
    have hfull := laws.wordValue_le_wordsValue r v _ upper hmem
    rw [List.map_append, List.map_cons, laws.word_append, laws.word_cons] at hfull
    have hm := OrderHomClass.monotone (laws.actionHom r (v a) (v b))
    exact (laws.word_mono r _ (hm bot_le)).trans hfull
  rcases hQ with hQ | hQ
  · exact hd j t hQ
  · have he : laws.action r (v j) (v t) ⊥ = laws.action r (v t) (v j) ⊥ := by
      apply Subtype.ext
      rw [laws.action_zero, laws.action_zero]
      exact laws.h_sym r (v j) (v t)
    rw [he]
    exact hd t j hQ

omit laws in
private theorem lift_many {Var : Type v} (v : Var → M) (r x : Var) (P : List (Var × Var))
    (hx : x = r ∨ ∃ c, (x, c) ∈ P) :
    v x = v r ∨ ∃ c, (v x, c) ∈ P.map (fun p => (v p.1, v p.2)) := by
  rcases hx with rfl | ⟨c, hc⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨v c, List.mem_map.mpr ⟨(x, c), hc, rfl⟩⟩

omit laws in
private theorem lift_outside {Var : Type v} (v : Var → M) (r x : Var) (P : List (Var × Var))
    (hx : x = r ∨ (∃ c, (x, c) ∈ P) ∨ ∃ c, (c, x) ∈ P) :
    v x = v r ∨ (∃ c, (v x, c) ∈ P.map (fun p => (v p.1, v p.2))) ∨
      ∃ c, (c, v x) ∈ P.map (fun p => (v p.1, v p.2)) := by
  rcases hx with rfl | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨v c, List.mem_map.mpr ⟨(x, c), hc, rfl⟩⟩)
  · exact Or.inr (Or.inr ⟨v c, List.mem_map.mpr ⟨(c, x), hc, rfl⟩⟩)

/-- Semantic containment in the concrete four-state algebra entails the
corresponding inequality in every model of the displayed forty equations. -/
theorem wordsValue_le_of_four {Var : Type v} (r : Var) (lower upper : List (List (Var × Var)))
    (hsemantic : ∀ w : Var → Four,
      (four_laws.wordsValue .ambiguous w lower).val = .winning →
        (four_laws.wordsValue .ambiguous w upper).val = .winning) (v : Var → M) :
    letI := laws.fiberSemilattice (v r)
    laws.wordsValue (v r) v lower ≤ laws.wordsValue (v r) v upper := by
  classical
  let _ := laws.fiberSemilattice (v r)
  let _ := laws.fiberOrderBot (v r)
  have hprefix (P : List (Var × Var)) : ∀ rest : List (Var × Var), P ++ rest ∈ lower →
      laws.word (v r) (P.map (fun p => (v p.1, v p.2))) ⊥ ≤ laws.wordsValue (v r) v upper := by
    induction P using List.reverseRecOn with
    | nil => intro _ _; exact bot_le
    | append_singleton P p ih =>
      obtain ⟨a, b⟩ := p
      intro rest hword
      have hword' : P ++ (a, b) :: rest ∈ lower := by simpa only [List.append_assoc, List.singleton_append] using hword
      have hzero := ih ((a, b) :: rest) hword'
      simp only [List.map_append, List.map_cons, List.map_nil, laws.word_append, laws.word_cons, laws.word_nil]
      apply laws.two_source_absorption (v r) (v a) (v b) _ _ hzero
      have hsources (j k : Var) (hjk : P ++ (j, k) :: rest ∈ lower ∨ P ++ (k, j) :: rest ∈ lower) :
          (v j = v r ∨ (∃ c, (v j, c) ∈ P.map (fun p => (v p.1, v p.2))) ∨
            ∃ c, (c, v j) ∈ P.map (fun p => (v p.1, v p.2))) ∨
            ∃ Q : List (M × M), ∃ t : M,
              (∀ p ∈ Q, p.1 = v r ∨ ∃ c, (p.1, c) ∈ P.map (fun p => (v p.1, v p.2))) ∧
              (∀ p ∈ Q, (p.2 = v r ∨ (∃ c, (p.2, c) ∈ P.map (fun p => (v p.1, v p.2))) ∨
                ∃ c, (c, p.2) ∈ P.map (fun p => (v p.1, v p.2))) ∨ p.2 = v k) ∧
              ((t = v r ∨ (∃ c, (t, c) ∈ P.map (fun p => (v p.1, v p.2))) ∨
                ∃ c, (c, t) ∈ P.map (fun p => (v p.1, v p.2))) ∨ t = v k ∨ t = v j) ∧
              laws.word (v r) Q (laws.action (v r) (v j) t ⊥) ≤ laws.wordsValue (v r) v upper := by
        by_cases hj : j = r ∨ (∃ c, (j, c) ∈ P) ∨ ∃ c, (c, j) ∈ P
        · exact Or.inl (lift_outside v r j P hj)
        · obtain ⟨Q, t, suffix, hQ, hf, hs, ht⟩ := covering_witness r j k P rest lower upper hjk hj hsemantic
          right
          refine ⟨Q.map (fun p => (v p.1, v p.2)), v t, ?_, ?_, ?_,
            laws.witness_le_wordsValue (v r) v j t Q suffix upper hQ⟩
          · intro p hp
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            exact lift_many v r q.1 P (hf q hq)
          · intro p hp
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            rcases hs q hq with hs | hs
            · exact Or.inl (lift_outside v r q.2 P hs)
            · exact Or.inr (congrArg v hs)
          · rcases ht with ht | ht | ht
            · exact Or.inl (lift_outside v r t P ht)
            · exact Or.inr (Or.inl (congrArg v ht))
            · exact Or.inr (Or.inr (congrArg v ht))
      intro j k hjk
      rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hsources a b (Or.inl hword')
      · exact hsources b a (Or.inr hword')
  have hwords : ∀ W ∈ lower, laws.word (v r) (W.map (fun p => (v p.1, v p.2))) ⊥ ≤ laws.wordsValue (v r) v upper := by
    intro W hW
    exact hprefix W [] (by simpa only [List.append_nil] using hW)
  have hjoin (language : List (List (Var × Var))) :
      (∀ W ∈ language, laws.word (v r) (W.map (fun p => (v p.1, v p.2))) ⊥ ≤ laws.wordsValue (v r) v upper) →
        laws.wordsValue (v r) v language ≤ laws.wordsValue (v r) v upper := by
    induction language with
    | nil => intro _; exact bot_le
    | cons W language ih =>
      intro hall
      rw [laws.wordsValue_cons]
      exact sup_le (hall W (List.mem_cons_self ..))
        (ih (fun Q hQ => hall Q (List.mem_cons_of_mem _ hQ)))
  exact hjoin lower hwords

end KFOL.Owner.FiniteBasis.Laws

namespace KFOL.Owner.FiniteBasis

universe u v

private theorem evalFour_owner {Var : Type v} (t : Term Unit Var) (v : Var → Four) :
    t.evalFour v = .owner ↔ v t.root = .owner := by
  induction t using Term.induction_owner with
  | var j => rfl
  | step s t _ ht => simpa only [Term.evalFour_step, Four.reset_owner, Term.root_step] using ht
  | guarded a x y z hx _ _ => simpa only [Term.evalFour_guarded, Four.guarded_owner, Term.root_guarded] using hx

private theorem roots_eq_of_four {Var : Type v} (s t : Term Unit Var)
    (hvalid : ∀ v : Var → Four, s.evalFour v = t.evalFour v) : s.root = t.root := by
  classical
  by_contra hn
  let w : Var → Four := fun i => if i = s.root then .owner else .other
  have hs : s.evalFour w = .owner := (evalFour_owner s w).mpr (by simp [w])
  have ht : t.evalFour w = .owner := (hvalid w).symm.trans hs
  have hw := (evalFour_owner t w).mp ht
  simp [w, Ne.symm hn] at hw

namespace Laws

variable {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    (laws : FiniteBasis.Laws (resetOperation M) (guardedOperation M))

include laws

/-- Every Four-valid native identity holds in every arbitrary model of the
forty explicitly listed identities. All word witnesses are derived internally. -/
theorem equal_of_four {Var : Type v} (s t : Term Unit Var)
    (hvalid : ∀ w : Var → Four, s.evalFour w = t.evalFour w) (v : Var → M) :
    s.realize v = t.realize v := by
  let _ := fourStructure (Role := Unit)
  let _ := laws.fiberSemilattice (v s.root)
  let _ := laws.fiberOrderBot (v s.root)
  have hr := roots_eq_of_four s t hvalid
  have hFour (w : Var → Four) :
      (four_laws.wordsValue .ambiguous w s.actionWords).val =
        (four_laws.wordsValue .ambiguous w t.actionWords).val := by
    calc
      _ = Four.reset (s.evalFour w) .ambiguous := four_laws.word_normal_form .ambiguous s w
      _ = Four.reset (t.evalFour w) .ambiguous := congrArg (fun x => Four.reset x .ambiguous) (hvalid w)
      _ = _ := (four_laws.word_normal_form .ambiguous t w).symm
  have hleft := laws.wordsValue_le_of_four s.root s.actionWords t.actionWords
    (fun w hw => (hFour w) ▸ hw) v
  have hright := laws.wordsValue_le_of_four s.root t.actionWords s.actionWords
    (fun w hw => (hFour w).symm ▸ hw) v
  have heq := congrArg Subtype.val (le_antisymm hleft hright)
  rw [laws.word_normal_form, laws.word_normal_form] at heq
  calc
    s.realize v = resetOperation M (s.realize v) (v s.root) := (laws.term_fixed s v).symm
    _ = resetOperation M (t.realize v) (v s.root) := heq
    _ = resetOperation M (t.realize v) (v t.root) := congrArg (fun r => resetOperation M (t.realize v) (v r)) hr
    _ = t.realize v := laws.term_fixed t v

end Laws

/-- The exact displayed forty-equation family is a complete equational basis,
with the independent derivation relation and arbitrary-depth native syntax. -/
theorem isBasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four theory := by
  let _ := fourStructure (Role := Unit)
  intro e
  constructor
  · intro hvalid
    apply Equational.derives_of_valid_in_models theory e.lhs e.rhs
    intro M str _ hm v
    exact (models_theory_iff.mp hm).equal_of_four e.lhs e.rhs hvalid v
  · intro hderive
    exact hderive.sound Four models_four

/-- A finite basis exists, and the exhibited family uses at most six actual
variables per identity. The four-variable lower bound is proved separately. -/
theorem hasFiniteBasis : letI := fourStructure (Role := Unit); Equational.HasFiniteBasis (Symbol Unit) Four :=
  ⟨theory, theory_finite, isBasis⟩

end KFOL.Owner.FiniteBasis
