module

public import KFOL.Owner.Basis.CommonRoot

/-! Normalization of arbitrary native terms into finite joins of common-root
unary action words in every algebra satisfying the thirty-six equations. -/

@[expose] public section

namespace KFOL.Owner.FiniteBasis.Laws

universe u

variable {M : Type u} {f : M → M → M} {h : M → M → M → M} (laws : FiniteBasis.Laws f h)

include laws

/-- The projected reset normalization equation from the report. -/
theorem project_reset (r s t j : M) (ht : f t j = t) :
    f (f s t) r = f (f (f (f s r) j) r) (f t r) := by
  have hst : f s t = f (f s j) (f t j) := by
    simpa only [ht] using laws.reset_split j s t
  calc
    _ = f (f (f s j) (f t j)) r := congrArg (fun z => f z r) hst
    _ = f (f (f s j) r) (f t r) := by
      simpa only [laws.R3, ht] using laws.project_join r j s t
    _ = _ := congrArg (fun z => f z (f t r)) (laws.reset_back r j s)

/-- The projected H normalization equation from the report. -/
theorem project_guarded (r s t u i j k : M) (hs : f s i = s) (ht : f t j = t) (hu : f u k = u) :
    f (h s t u) r = f (f s r)
      (f (f (f (h r (f (f t r) j) k) (h r (f (f u r) k) j)) i) r) := by
  have hh : h s t u = f s (h i t u) := by
    simpa only [hs] using laws.h_expand i t u s
  have hG : f (f (f s r) i) r = f s r := by
    simpa only [hs] using (laws.reset_back r i s).symm
  have hsplit : h r t u = f (h r (f (f t r) j) k) (h r (f (f u r) k) j) := by
    calc
      _ = f (h r (f t j) k) (h r j (f u k)) := by
        simpa only [ht, hu, laws.h_root] using laws.h_split r j k t u
      _ = _ := by rw [laws.h_back r j k t, laws.h_sym r j (f u k), laws.h_back r k j u]
  calc
    _ = f (f s (h i t u)) r := congrArg (fun z => f z r) hh
    _ = f (f (f (f s r) i) r) (f (h i t u) r) := laws.project_reset r s (h i t u) i (laws.h_root i t u)
    _ = f (f s r) (f (f (h r t u) i) r) := by rw [hG, laws.h_reroot r i u t]
    _ = _ := congrArg (fun z => f (f s r) (f (f z i) r)) hsplit

omit laws in
/-- Every native term is fixed by its syntactically determined root, in every
model of the finite basis. This does not use the intended winner-set model. -/
theorem term_fixed [str : (Equational.language (Symbol Unit)).Structure M]
    (hlaws : FiniteBasis.Laws (resetOperation M) (guardedOperation M))
    {Var : Type*} (t : Term Unit Var) (v : Var → M) :
    resetOperation M (t.realize v) (v t.root) = t.realize v := by
  induction t using Term.induction_owner with
  | var j => exact hlaws.R1 (v j)
  | step s t _ ht =>
    simpa only [realize_step, Term.root_step, ht] using
      hlaws.reset_laws.e8 (s.realize v) (t.realize v) (v t.root)
  | guarded a x y z hx _ _ =>
    cases a
    have he : guardedOperation M (x.realize v) (y.realize v) (z.realize v) =
        resetOperation M (x.realize v) (guardedOperation M (v x.root) (y.realize v) (z.realize v)) := by
      simpa only [hx] using hlaws.h_expand (v x.root) (y.realize v) (z.realize v) (x.realize v)
    simp only [realize_guarded, Term.root_guarded, he]
    simpa only [hlaws.h_root] using hlaws.reset_laws.e8 (x.realize v)
      (guardedOperation M (v x.root) (y.realize v) (z.realize v)) (v x.root)

end KFOL.Owner.FiniteBasis.Laws

namespace KFOL.Owner.Term

universe v

@[simp] theorem actionWords_var {Var : Type v} (j : Var) :
    actionWords (.var j : Term Unit Var) = [[(j, j)]] := rfl

@[simp] theorem actionWords_step {Var : Type v} (s t : Term Unit Var) :
    (step s t).actionWords = s.actionWords.map (fun w => [(t.root, t.root)] ++ w) ++ t.actionWords := rfl

@[simp] theorem actionWords_guarded {Var : Type v} (x y z : Term Unit Var) :
    (guarded () x y z).actionWords = x.actionWords ++
      ((y.actionWords.map (fun w => [(x.root, x.root), (y.root, z.root)] ++ w)) ++
        (z.actionWords.map (fun w => [(x.root, x.root), (z.root, y.root)] ++ w))) := rfl

theorem actionWords_ne_nil {Var : Type v} (t : Term Unit Var) : t.actionWords ≠ [] := by
  induction t using induction_owner with
  | var j => exact List.cons_ne_nil _ _
  | step s t _ ht =>
    intro he
    exact ht (List.append_eq_nil_iff.mp he).2
  | guarded a x y z hx _ _ =>
    intro he
    exact hx (List.append_eq_nil_iff.mp he).1

end KFOL.Owner.Term

namespace KFOL.Owner.FiniteBasis.Laws

universe u v

variable {M : Type u} {f : M → M → M} {h : M → M → M → M} (laws : FiniteBasis.Laws f h)

/-- The join of a finite language of word values, with root as empty join. -/
def wordsValue (r : M) {Var : Type v} (v : Var → M) (language : List (List (Var × Var))) : RootFiber f r := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  exact language.foldr (fun w rest => laws.word r (w.map (fun p => (v p.1, v p.2))) ⊥ ⊔ rest) ⊥

theorem wordsValue_nil (r : M) {Var : Type v} (v : Var → M) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.wordsValue r v [] = ⊥ := rfl

theorem wordsValue_cons (r : M) {Var : Type v} (v : Var → M) (w : List (Var × Var))
    (rest : List (List (Var × Var))) :
    letI := laws.fiberSemilattice r
    letI := laws.fiberOrderBot r
    laws.wordsValue r v (w :: rest) =
      laws.word r (w.map (fun p => (v p.1, v p.2))) ⊥ ⊔ laws.wordsValue r v rest := rfl

theorem wordsValue_append (r : M) {Var : Type v} (v : Var → M)
    (left right : List (List (Var × Var))) :
    letI := laws.fiberSemilattice r
    laws.wordsValue r v (left ++ right) = laws.wordsValue r v left ⊔ laws.wordsValue r v right := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  induction left with
  | nil => simp only [List.nil_append, laws.wordsValue_nil, bot_sup_eq]
  | cons w rest ih =>
    simp only [List.cons_append, laws.wordsValue_cons, ih]
    exact (sup_assoc ..).symm

/-- Actions preserve nonempty joins; the empty case would incorrectly erase
their constant contribution. -/
theorem wordsValue_prefix (r : M) {Var : Type v} (v : Var → M) (front : List (Var × Var))
    (language : List (List (Var × Var))) (hne : language ≠ []) :
    laws.wordsValue r v (language.map (fun w => front ++ w)) =
      laws.word r (front.map (fun p => (v p.1, v p.2))) (laws.wordsValue r v language) := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  induction language with
  | nil => exact False.elim (hne rfl)
  | cons w rest ih =>
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, laws.wordsValue_cons, laws.wordsValue_nil,
        sup_bot_eq, List.map_append, laws.word_append]
    | cons w' rest =>
      rw [List.map_cons, laws.wordsValue_cons, ih (List.cons_ne_nil _ _), laws.wordsValue_cons,
        laws.word_sup]
      simp only [List.map_append, laws.word_append, laws.wordsValue_cons, laws.word_sup]

end KFOL.Owner.FiniteBasis.Laws

namespace KFOL.Owner.FiniteBasis.Laws

universe u v

variable {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    (laws : FiniteBasis.Laws (resetOperation M) (guardedOperation M))

/-- The explicit finite language normalizes every native term in every model
of the thirty-six identities. No finite carrier or intended-model equality is used. -/
theorem word_normal_form {Var : Type v} (r : M) (t : Term Unit Var) (v : Var → M) :
    (laws.wordsValue r v t.actionWords).val = resetOperation M (t.realize v) r := by
  let _ := laws.fiberSemilattice r
  let _ := laws.fiberOrderBot r
  induction t using Term.induction_owner with
  | var j =>
    simp only [Term.actionWords_var, laws.wordsValue_cons, laws.wordsValue_nil,
      List.map_cons, List.map_nil, word_cons, word_nil, sup_bot_eq]
    rw [laws.action_diagonal]
    exact laws.G_zero r (v j)
  | step s t hs ht =>
    rw [Term.actionWords_step, laws.wordsValue_append,
      laws.wordsValue_prefix r v [(t.root, t.root)] s.actionWords s.actionWords_ne_nil]
    change resetOperation M (laws.action r (v t.root) (v t.root) (laws.wordsValue r v s.actionWords)).val
      (laws.wordsValue r v t.actionWords).val = resetOperation M ((Term.step s t).realize v) r
    rw [laws.action_diagonal, hs, ht, realize_step]
    exact (laws.project_reset r (s.realize v) (t.realize v) (v t.root) (laws.term_fixed t v)).symm
  | guarded a x y z hx hy hz =>
    cases a
    rw [Term.actionWords_guarded, laws.wordsValue_append, laws.wordsValue_append,
      laws.wordsValue_prefix r v [(x.root, x.root), (y.root, z.root)] y.actionWords y.actionWords_ne_nil,
      laws.wordsValue_prefix r v [(x.root, x.root), (z.root, y.root)] z.actionWords z.actionWords_ne_nil]
    change ((laws.wordsValue r v x.actionWords) ⊔
      (laws.action r (v x.root) (v x.root) (laws.action r (v y.root) (v z.root) (laws.wordsValue r v y.actionWords)) ⊔
        laws.action r (v x.root) (v x.root) (laws.action r (v z.root) (v y.root) (laws.wordsValue r v z.actionWords)))).val = _
    have hmap (A B : RootFiber (resetOperation M) r) :
        laws.action r (v x.root) (v x.root) A ⊔ laws.action r (v x.root) (v x.root) B =
          laws.action r (v x.root) (v x.root) (A ⊔ B) :=
      (map_sup (laws.actionHom r (v x.root) (v x.root)) A B).symm
    rw [hmap]
    change resetOperation M (laws.wordsValue r v x.actionWords).val
      (laws.action r (v x.root) (v x.root)
        (laws.action r (v y.root) (v z.root) (laws.wordsValue r v y.actionWords) ⊔
          laws.action r (v z.root) (v y.root) (laws.wordsValue r v z.actionWords))).val = _
    rw [laws.action_diagonal]
    change resetOperation M (laws.wordsValue r v x.actionWords).val
      (resetOperation M (resetOperation M
        (resetOperation M
          (guardedOperation M r (resetOperation M (laws.wordsValue r v y.actionWords).val (v y.root)) (v z.root))
          (guardedOperation M r (resetOperation M (laws.wordsValue r v z.actionWords).val (v z.root)) (v y.root)))
        (v x.root)) r) = _
    rw [hx, hy, hz, realize_guarded]
    exact (laws.project_guarded r (x.realize v) (y.realize v) (z.realize v)
      (v x.root) (v y.root) (v z.root) (laws.term_fixed x v) (laws.term_fixed y v) (laws.term_fixed z v)).symm

end KFOL.Owner.FiniteBasis.Laws
