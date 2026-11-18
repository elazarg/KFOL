module

public import KFOL.Core.SourceReciprocity
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Preorder.Finite

/-! # A topological test for a marked source query

A negative probe may post atoms only before its own head. At a fixed
positive coloring an input is active if every loss there can be blocked
by a mismatching posting at an earlier active input.
-/

@[expose] public section

namespace KFOL.Core.Sources.Passive

/-- The posted owner in a passive status, forgetting which owner observes it. -/
def color {Role : Type*} {k : Role} : Passive k → Option Role
  | .neutral => none
  | .atom r => some r.val

end KFOL.Core.Sources.Passive

namespace KFOL.Core.AcyclicSourceQueries

open Sources
open scoped Classical

universe u v w
variable {Role : Type u} {Var : Type v} {Row : Type w}

/-- A probe has no posting at its own head. -/
noncomputable def posting (z : ProbeIndex Role Var) (i : Var) : Option Role :=
  if ne : i ≠ z.2.1 then (z.2.2 ⟨i,ne⟩).color else none

private theorem posted_atom (three : Fin 3 ↪ Role) (z : ProbeIndex Role Var) (i : Var) (r : Role)
    (post : posting z i = some r) : probeAt three z i = WinnerSet.singleton r := by
  by_cases he : i = z.2.1
  · simp [posting,he] at post
  · rw [probeAt,probe_other three z.1 z.2.1 z.2.2 i he]
    cases h : z.2.2 ⟨i,he⟩ with
    | neutral => simp [posting,he,h,Passive.color] at post
    | atom s =>
      have eq : s.val = r := by simpa [posting,he,h,Passive.color] using post
      exact congrArg WinnerSet.singleton eq

variable [LinearOrder Var] [Fintype Var]

/-- The activation test depends only on predecessors. The proper positive
coloring is independent of the queried head. -/
noncomputable def Active [Finite Var] {k : Role} (p : Var → Passive k) (neg : Row → ProbeIndex Role Var) :
    Var → Prop :=
  wellFounded_lt.fix fun h prev => ∀ z, (neg z).2.1 = h →
    ∃ (i : Var) (lt : i < h) (r : Role),
      posting (neg z) i = some r ∧ (p i).color ≠ some r ∧ prev i lt

theorem active_iff {k : Role} (p : Var → Passive k) (neg : Row → ProbeIndex Role Var) (h : Var) :
    Active p neg h ↔ ∀ z, (neg z).2.1 = h → ∃ i < h, ∃ r,
      posting (neg z) i = some r ∧ (p i).color ≠ some r ∧ Active p neg i := by
  unfold Active
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

private def Fixes (fixed : Var → Role → Prop) (v : Var → WinnerSet Role) :=
  ∀ i r, fixed i r → v i = WinnerSet.singleton r

private def Independent (t : Term Role Var) (fixed : Var → Role → Prop) (i : Var) :=
  ∀ v w, Fixes fixed v → Fixes fixed w → (∀ a, a ≠ i → v a = w a) → t.eval v = t.eval w

omit [Fintype Var] in
private theorem independent_subset (t : Term Role Var) (fixed : Var → Role → Prop)
    (D : Finset Var) (indep : ∀ i ∈ D, Independent t fixed i)
    (v w : Var → WinnerSet Role) (hv : Fixes fixed v) (hw : Fixes fixed w)
    (agree : ∀ a ∉ D, v a = w a) : t.eval v = t.eval w := by
  classical
  induction D using Finset.induction_on generalizing v with
  | empty => exact congrArg t.eval (funext (fun a => agree a (Finset.notMem_empty a)))
  | insert i D _ ih =>
    let v' := Function.update v i (w i)
    have fixed' : Fixes fixed v' := by
      intro a r ha
      by_cases he : a = i
      · subst a; simpa [v'] using hw i r ha
      · simpa [v',he] using hv a r ha
    have one := indep i (Finset.mem_insert_self ..) v v' hv fixed'
      (fun a ha => (Function.update_of_ne ha _ _).symm)
    apply one.trans (ih (fun a ha => indep a (Finset.mem_insert_of_mem ha)) v' fixed' ?_)
    intro a ha
    by_cases he : a = i
    · simp [v',he]
    · simpa [v',he] using agree a (by simp [he,ha])

private theorem inactive_independent {k : Role} (p : Var → Passive k) (neg : Row → ProbeIndex Role Var)
    (earlier : ∀ z i r, posting (neg z) i = some r → i < (neg z).2.1)
    (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (safe : ∀ z, (neg z).1 ∉ (t.eval (probeAt three (neg z))).val) :
    ∀ h, ¬Active p neg h → Independent t (fun i r => Active p neg i ∧ (p i).color = some r) h := by
  classical
  let fixed := fun i r => Active p neg i ∧ (p i).color = some r
  intro h
  induction h using WellFoundedLT.induction with
  | ind h ih =>
    intro inactive v w hv hw away
    rw [active_iff] at inactive
    push Not at inactive
    obtain ⟨z,hz,bad⟩ := inactive
    let patched (v : Var → WinnerSet Role) (i : Var) : WinnerSet Role :=
      if Active p neg i then v i else
        match posting (neg z) i with
        | some r => WinnerSet.singleton r
        | none => v i
    have patch_fixed (a : Var → WinnerSet Role) (ha : Fixes fixed a) : Fixes fixed (patched a) := by
      intro i r hi
      simpa [patched,hi.1] using ha i r hi
    let D := Finset.univ.filter fun i => i < h ∧ ¬Active p neg i
    have Dmem (i : Var) : i ∈ D ↔ i < h ∧ ¬Active p neg i := by simp [D]
    have unchanged (v : Var → WinnerSet Role) (hv : Fixes fixed v) : t.eval v = t.eval (patched v) := by
      apply independent_subset t fixed D (fun i hi => ih i ((Dmem i).mp hi).1 ((Dmem i).mp hi).2)
        v (patched v) hv (patch_fixed v hv)
      intro i outside
      by_cases live : Active p neg i
      · simp [patched,live]
      · cases hp : posting (neg z) i with
        | none => simp [patched,live,hp]
        | some r => exact (outside ((Dmem i).mpr ⟨hz ▸ earlier z i r hp,live⟩)).elim
    apply (unchanged v hv).trans
    apply Eq.trans _ (unchanged w hw).symm
    apply (probe_loss_iff_cofactor_independent three t ht _ _ _).mp (safe z)
    · intro i hi
      have hi' : i ≠ h := hz ▸ hi
      simp only [patched, away i hi']
    · intro i r hr
      have post : posting (neg z) i.val = some r.val := by simp [posting,i.property,hr,Passive.color]
      by_cases live : Active p neg i.val
      · have color : (p i.val).color = some r.val := by
          by_contra hne
          exact bad i.val (hz ▸ earlier z i.val r.val post) r.val post hne live
        simpa [patched,live] using hv i.val r.val ⟨live,color⟩
      · simp [patched,live,post]

/-- Attach the same earlier input once for each of its listed owners. -/
private def attach (i : Var) (rs : List Role) (t : Term Role Var) : Term Role Var :=
  rs.foldr (fun r s => .choice r s (.var i)) t

omit [LinearOrder Var] [Fintype Var] in
private theorem attach_core {t : Term Role Var} (ht : t.IsCore) (i : Var) (rs : List Role) :
    (attach i rs t).IsCore := by
  induction rs with
  | nil => exact ht
  | cons _ _ ih => exact ⟨ih,trivial⟩

omit [LinearOrder Var] [Fintype Var] in
private theorem attach_quiet {v : Var → WinnerSet Role} {k : Role} {i : Var}
    (hi : k ∉ (v i).val) (rs : List Role) {t : Term Role Var}
    (ht : k ∉ (t.eval v).val) : k ∉ ((attach i rs t).eval v).val := by
  induction rs with
  | nil => exact ht
  | cons r _ ih => exact fun hit => (WinnerSet.choice_subset_union r _ _ hit).elim ih hi

omit [LinearOrder Var] [Fintype Var] in
private theorem attach_blocks {v : Var → WinnerSet Role} {k r : Role} {i : Var}
    (hi : k ∉ (v i).val) (atom : v i = WinnerSet.singleton r) (rs : List Role)
    (hr : r ∈ rs) (t : Term Role Var) : k ∉ ((attach i rs t).eval v).val := by
  induction rs with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with he | rest
    · subst s
      change k ∉ (WinnerSet.choice r _ (v i)).val
      simpa [WinnerSet.choice,atom] using hi
    · exact fun hit => (WinnerSet.choice_subset_union s _ _ hit).elim (ih rest) hi

omit [LinearOrder Var] [Fintype Var] in
private theorem attach_keeps {v : Var → WinnerSet Role} {k : Role} {i : Var} (rs : List Role)
    (unblocked : ∀ r ∈ rs, r ≠ k → v i ≠ WinnerSet.singleton r) (t : Term Role Var)
    (hit : k ∈ (t.eval v).val) : k ∈ ((attach i rs t).eval v).val := by
  induction rs with
  | nil => exact hit
  | cons r rs ih =>
    have old := ih (fun a ha => unblocked a (List.mem_cons_of_mem _ ha))
    by_cases eq : r = k
    · subst r; exact (WinnerSet.mem_choice_owner _ _ _).mpr (Or.inl old)
    · refine (WinnerSet.mem_choice_other r k eq _ _).mpr
        ⟨Or.inl old, ?_, unblocked r List.mem_cons_self eq⟩
      intro atom
      change (attach i rs t).eval v = WinnerSet.singleton r at atom
      rw [atom] at old
      exact eq old.symm

private def spine (rs : Var → List Role) (h : Var) (xs : List Var) : Term Role Var :=
  xs.foldr (fun i t => attach i (rs i) t) (.var h)

omit [Fintype Var] in
private theorem spine_blocks (rs : Var → List Role) (h : Var) (xs : List Var)
    (sorted : xs.Pairwise (· ≤ ·)) (v : Var → WinnerSet Role) (k : Role) {i : Var} (hi : i ∈ xs)
    (absent : ∀ a ≤ i, k ∉ (v a).val) {r : Role}
    (hr : r ∈ rs i) (atom : v i = WinnerSet.singleton r) : k ∉ ((spine rs h xs).eval v).val := by
  induction xs with
  | nil => simp at hi
  | cons a xs ih =>
    rcases List.mem_cons.mp hi with eq | rest
    · subst a; exact attach_blocks (absent i le_rfl) atom _ hr _
    · have lea := (List.pairwise_cons.mp sorted).1 i rest
      exact attach_quiet (absent a lea) _ (ih (List.pairwise_cons.mp sorted).2 rest)

omit [LinearOrder Var] [Fintype Var] in
private theorem attach_length (i : Var) (rs : List Role) (t : Term Role Var) :
    (attach i rs t).inputOccurrences.length = t.inputOccurrences.length + rs.length := by
  induction rs with
  | nil => simp [attach]
  | cons r rs ih =>
    change ((attach i rs t).inputOccurrences ++ [(i,1)]).length = _
    simp [ih, Nat.add_assoc]

omit [LinearOrder Var] [Fintype Var] in
private theorem spine_length (rs : Var → List Role) (K : ℕ) (width : ∀ i, (rs i).length ≤ K)
    (h : Var) (xs : List Var) : (spine rs h xs).inputOccurrences.length ≤ 1 + K * xs.length := by
  induction xs with
  | nil => simp [spine,Term.inputOccurrences]
  | cons i xs ih =>
    change (attach i (rs i) (spine rs h xs)).inputOccurrences.length ≤ _
    rw [attach_length, List.length_cons, Nat.mul_succ]
    have hi := width i
    omega

/-- An active query has a pure-core witness with at most one leaf for the
head and one for each (owner, other input) pair. -/
theorem exists_small_witness [Fintype Role] {k : Role} (p : Var → Passive k)
    (neg : Row → ProbeIndex Role Var) (three : Fin 3 ↪ Role) (h : Var) (active : Active p neg h) :
    ∃ t : Term Role Var, t.IsCore ∧ (∀ z, (neg z).1 ∉ (t.eval (probeAt three (neg z))).val) ∧
      k ∈ (t.eval (probe three k h (fun i => p i.val))).val ∧
      t.inputOccurrences.length ≤ 1 + Fintype.card Role * (Fintype.card Var - 1) := by
  classical
  let rs (i : Var) := (Finset.univ.filter fun r => (p i).color ≠ some r).toList
  let xs := (Finset.univ.filter fun i => i < h ∧ Active p neg i).sort
  have memRoles (r i) : r ∈ rs i ↔ (p i).color ≠ some r := by simp [rs]
  have memVars (i) : i ∈ xs ↔ i < h ∧ Active p neg i := by simp [xs]
  have sorted : xs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  refine ⟨spine rs h xs, ?_, ?_, ?_, ?_⟩
  · suffices ∀ ys, (spine rs h ys).IsCore from this xs
    intro ys
    induction ys with
    | nil => trivial
    | cons i ys ih => exact attach_core ih i (rs i)
  · intro z
    let v := probeAt three (neg z)
    let b := (neg z).2.1
    let m := (neg z).1
    have only (i : Var) : m ∈ (v i).val ↔ i = b := mem_probe_iff three _ _ _ i
    by_cases used : b = h ∨ b ∈ xs
    · have live : Active p neg b := used.elim (fun eq => eq ▸ active) (fun mem => ((memVars _).mp mem).2)
      obtain ⟨i,lt,r,posted,miss,livei⟩ := (active_iff p neg b).mp live z rfl
      have le : b ≤ h := used.elim Eq.le (fun mem => ((memVars _).mp mem).1.le)
      have inside := (memVars i).mpr ⟨lt_of_lt_of_le lt le,livei⟩
      exact spine_blocks rs h xs sorted v m inside
        (fun a ha hit => (lt_of_le_of_lt ha lt).ne ((only a).mp hit)) ((memRoles r i).mpr miss)
        (posted_atom three (neg z) i r posted)
    · have base : m ∉ (v h).val := fun hit => used (Or.inl ((only h).mp hit).symm)
      have away (i) (hi : i ∈ xs) : m ∉ (v i).val := fun hit =>
        used (Or.inr (((only i).mp hit) ▸ hi))
      suffices ∀ ys, (∀ i ∈ ys, m ∉ (v i).val) → m ∉ ((spine rs h ys).eval v).val from this xs away
      intro ys
      induction ys with
      | nil => exact fun _ => base
      | cons i ys ih =>
        intro no
        exact attach_quiet (no i List.mem_cons_self) _ (ih (fun a ha => no a (List.mem_cons_of_mem _ ha)))
  · let v := probe three k h (fun i => p i.val)
    suffices ∀ ys, (∀ i ∈ ys, i < h) → k ∈ ((spine rs h ys).eval v).val from
      this xs fun i hi => ((memVars _).mp hi).1
    intro ys
    induction ys with
    | nil => exact fun _ => (mem_probe_iff three k h (fun i => p i.val) h).mpr rfl
    | cons i ys ih =>
      intro before
      have ne := (before i List.mem_cons_self).ne
      apply attach_keeps _ _ _ (ih fun a ha => before a (List.mem_cons_of_mem _ ha))
      intro r hr hrk atom
      rw [show v i = representative three k (p i) from probe_other three k h _ i ne] at atom
      have col := (representative_atom_iff three k (p i) ⟨r,hrk⟩).mp atom
      exact (memRoles r i).mp hr (by simp [col,Passive.color])

  · have width (i : Var) : (rs i).length ≤ Fintype.card Role := by
      simpa [rs] using Finset.card_le_card (Finset.filter_subset (fun r => (p i).color ≠ some r) Finset.univ)
    have before (i : Var) (hi : i ∈ Finset.univ.filter fun i => i < h ∧ Active p neg i) :
        i ∈ Finset.univ.erase h := Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hi).2.1.ne, Finset.mem_univ _⟩
    have count : xs.length ≤ Fintype.card Var - 1 := by
      simpa [xs] using Finset.card_le_card before
    exact (spine_length rs _ width h xs).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ count) 1)

/-- The topological activation test exactly recognizes the existence of a core
word omitting every negative probe and supplying the one requested source. -/
theorem exists_marked_iff_active [Fintype Role] {k : Role} (p : Var → Passive k)
    (neg : Row → ProbeIndex Role Var)
    (earlier : ∀ z i r, posting (neg z) i = some r → i < (neg z).2.1)
    (three : Fin 3 ↪ Role) (h : Var) :
    (∃ t : Term Role Var, t.IsCore ∧ (∀ z, (neg z).1 ∉ (t.eval (probeAt three (neg z))).val) ∧
      k ∈ (t.eval (probe three k h (fun i => p i.val))).val) ↔ Active p neg h := by
  refine ⟨?_,fun active => ?_⟩
  swap
  · obtain ⟨t,ht,hs,hit,_⟩ := exists_small_witness p neg three h active
    exact ⟨t,ht,hs,hit⟩
  rintro ⟨t,ht,safe,hit⟩
  by_contra dead
  have ind := inactive_independent p neg earlier three t ht safe h dead
  apply (probe_loss_iff_cofactor_independent three t ht k h (fun i => p i.val)).mpr ?_ hit
  intro v w away posted
  apply ind v w ?_ ?_ away
  · intro i r fixed
    have ne : i ≠ h := fun eq => dead (eq ▸ fixed.1)
    cases col : p i with
    | neutral => simp [col,Passive.color] at fixed
    | atom s =>
      have eq : s.val = r := by simpa [col,Passive.color] using fixed.2
      exact (posted ⟨i,ne⟩ s col).trans (congrArg WinnerSet.singleton eq)
  · intro i r fixed
    have ne : i ≠ h := fun eq => dead (eq ▸ fixed.1)
    rw [← away i ne]
    cases col : p i with
    | neutral => simp [col,Passive.color] at fixed
    | atom s =>
      have eq : s.val = r := by simpa [col,Passive.color] using fixed.2
      exact (posted ⟨i,ne⟩ s col).trans (congrArg WinnerSet.singleton eq)

/-- One actual negative row per inactive head preserves the answers for
every head at once; no rows at active heads are needed. -/
theorem exists_certificate {k : Role} (p : Var → Passive k) (neg : Row → ProbeIndex Role Var) :
    ∃ select : {i : Var // ¬Active p neg i} → Row,
      (∀ i, (neg (select i)).2.1 = i.val) ∧ ∀ h, Active p (neg ∘ select) h ↔ Active p neg h := by
  classical
  have find (i : {i : Var // ¬Active p neg i}) :
      ∃ z, (neg z).2.1 = i.val ∧ ∀ a < i.val, ∀ r, posting (neg z) a = some r →
        (p a).color ≠ some r → ¬Active p neg a := by
    have hn := i.property
    simpa only [active_iff p neg i.val, not_forall, not_exists, not_and, exists_prop] using hn
  choose select head bad using find
  refine ⟨select,head,fun h => ?_⟩
  induction h using WellFoundedLT.induction with
  | ind h ih =>
    constructor
    · intro live
      by_contra dead
      let v : {i : Var // ¬Active p neg i} := ⟨h,dead⟩
      obtain ⟨i,lt,r,post,miss,prev⟩ := (active_iff p (neg ∘ select) h).mp live v (head v)
      exact bad v i lt r post miss ((ih i lt).mp prev)
    · intro live
      apply (active_iff p (neg ∘ select) h).mpr
      intro v hv
      obtain ⟨i,lt,r,post,miss,prev⟩ := (active_iff p neg h).mp live (select v) hv
      exact ⟨i,lt,r,post,miss,(ih i lt).mpr prev⟩

end KFOL.Core.AcyclicSourceQueries
