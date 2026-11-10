module

public import KFOL.Owner.Basis.WinnerSet

/-! A six-element algebra satisfies every four-variable owner identity but
fails a five-variable instance of the action-band identity. The local
certificates use the complete thirty-six-law basis, so the conclusion is
independent of term depth. -/

@[expose] public section

namespace KFOL.Owner.FourVariableObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option maxSynthPendingDepth 128

theorem reset_ne : ∀ (e : Fin 5) (x y : Carrier),
    x ≠ excluded e → y ≠ excluded e → reset x y ≠ excluded e := by decide

theorem guarded_ne : ∀ (e : Fin 5) (x y z : Carrier),
    x ≠ excluded e → y ≠ excluded e → z ≠ excluded e → guarded x y z ≠ excluded e := by decide

instance (e : Fin 5) : (Equational.language (Symbol Unit)).Structure (Local e) where
  funMap f args := match f with
    | .reset => ⟨reset (args 0).val (args 1).val, reset_ne e _ _ (args 0).property (args 1).property⟩
    | .guarded _ => ⟨guarded (args 0).val (args 1).val (args 2).val,
        guarded_ne e _ _ _ (args 0).property (args 1).property (args 2).property⟩
  RelMap r := nomatch r

private theorem law_R1 : ∀ r : Carrier, (reset r r) = r := by decide

private theorem law_R2 : ∀ r a : Carrier, (reset (reset r a) r) = (reset a r) := by decide

private theorem law_R3 : ∀ r a : Carrier, (reset (reset r a) a) = (reset r a) := by decide

private theorem law_R4 : ∀ r a b : Carrier, (reset r (reset (reset r a) b)) = (reset r (reset a b)) := by decide

private theorem law_R5 : ∀ r a b : Carrier, (reset (reset (reset r a) b) a) = (reset (reset r b) a) := by decide

private theorem law_R6 : ∀ r a b : Carrier, (reset r (reset a b)) = (reset a (reset r b)) := by decide

private theorem law_h_sym : ∀ r a b : Carrier, (guarded r a b) = (guarded r b a) := by decide

private theorem law_h_minor : ∀ r a : Carrier, (guarded r a a) = (reset a r) := by decide

private theorem law_h_root : ∀ r a b : Carrier, (reset (guarded r a b) r) = (guarded r a b) := by decide

private theorem law_h_expand : ∀ r a b u : Carrier, (guarded (reset u r) a b) = (reset (reset u r) (guarded r a b)) := by decide

private theorem law_h_split : ∀ r a b u v : Carrier, (guarded r (reset u a) (reset v b)) = (reset (reset (guarded r (reset u a) b) r) (reset (guarded r a (reset v b)) r)) := by decide

private theorem law_h_back : ∀ r a b u : Carrier, (guarded r (reset u a) b) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_h_reroot : ∀ r a b u : Carrier, (reset (guarded a u b) r) = (reset (reset (guarded r u b) a) r) := by decide

private theorem law_h_insert : ∀ r a b : Carrier, (guarded r a b) = (guarded r (reset r a) b) := by decide

private theorem law_project_join : ∀ r a u v : Carrier, (reset (reset (reset u a) (reset v a)) r) = (reset (reset (reset (reset u a) r) r) (reset (reset (reset v a) r) r)) := by decide

private theorem law_reset_split : ∀ a u v : Carrier, (reset u (reset v a)) = (reset (reset u a) (reset v a)) := by decide

private theorem law_root_preserve : ∀ r u v : Carrier, (reset (reset u (reset v r)) r) = (reset u (reset v r)) := by decide

private theorem law_F_closed : ∀ r a b u : Carrier, (reset (guarded r (reset (reset u r) a) b) r) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_F_join : ∀ r a b u v : Carrier, (guarded r (reset (reset (reset (reset u r) r) (reset (reset v r) r)) a) b) = (reset (reset (guarded r (reset (reset u r) a) b) r) (reset (guarded r (reset (reset v r) a) b) r)) := by decide

private theorem law_F_contract : ∀ r a b u : Carrier, (reset (reset (guarded r (reset (reset u r) a) b) r) (reset (reset (reset (guarded r (reset r a) b) r) (reset (reset u r) r)) r)) = (reset (reset (guarded r (reset r a) b) r) (reset (reset u r) r)) := by decide

private theorem law_F_idem : ∀ r a b u : Carrier, (guarded r (reset (guarded r (reset (reset u r) a) b) a) b) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_F_Ga : ∀ r a b u : Carrier, (guarded r (reset (reset (reset (reset u r) a) r) a) b) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_F_Ka : ∀ r a b u : Carrier, (guarded r (reset (guarded r (reset u r) a) a) b) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_F_Kb : ∀ r a b u : Carrier, (guarded r (reset (guarded r (reset u r) b) a) b) = (guarded r (reset (reset u r) a) b) := by decide

private theorem law_F_ca : ∀ r a b : Carrier, (guarded r (reset (reset a r) a) b) = (guarded r (reset r a) b) := by decide

private theorem law_F_cb : ∀ r a b : Carrier, (guarded r (reset (reset b r) a) b) = (guarded r (reset r a) b) := by decide

private theorem law_capture : ∀ r a b u : Carrier, (reset (reset (guarded r (guarded r (reset (reset u r) a) b) b) a) r) = (reset (reset (guarded r (reset u r) b) a) r) := by decide

private theorem law_weak_gate : ∀ r a b u : Carrier, (reset (reset (guarded r (reset (reset u r) a) b) a) r) = (reset (reset (guarded r (reset u r) b) a) r) := by decide

private theorem law_terminal : ∀ r a b : Carrier, (guarded r (guarded r a b) b) = (guarded r (reset a r) b) := by decide

private theorem law_terminal_bound : ∀ r a b : Carrier, (reset (reset (guarded r a b) r) (reset (reset (reset (reset a r) r) (reset (reset b r) r)) r)) = (reset (reset (reset a r) r) (reset (reset b r) r)) := by decide

private theorem law_terminal_weak : ∀ r a b : Carrier, (reset (reset (guarded r a b) r) (reset (guarded r (reset a r) b) r)) = (guarded r (reset a r) b) := by decide

private theorem law_G_def : ∀ r a u : Carrier, (reset (reset (reset u r) a) r) = (guarded r (reset (reset u r) a) a) := by decide

private theorem law_K_def : ∀ r a u : Carrier, (guarded r (reset u r) a) = (guarded r (reset (reset u r) r) a) := by decide

private theorem law_G_root : ∀ r u : Carrier, (reset (reset (reset u r) r) r) = (reset u r) := by decide

private theorem law_K_root : ∀ r u : Carrier, (guarded r (reset u r) r) = (reset u r) := by decide

/-- The only failures of the action-band law use all five indispensable values. -/
private theorem band_iff (r a b c d u : Carrier) :
    guarded r (reset (guarded r (reset (guarded r (reset (reset u r) a) b) c) d) a) b =
      guarded r (reset (guarded r (reset (reset u r) c) d) a) b ↔
    ¬ (r = .root ∧ a = .root ∧ b = .block ∧
        ((c = .left ∧ d = .right) ∨ (c = .right ∧ d = .left)) ∧ u = .input) := by
  cases r <;> revert a b c d u <;> decide

/-- Each local model satisfies all thirty-six equations, hence every identity
of Four. The finite checks above concern complete laws, not bounded-depth terms. -/
theorem local_laws (e : Fin 5) :
    FiniteBasis.Laws (FiniteBasis.resetOperation (Local e)) (FiniteBasis.guardedOperation (Local e)) where
  R1 r := Subtype.ext (law_R1 (r).val)
  R2 r a := Subtype.ext (law_R2 (r).val (a).val)
  R3 r a := Subtype.ext (law_R3 (r).val (a).val)
  R4 r a b := Subtype.ext (law_R4 (r).val (a).val (b).val)
  R5 r a b := Subtype.ext (law_R5 (r).val (a).val (b).val)
  R6 r a b := Subtype.ext (law_R6 (r).val (a).val (b).val)
  h_sym r a b := Subtype.ext (law_h_sym (r).val (a).val (b).val)
  h_minor r a := Subtype.ext (law_h_minor (r).val (a).val)
  h_root r a b := Subtype.ext (law_h_root (r).val (a).val (b).val)
  h_expand r a b u := Subtype.ext (law_h_expand (r).val (a).val (b).val (u).val)
  h_split r a b u v := Subtype.ext (law_h_split (r).val (a).val (b).val (u).val (v).val)
  h_back r a b u := Subtype.ext (law_h_back (r).val (a).val (b).val (u).val)
  h_reroot r a b u := Subtype.ext (law_h_reroot (r).val (a).val (b).val (u).val)
  h_insert r a b := Subtype.ext (law_h_insert (r).val (a).val (b).val)
  project_join r a u v := Subtype.ext (law_project_join (r).val (a).val (u).val (v).val)
  reset_split a u v := Subtype.ext (law_reset_split (a).val (u).val (v).val)
  root_preserve r u v := Subtype.ext (law_root_preserve (r).val (u).val (v).val)
  F_closed r a b u := Subtype.ext (law_F_closed (r).val (a).val (b).val (u).val)
  F_join r a b u v := Subtype.ext (law_F_join (r).val (a).val (b).val (u).val (v).val)
  F_contract r a b u := Subtype.ext (law_F_contract (r).val (a).val (b).val (u).val)
  F_idem r a b u := Subtype.ext (law_F_idem (r).val (a).val (b).val (u).val)
  F_band r a b c d u := by
    apply Subtype.ext
    change guarded r.val (reset (guarded r.val (reset (guarded r.val (reset (reset u.val r.val) a.val) b.val) c.val) d.val) a.val) b.val =
      guarded r.val (reset (guarded r.val (reset (reset u.val r.val) c.val) d.val) a.val) b.val
    apply (band_iff _ _ _ _ _ _).mpr
    rintro ⟨hr, _, hb, hcd, hu⟩
    have hnr := r.property
    have hnb := b.property
    have hnc := c.property
    have hnd := d.property
    have hnu := u.property
    have he := (show ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 from by decide) e
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> simp_all [excluded]
  F_Ga r a b u := Subtype.ext (law_F_Ga (r).val (a).val (b).val (u).val)
  F_Ka r a b u := Subtype.ext (law_F_Ka (r).val (a).val (b).val (u).val)
  F_Kb r a b u := Subtype.ext (law_F_Kb (r).val (a).val (b).val (u).val)
  F_ca r a b := Subtype.ext (law_F_ca (r).val (a).val (b).val)
  F_cb r a b := Subtype.ext (law_F_cb (r).val (a).val (b).val)
  capture r a b u := Subtype.ext (law_capture (r).val (a).val (b).val (u).val)
  weak_gate r a b u := Subtype.ext (law_weak_gate (r).val (a).val (b).val (u).val)
  terminal r a b := Subtype.ext (law_terminal (r).val (a).val (b).val)
  terminal_bound r a b := Subtype.ext (law_terminal_bound (r).val (a).val (b).val)
  terminal_weak r a b := Subtype.ext (law_terminal_weak (r).val (a).val (b).val)
  G_def r a u := Subtype.ext (law_G_def (r).val (a).val (u).val)
  K_def r a u := Subtype.ext (law_K_def (r).val (a).val (u).val)
  G_root r u := Subtype.ext (law_G_root (r).val (u).val)
  K_root r u := Subtype.ext (law_K_root (r).val (u).val)

/-- Forgetting the omitted-value subtype commutes with every native term. -/
theorem realize_local {Var : Type*} (e : Fin 5) (t : Term Unit Var) (v : Var → Local e) :
    (t.realize v).val = t.realize (fun j => (v j).val) := by
  induction t using Term.induction_owner with
  | var => rfl
  | step s t hs ht =>
    change reset (s.realize v).val (t.realize v).val =
      reset (s.realize (fun j => (v j).val)) (t.realize (fun j => (v j).val))
    rw [hs, ht]
  | guarded a x y z hx hy hz =>
    cases a
    change guarded (x.realize v).val (y.realize v).val (z.realize v).val =
      guarded (x.realize (fun j => (v j).val)) (y.realize (fun j => (v j).val))
        (z.realize (fun j => (v j).val))
    rw [hx, hy, hz]

/-- Every identity supported on at most four variables holds, regardless of
padded arity or term depth. The proof uses full local completeness. -/
theorem holds_of_variableCount_le (e : Equational.Identity (Symbol Unit))
    (hn : e.variableCount ≤ 4) (hvalid : letI := fourStructure (Role := Unit); e.Holds Four) :
    e.Holds Carrier := by
  classical
  intro v
  let X := e.support.image v
  have hX : X.card ≤ 4 := Finset.card_image_le.trans hn
  have hmissing : ∃ i : Fin 5, excluded i ∉ X := by
    by_contra! h
    have hc := Finset.card_le_card
      (show Finset.univ.image excluded ⊆ X from by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact h i)
    have hcard : (Finset.univ.image excluded).card = 5 := by decide
    rw [hcard] at hc
    omega
  obtain ⟨i, hi⟩ := hmissing
  have hjoin := (show ∀ j : Fin 5, Carrier.join ≠ excluded j from by decide) i
  let w : Fin e.arity → Local i := fun j =>
    if hj : j ∈ e.support then ⟨v j, fun he => hi (he ▸ Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
    else ⟨.join, hjoin⟩
  have heq : e.lhs.realize w = e.rhs.realize w :=
    (local_laws i).equal_of_four e.lhs e.rhs hvalid w
  have hvalues : ∀ j ∈ e.support, (w j).val = v j := by
    intro j hj
    simp only [w, hj, dite_true]
  calc
    e.lhs.realize v = e.lhs.realize (fun j => (w j).val) :=
      Equational.realize_eq_of_eqOn e.lhs v _
        (fun j hj => (hvalues j (Finset.mem_union_left _ hj)).symm)
    _ = (e.lhs.realize w).val := (realize_local i e.lhs w).symm
    _ = (e.rhs.realize w).val := congrArg Subtype.val heq
    _ = e.rhs.realize (fun j => (w j).val) := realize_local i e.rhs w
    _ = e.rhs.realize v := Equational.realize_eq_of_eqOn e.rhs _ v
      (fun j hj => hvalues j (Finset.mem_union_right _ hj))

theorem actionBand_holds : letI := fourStructure (Role := Unit); actionBand.Holds Four := by
  intro v
  change Fin 5 → Four at v
  change Four.guarded (v 0)
      (Four.guarded (v 0) (Four.reset (Four.guarded (v 0) (Four.reset (v 4) (v 0)) (v 1)) (v 2)) (v 3)) (v 1) =
    Four.guarded (v 0) (Four.guarded (v 0) (Four.reset (Four.reset (v 4) (v 0)) (v 2)) (v 3)) (v 1)
  generalize v 0 = r
  generalize v 1 = b
  generalize v 2 = c
  generalize v 3 = d
  generalize v 4 = u
  cases r <;> cases b <;> cases c <;> cases d <;> cases u <;> rfl

theorem actionBand_fails : ¬actionBand.Holds Carrier := by
  intro h
  have hh := h ![.root, .block, .left, .right, .input]
  have hn : Carrier.root ≠ .join := by decide
  exact hn hh

/-- No basis, even infinite, can use only four distinct variables per axiom. -/
theorem not_hasVariableBound_four (T : Equational.Theory (Symbol Unit))
    (hbasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four T) :
    ¬Equational.HasVariableBound T 4 := by
  let _ := fourStructure (Role := Unit)
  intro hbound
  have hmodels : Equational.Models T Carrier :=
    fun e he => holds_of_variableCount_le e (hbound e he) (hbasis.models e he)
  exact actionBand_fails (((hbasis actionBand).mp actionBand_holds).sound Carrier hmodels)

/-- Every basis of the one-owner theory has variable bound at least five. -/
theorem variableBound_ge_five (T : Equational.Theory (Symbol Unit)) (n : ℕ)
    (hbasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four T)
    (hbound : Equational.HasVariableBound T n) : 5 ≤ n := by
  by_contra hn
  apply not_hasVariableBound_four T hbasis
  exact fun e he => (hbound e he).trans (by omega)

/-- The lower bound applies to the intended winner-set algebra for every K ≥ 3. -/
theorem variableBound_ge_five_winnerSet {Role : Type*} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) (T : Equational.Theory (Symbol Unit)) (n : ℕ)
    (hbasis : letI := oneOwnerStructure owner; Equational.IsBasis (WinnerSet Role) T)
    (hbound : Equational.HasVariableBound T n) : 5 ≤ n := by
  apply variableBound_ge_five T n _ hbound
  intro e
  exact (FiniteBasis.winnerSet_holds_iff_four three owner observer ho e).symm.trans (hbasis e)

end KFOL.Owner.FourVariableObstruction
