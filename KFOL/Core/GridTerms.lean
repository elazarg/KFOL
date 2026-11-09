module

public import KFOL.Core.GridRows
public import KFOL.Core.Folds

/-! # Padded row and column fold terms -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

/-- A private row variable pads the h-fold of a row of cells. -/
def fTerm {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) :
    Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) :=
  foldTerm (three 2) ((List.finRange s).map (fun j => .var (some (cell i j)))) (.var (some (row i)))

/-- A private column variable pads the h-fold of a column of cells. -/
def gTerm {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s) :
    Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) :=
  foldTerm (three 2) ((List.finRange r).map (fun i => .var (some (cell i j)))) (.var (some (col j)))

/-- An f-fold of all padded rows; repeating the supplied row as final
argument avoids an empty-fold convention or an additional constant. -/
def tTerm {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) :
    Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) :=
  foldTerm (three 0) ((List.finRange r).map (fTerm three)) (fTerm three i)

/-- The analogous g-fold of all padded columns. -/
def sTerm {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s) :
    Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) :=
  foldTerm (three 1) ((List.finRange s).map (gTerm three)) (gTerm three j)

theorem fTerm_atom {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (b : Role)
    (hb : three 2 ≠ b) (v : Option (Variable r s) → Native Role) :
    (fTerm three i).realize v = Native.atom b ↔ ∀ x ∈ fBlock i, v x = Native.atom b := by
  rw [fTerm, realize_fold_atom_other _ _ hb]
  simp only [FirstOrder.Language.Term.realize_var, List.forall_mem_map, List.mem_finRange,
    forall_const]
  constructor
  · rintro ⟨hrow,hcells⟩ x hx
    obtain ⟨a,rfl⟩ := exists_fMarker i x hx
    cases a with
    | none => exact hrow
    | some j => exact hcells j
  · intro h
    exact ⟨h _ (by simp), fun j => h _ (by simp)⟩

theorem gTerm_atom {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s) (b : Role)
    (hb : three 2 ≠ b) (v : Option (Variable r s) → Native Role) :
    (gTerm three j).realize v = Native.atom b ↔ ∀ x ∈ gBlock j, v x = Native.atom b := by
  rw [gTerm, realize_fold_atom_other _ _ hb]
  simp only [FirstOrder.Language.Term.realize_var, List.forall_mem_map, List.mem_finRange,
    forall_const]
  constructor
  · rintro ⟨hcol,hcells⟩ x hx
    obtain ⟨a,rfl⟩ := exists_gMarker j x hx
    cases a with
    | none => exact hcol
    | some i => exact hcells i
  · intro h
    exact ⟨h _ (by simp), fun i => h _ (by simp)⟩

theorem tTerm_atom {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (v : Option (Variable r s) → Native Role) :
    (tTerm three i).realize v = Native.atom (three 0) ↔
      ∃ k : Fin r, ∀ x ∈ fBlock k, v x = Native.atom (three 0) := by
  rw [tTerm, realize_fold_atom_owner]
  have hne := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  constructor
  · rintro (h | ⟨term, hmem, h⟩)
    · exact ⟨i, (fTerm_atom three i _ hne v).mp h⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
      exact ⟨k, (fTerm_atom three k _ hne v).mp h⟩
  · rintro ⟨k,hk⟩
    exact Or.inr ⟨fTerm three k, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩,
      (fTerm_atom three k _ hne v).mpr hk⟩

theorem sTerm_atom {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (v : Option (Variable r s) → Native Role) :
    (sTerm three j).realize v = Native.atom (three 1) ↔
      ∃ l : Fin s, ∀ x ∈ gBlock l, v x = Native.atom (three 1) := by
  rw [sTerm, realize_fold_atom_owner]
  have hne := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  constructor
  · rintro (h | ⟨term, hmem, h⟩)
    · exact ⟨j, (gTerm_atom three j _ hne v).mp h⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
      exact ⟨k, (gTerm_atom three k _ hne v).mp h⟩
  · rintro ⟨k,hk⟩
    exact Or.inr ⟨gTerm three k, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩,
      (gTerm_atom three k _ hne v).mpr hk⟩

/-- The padded crossing identity: its two arms cannot collapse together. -/
theorem terms_cannot_cross {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s)
    (v : Option (Variable r s) → Native Role) :
    ¬ ((tTerm three i).realize v = Native.atom (three 0) ∧
      (sTerm three j).realize v = Native.atom (three 1)) := by
  rintro ⟨hT,hS⟩
  obtain ⟨k,hk⟩ := (tTerm_atom three i v).mp hT
  obtain ⟨l,hl⟩ := (sTerm_atom three j v).mp hS
  have he := (hk (some (cell k l)) (by simp)).symm.trans (hl (some (cell k l)) (by simp))
  exact three.injective.ne (show (0 : Fin 3) ≠ 1 by decide) (Native.atom.inj he)

end KFOL.Core.Grid
