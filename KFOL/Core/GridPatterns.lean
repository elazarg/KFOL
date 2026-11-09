module

public import KFOL.Core.GridFoldValues

/-! # The two nontrivial ideal patterns are actual padded fold values -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- At every F-row the outer f-fold absorbs all other entries through
its alpha block. -/
theorem tTerm_fRow {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s)) :
    (tTerm three i).realize (rawValue three (.inl (p,a))) = Native.atom (three 0) := by
  apply (tTerm_atom three i _).mpr
  exact ⟨p.val.2,fun x hx => (fRow_atom three p a x).mpr hx⟩

theorem sTerm_gRow {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r)) :
    (sTerm three j).realize (rawValue three (.inr (.inl (p,a)))) = Native.atom (three 1) := by
  apply (sTerm_atom three j _).mpr
  exact ⟨p.val.2,fun x hx => (gRow_atom three p a x).mpr hx⟩

/-- No upper marker survives the complete padded T term. -/
theorem tTerm_no_upper {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (c : Coordinate r s) :
    (tTerm three i).realize (rawValue three c) ≠ Native.upper := by
  rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨k,l⟩)
  · rw [tTerm_fRow]
    simp
  · intro h
    obtain ⟨hmarker,_,_⟩ := (realize_fold_upper (three 0) _ _ _).mp h
    rcases hmarker with hbase | ⟨term,hmem,hvalue⟩
    · exact fTerm_no_upper_gRow three i p a hbase
    · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hmem
      exact fTerm_no_upper_gRow three k p a hvalue
  · intro h
    obtain ⟨hmarker,_,_⟩ := (realize_fold_upper (three 0) _ _ _).mp h
    rcases hmarker with hbase | ⟨term,hmem,hvalue⟩
    · exact fTerm_no_upper_annotation three i k l hbase
    · obtain ⟨m,_,rfl⟩ := List.mem_map.mp hmem
      exact fTerm_no_upper_annotation three m k l hvalue

theorem sTerm_no_upper {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s) (c : Coordinate r s) :
    (sTerm three j).realize (rawValue three c) ≠ Native.upper := by
  rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨k,l⟩)
  · intro h
    obtain ⟨hmarker,_,_⟩ := (realize_fold_upper (three 1) _ _ _).mp h
    rcases hmarker with hbase | ⟨term,hmem,hvalue⟩
    · exact gTerm_no_upper_fRow three j p a hbase
    · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hmem
      exact gTerm_no_upper_fRow three k p a hvalue
  · rw [sTerm_gRow]
    simp
  · intro h
    obtain ⟨hmarker,_,_⟩ := (realize_fold_upper (three 1) _ _ _).mp h
    rcases hmarker with hbase | ⟨term,hmem,hvalue⟩
    · exact gTerm_no_upper_annotation three j l k hbase
    · obtain ⟨m,_,rfl⟩ := List.mem_map.mp hmem
      exact gTerm_no_upper_annotation three m l k hvalue

/-- T is exactly the alpha-on-F-rows pattern, with lower entries elsewhere. -/
theorem tTerm_pattern {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (i : Fin r)
    (c : Coordinate r s) :
    (tTerm three i).realize (rawValue three c) = pattern three (some false) c := by
  obtain ⟨kind,hkind⟩ := pattern_of_no_upper hr hs three (tTerm three i) (tTerm_no_upper three i)
  let p : {p : Fin r × Fin r // p.1 ≠ p.2} := ⟨(i,other hr i), Ne.symm (other_ne hr i)⟩
  have he := hkind (.inl (p,none))
  rw [tTerm_fRow] at he
  cases kind with
  | none => simp [pattern] at he
  | some b => cases b with
    | false => exact hkind c
    | true => simp [pattern] at he

/-- S is exactly the beta-on-G-rows pattern. -/
theorem sTerm_pattern {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s)
    (c : Coordinate r s) :
    (sTerm three j).realize (rawValue three c) = pattern three (some true) c := by
  obtain ⟨kind,hkind⟩ := pattern_of_no_upper hr hs three (sTerm three j) (sTerm_no_upper three j)
  let p : {p : Fin s × Fin s // p.1 ≠ p.2} := ⟨(j,other hs j), Ne.symm (other_ne hs j)⟩
  have he := hkind (.inr (.inl (p,none)))
  rw [sTerm_gRow] at he
  cases kind with
  | none => simp [pattern] at he
  | some b => cases b with
    | false => simp [pattern] at he
    | true => exact hkind c

end KFOL.Core.Grid
