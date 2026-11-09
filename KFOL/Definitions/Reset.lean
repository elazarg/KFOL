module

public import KFOL.Definitions.Equational
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Finset.Sort

/-! # Reset values, signature, selection and canonical guard tables

Reset uses the shared nonempty winner-set carrier and mathlib's generic term
syntax. The guard table is the minimal part of a finite structural collection;
validity is still defined independently by algebraic evaluation.
-/

@[expose] public section

namespace KFOL

universe u v w

/-- An atomic right operand discards the left; an ambiguous one keeps both. -/
noncomputable def WinnerSet.reset {Role : Type u} (A B : WinnerSet Role) : WinnerSet Role := by
  classical
  exact if B.Ambiguous then A.union B else B

namespace Reset

/-- Reset is one binary operation, without constants or extra owned operations. -/
inductive Symbol : ℕ → Type
  | reset : Symbol 2

/-- Reset terms reuse the relation-free mathlib term type. -/
abbrev Term (Var : Type v) := Equational.Term Symbol Var

/-- Interpret the single binary symbol by an explicitly supplied operation. -/
@[instance_reducible] def structureOf {M : Type u} (op : M → M → M) :
    (Equational.language Symbol).Structure M where
  funMap f args := match f with
    | .reset => op (args 0) (args 1)
  RelMap r := nomatch r

/-- The fixed separating chain Z={a}, U={a,b}, T={a,b,c}. -/
def chainValue {Role : Type u} (three : Fin 3 ↪ Role) (i : Fin 3) : WinnerSet Role :=
  if i = 0 then WinnerSet.singleton (three 0)
  else if i = 1 then (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))
  else (WinnerSet.singleton (three 2)).union
    ((WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)))

namespace Term

variable {Var : Type v} {Role : Type u}

/-- Ergonomic binary constructor on the generic syntax. -/
def step (s t : Term Var) : Term Var :=
  .func .reset (fun i => if i = 0 then s else t)

/-- The rightmost variable, independently of evaluation and selection. -/
def root : Term Var → Var
  | .var x => x
  | .func .reset args => root (args 1)

/-- A position is selected according to the ambiguity statuses of inputs. -/
def Selected : Term Var → Set Var → Var → Prop
  | .var i, _, j => j = i
  | .func .reset args, B, j =>
    Selected (args 1) B j ∨ (root (args 1) ∈ B ∧ Selected (args 0) B j)

/-- Evaluation uses mathlib realization with the shared reset operation. -/
noncomputable def eval (t : Term Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf (WinnerSet.reset (Role := Role))
  t.realize v

/-- Raw prerequisites collected from the syntax, before antichain minimization. -/
def guards [DecidableEq Var] : Term Var → Var → Finset (Finset Var)
  | .var i, j => if j = i then {∅} else ∅
  | .func .reset args, j =>
    guards (args 1) j ∪ (guards (args 0) j).image (insert (root (args 1)))

/-- Delete every prerequisite having a strictly smaller prerequisite. -/
def minimize [DecidableEq Var] (G : Finset (Finset Var)) : Finset (Finset Var) :=
  G.filter (fun A => ∀ B ∈ G, B ⊆ A → A ⊆ B)

/-- The canonical table for one output position. Unused positions have no guards. -/
def table [DecidableEq Var] (t : Term Var) (j : Var) : Finset (Finset Var) :=
  minimize (t.guards j)

/-- Finite guard composition: outer prerequisites refer to inner roots; inner
prerequisites supply the final output position. Minimize after taking unions. -/
def composedGuards {Var' : Type w} [DecidableEq Var] [DecidableEq Var']
    (t : Term Var) (s : Var → Term Var') (j : Var') : Finset (Finset Var') :=
  t.varFinset.biUnion (fun i => (t.table i).biUnion (fun A =>
    ((s i).table j).image (fun C => A.image (fun k => (s k).root) ∪ C)))

end Term
/-- The six reset laws, independently imposed on an arbitrary binary algebra. -/
structure Laws {M : Type u} (op : M → M → M) : Prop where
  idem : ∀ x, op x x = x
  absorb : ∀ x y, op (op x y) x = op y x
  repeat_right : ∀ x y, op (op x y) y = op x y
  nested : ∀ x y z, op x (op (op x y) z) = op x (op y z)
  exchange : ∀ x y z, op (op (op x y) z) y = op (op x z) y
  left_comm : ∀ x y z, op x (op y z) = op y (op x z)

/-- The binary operation of an arbitrary structure in exactly the reset signature. -/
def operation (M : Type u) [(Equational.language Symbol).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .reset
    (fun i => if i = 0 then x else y)

/-- R1--R6 as actual finite-arity equations, in their paper order. Unused
variable declarations in the first three equations do not affect support. -/
def basisAxiom (i : Fin 6) : Equational.Identity Symbol :=
  let x : Term (Fin 3) := .var 0
  let y : Term (Fin 3) := .var 1
  let z : Term (Fin 3) := .var 2
  if i = 0 then ⟨3, Term.step x x, x⟩
  else if i = 1 then ⟨3, Term.step (Term.step x y) x, Term.step y x⟩
  else if i = 2 then ⟨3, Term.step (Term.step x y) y, Term.step x y⟩
  else if i = 3 then
    ⟨3, Term.step x (Term.step (Term.step x y) z), Term.step x (Term.step y z)⟩
  else if i = 4 then
    ⟨3, Term.step (Term.step (Term.step x y) z) y, Term.step (Term.step x z) y⟩
  else ⟨3, Term.step x (Term.step y z), Term.step y (Term.step x z)⟩

/-- Exactly the displayed family of six equations, independent of its consequences. -/
def basis : Equational.Theory Symbol := Set.range basisAxiom

/-- A finite antimatroid with exactly one feasible singleton. The ground is
explicit, so unused ambient variables are not silently added to the support. -/
structure RootedAntimatroid (Var : Type v) [DecidableEq Var] where
  ground : Finset Var
  feasible : Set (Finset Var)
  root : Var
  empty_mem : ∅ ∈ feasible
  ground_mem : ground ∈ feasible
  subset_ground : ∀ A ∈ feasible, A ⊆ ground
  union_mem : ∀ A ∈ feasible, ∀ B ∈ feasible, A ∪ B ∈ feasible
  accessible : ∀ A ∈ feasible, A.Nonempty → ∃ a ∈ A, A.erase a ∈ feasible
  root_mem : {root} ∈ feasible
  singleton_unique : ∀ a, {a} ∈ feasible → a = root

/-- Readiness uses only feasible sets: j can be reached using positions in B
and possibly j itself. It is independent of terms and their selectors. -/
def RootedAntimatroid.Ready {Var : Type v} [DecidableEq Var]
    (F : RootedAntimatroid Var) (B : Set Var) (j : Var) : Prop :=
  ∃ A ∈ F.feasible, j ∈ A ∧ (A : Set Var) ⊆ insert j B

/-- The feasible-family operation corresponding to one reset node. -/
def familyProduct {Var : Type v} [DecidableEq Var]
    (F G : Set (Finset Var)) : Set (Finset Var) :=
  {D | D = ∅ ∨ ∃ A ∈ F, ∃ C ∈ G, C.Nonempty ∧ D = A ∪ C}

/-- Actual semantic term functions, independently of antimatroids or tables. -/
abbrev TermFunction (Role : Type u) (Var : Type v) :=
  {f : (Var → WinnerSet Role) → WinnerSet Role //
    ∃ t : Term Var, ∀ valuation, f valuation = t.eval valuation}

/-- The paper's feasible sets on the actual syntactic support of a term. -/
def Term.feasible {Var : Type v} [DecidableEq Var] (t : Term Var) : Set (Finset Var) :=
  {A | A ⊆ t.varFinset ∧ ∀ j ∈ A, t.Selected (A : Set Var) j}

/-- Candidate guard data, independent of realizability by a term. -/
structure GuardTable (Var : Type v) where
  root : Var
  guards : Var → Finset (Finset Var)

/-- A prerequisite enables an output on a set of ambiguity statuses. -/
def GuardTable.Enabled {Var : Type v} (G : GuardTable Var) (B : Set Var) (j : Var) : Prop :=
  ∃ A ∈ G.guards j, (A : Set Var) ⊆ B

/-- Constructibility is a finite sequence of fresh enabled additions. It does
not refer to terms, antimatroid feasibility or a recognition algorithm. -/
inductive GuardTable.Constructible {Var : Type v} [DecidableEq Var]
    (G : GuardTable Var) : Finset Var → Prop
  | empty : Constructible G ∅
  | insert {A : Finset Var} (j : Var) (hA : Constructible G A)
      (fresh : j ∉ A) (enabled : G.Enabled (A : Set Var) j) :
      Constructible G (insert j A)

/-- A candidate is already minimal at each output position. -/
def GuardTable.IsAntichain {Var : Type v} [DecidableEq Var] (G : GuardTable Var) : Prop :=
  ∀ j, ∀ A ∈ G.guards j, ∀ B ∈ G.guards j, A ⊆ B → A = B

/-- Number of explicitly listed distinct prerequisites over a finite input set. -/
def GuardTable.entryCount {Var : Type v} [Fintype Var] (G : GuardTable Var) : ℕ :=
  ∑ j, (G.guards j).card

/-- The three realizability conditions, with minimality of the input tables
explicit. The paper-facing statement repeats every clause. -/
def GuardTable.WellFormed {Var : Type v} [DecidableEq Var] (G : GuardTable Var) : Prop :=
  G.IsAntichain ∧ G.guards G.root = {∅} ∧
    (∀ j, ∅ ∈ G.guards j → j = G.root) ∧
    (∀ j, ∀ A ∈ G.guards j, j ∉ A) ∧
    (∀ j, ∀ A ∈ G.guards j, G.Constructible A)

/-- The canonical guard data of a term, using its independently defined root. -/
def Term.guardTable {Var : Type v} [DecidableEq Var] (t : Term Var) : GuardTable Var :=
  ⟨t.root, t.table⟩

/-- One parallel greedy round: add every target position already enabled by
an explicit prerequisite in the reached finite set. -/
def GuardTable.advance {Var : Type v} [DecidableEq Var] (G : GuardTable Var)
    (target reached : Finset Var) : Finset Var :=
  reached ∪ target.filter (fun j => ∃ A ∈ G.guards j, A ⊆ reached)

/-- Run the greedy closure for a fixed number of rounds. -/
def GuardTable.reached {Var : Type v} [DecidableEq Var] (G : GuardTable Var)
    (target : Finset Var) : ℕ → Finset Var
  | 0 => ∅
  | k + 1 => G.advance target (G.reached target k)

/-- Constructibility recognition uses exactly as many rounds as target labels. -/
def GuardTable.constructibleCheck {Var : Type v} [DecidableEq Var]
    (G : GuardTable Var) (target : Finset Var) : Bool :=
  decide (G.reached target target.card = target)

/-- Scan only listed prerequisites for self-dependency, failed construction,
or a strictly larger listed guard. This avoids enumerating arbitrary subsets. -/
def GuardTable.badGuards {Var : Type v} [DecidableEq Var] (G : GuardTable Var)
    (j : Var) : Finset (Finset Var) :=
  (G.guards j).filter (fun A => j ∈ A ∨ G.constructibleCheck A = false ∨
    ∃ B ∈ G.guards j, A ⊆ B ∧ A ≠ B)

/-- Executable recognition scans the finite input set and the supplied guards. -/
def GuardTable.check {Var : Type v} [DecidableEq Var] [Fintype Var]
    (G : GuardTable Var) : Bool :=
  decide (G.guards G.root = {∅} ∧
    (Finset.univ.filter (fun j => (∅ ∈ G.guards j ∧ j ≠ G.root) ∨
      G.badGuards j ≠ ∅)) = ∅)

/-- Primitive reset syntax size counts all variable and operation occurrences,
including independent repeated copies. It is not a machine-time bound. -/
def Term.size {Var : Type v} : Term Var → ℕ
  | .var _ => 1
  | .func .reset args => 1 + size (args 0) + size (args 1)

/-- A left-associated path with the specified final variable. -/
def Term.pathTerm {Var : Type v} (r : Var) : List Var → Term Var
  | [] => .var r
  | x :: xs => Term.step (xs.foldl (fun t i => Term.step t (.var i)) (.var x)) (.var r)

/-- Join common-root terms, with the root projection as the empty join. -/
def Term.joinPaths {Var : Type v} (r : Var) (ts : List (Term Var)) : Term Var :=
  ts.foldr Term.step (.var r)

/-- Fresh target positions enabled by the current root-first order. -/
def GuardTable.greedyCandidates {Var : Type v} [DecidableEq Var]
    (G : GuardTable Var) (target : Finset Var) (xs : List Var) : Finset Var :=
  (target \ insert G.root xs.toFinset).filter
    (fun j => ∃ A ∈ G.guards j, A ⊆ insert G.root xs.toFinset)

/-- The tail of a root-first greedy order. At each step choose the least
fresh enabled position, stopping when no such position exists. -/
def GuardTable.greedyOrder {Var : Type v} [LinearOrder Var]
    (G : GuardTable Var) (target : Finset Var) : ℕ → List Var
  | 0 => []
  | k + 1 =>
    let xs := G.greedyOrder target k
    let C := G.greedyCandidates target xs
    if h : C.Nonempty then xs ++ [C.min' h] else xs

/-- Construct a path using at most one greedy addition per target position. -/
def GuardTable.greedyPath {Var : Type v} [LinearOrder Var]
    (G : GuardTable Var) (target : Finset Var) : Term Var :=
  Term.pathTerm G.root (G.greedyOrder target target.card).reverse

/-- A computable listing of the supplied guards in colexicographic order.
This sorts only the explicit input, without enumerating other subsets. -/
def GuardTable.guardList {Var : Type v} [LinearOrder Var]
    (G : GuardTable Var) (j : Var) : List (Finset Var) :=
  ((G.guards j).map toColex.toEmbedding).sort.map ofColex

/-- Exactly one greedy path per explicitly listed prerequisite. -/
def GuardTable.synthesisPaths {Var : Type v} [LinearOrder Var] [Fintype Var]
    (G : GuardTable Var) : List (Term Var) :=
  Finset.univ.sort.flatMap (fun j => (G.guardList j).map
    (fun A => G.greedyPath (insert j A)))

/-- Executable synthesis either rejects the candidate or returns an actual
primitive reset term. All ordering assumptions are local to the algorithm. -/
def GuardTable.synthesize {Var : Type v} [LinearOrder Var] [Fintype Var]
    (G : GuardTable Var) : Option (Term Var) :=
  if G.check then some (Term.joinPaths G.root G.synthesisPaths) else none

end Reset
end KFOL
