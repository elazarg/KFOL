module

public import KFOL.Definitions.Core

/-! # A two-way navigational query language and valuation documents

Paths denote binary relations and tests denote unary predicates, independently
of winner-set evaluation. Only child/parent, union, composition and filtering
are used. Negation is restricted to fixed role labels, never input predicates.
-/

@[expose] public section
namespace KFOL.Query
universe u v w

mutual
  inductive Path (Role : Type u) (Var : Type v) where
    | child | parent
    | union (left right : Path Role Var)
    | comp (left right : Path Role Var)
    | filter (path : Path Role Var) (test : Test Role Var)
  inductive Test (Role : Type u) (Var : Type v) where
    | truth | falsity
    | role (r : Role) | notRole (r : Role) | mark (j : Var)
    | and (left right : Test Role Var)
    | or (left right : Test Role Var)
    | exists (path : Path Role Var)
end

/-- A labelled navigation structure; no game semantics enters this interface. -/
structure Document (Role : Type u) (Var : Type v) (Node : Type w) where
  child : Node → Node → Prop
  role : Role → Node → Prop
  mark : Var → Node → Prop

mutual
  def Path.Holds {Role : Type u} {Var : Type v} {Node : Type w}
      (document : Document Role Var Node) : Path Role Var → Node → Node → Prop
    | .child, x, y => document.child x y
    | .parent, x, y => document.child y x
    | .union p q, x, y => p.Holds document x y ∨ q.Holds document x y
    | .comp p q, x, y => ∃ z, p.Holds document x z ∧ q.Holds document z y
    | .filter p test, x, y => p.Holds document x y ∧ test.Holds document y
  def Test.Holds {Role : Type u} {Var : Type v} {Node : Type w}
      (document : Document Role Var Node) : Test Role Var → Node → Prop
    | .truth, _ => True
    | .falsity, _ => False
    | .role r, x => document.role r x
    | .notRole r, x => ¬document.role r x
    | .mark j, x => document.mark j x
    | .and p q, x => p.Holds document x ∧ q.Holds document x
    | .or p q, x => p.Holds document x ∨ q.Holds document x
    | .exists p, x => ∃ y, p.Holds document x y
end

mutual
  def Path.size {Role : Type u} {Var : Type v} : Path Role Var → ℕ
    | .child | .parent => 1
    | .union p q | .comp p q => 1 + p.size + q.size
    | .filter p test => 1 + p.size + test.size
  def Test.size {Role : Type u} {Var : Type v} : Test Role Var → ℕ
    | .truth | .falsity | .role _ | .notRole _ | .mark _ => 1
    | .and p q | .or p q => 1 + p.size + q.size
    | .exists p => 1 + p.size
end

/-- The document has one role node for each role, and a j-labelled leaf below
role r precisely when the j-th input contains r. Every node is reachable. -/
inductive Node {Role : Type u} {Var : Type v} (valuation : Var → WinnerSet Role) where
  | root
  | role (r : Role)
  | mark (r : Role) (j : Var) (present : r ∈ (valuation j).val)

def document {Role : Type u} {Var : Type v} (valuation : Var → WinnerSet Role) :
    Document Role Var (Node valuation) where
  child x y := match x, y with
    | .root, .role _ => True
    | .role r, .mark s _ _ => r = s
    | _, _ => False
  role r x := x = .role r
  mark j x := match x with
    | .mark _ k _ => j = k
    | _ => False

def input {Role : Type u} {Var : Type v} (j : Var) : Path Role Var :=
  .filter .child (.exists (.filter .child (.mark j)))

/-- Linear-size existence of a winner other than r. Public syntax is required
explicitly; there is no arbitrary definition for excluded role switches. -/
def nonOwner {Role : Type u} {Var : Type v} [DecidableEq Role] (r : Role) :
    (t : Term Role Var) → t.IsPublic → Test Role Var
  | .winner a, _ => if a = r then .falsity else .truth
  | .var j, _ => .exists (.filter (input j) (.notRole r))
  | .choice a s t, h =>
      if a = r then .and (nonOwner r s h.1) (nonOwner r t h.2)
      else .or (nonOwner r s h.1) (nonOwner r t h.2)
  | .rename _ _, h => False.elim h

/-- The parent test returns from an output role to the common document root.
Each compiled child occurs once, avoiding exponential query expansion. -/
def compile {Role : Type u} {Var : Type v} [DecidableEq Role] :
    (t : Term Role Var) → t.IsPublic → Path Role Var
  | .winner r, _ => .filter .child (.role r)
  | .var j, _ => input j
  | .choice r s t, h =>
      .filter (.union (compile s h.1) (compile t h.2))
        (.or (.role r) (.exists (.filter .parent
          (.and (nonOwner r s h.1) (nonOwner r t h.2)))))
  | .rename _ _, h => False.elim h

/-- The regular relation for one owned operation. The fresh point `none`
observes A itself; an ordinary role x observes A ⋆_r {x}. No edge returns to
the fresh point. Composition here will be ordinary relational composition. -/
noncomputable def relation {Role : Type u} (owner : Role) (A : WinnerSet Role) :
    Option Role → Option Role → Prop := fun x y =>
  match y with
  | none => False
  | some y => match x with
    | none => y ∈ A.val
    | some x => y ∈ (WinnerSet.choice owner A (WinnerSet.singleton x)).val

end KFOL.Query
