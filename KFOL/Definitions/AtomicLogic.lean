module

public import KFOL.Definitions.Public
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Perm.Finite

/-! # Atomic inputs and a sorted case expansion

Input variables have role sort. Winner expressions have a separate sort,
which permits ambiguous intermediate values. The independent native
semantics restricts only the inputs to singleton winner sets.
-/

@[expose] public section

namespace KFOL.AtomicLogic

universe u v w v' w'

/-- Equations of native terms, evaluated only at atomic inputs. -/
def Valid {Role : Type u} {Var : Type v} (s t : KFOL.Term Role Var) : Prop :=
  ∀ valuation : Var → Role,
    s.eval (fun x => WinnerSet.singleton (valuation x)) =
      t.eval (fun x => WinnerSet.singleton (valuation x))

/-- Role-sort terms cannot contain winner-valued expressions. -/
inductive RoleTerm (Role : Type u) (Var : Type v) where
  | var (x : Var)
  | constant (r : Role)

namespace RoleTerm

def eval {Role : Type u} {Var : Type v} (valuation : Var → Role) :
    RoleTerm Role Var → Role
  | .var x => valuation x
  | .constant r => r

def subst {Role : Type u} {Var : Type v} {Var' : Type v'}
    (replacement : Var → RoleTerm Role Var') : RoleTerm Role Var → RoleTerm Role Var'
  | .var x => replacement x
  | .constant r => .constant r

end RoleTerm

/-- The winner sort has its own variables and a role-indexed case operation. -/
inductive WinnerTerm (Role : Type u) (AtomVar : Type v) (WinnerVar : Type w) where
  | var (x : WinnerVar)
  | value (S : WinnerSet Role)
  | inject (a : RoleTerm Role AtomVar)
  | choice (r : Role) (s t : WinnerTerm Role AtomVar WinnerVar)
  | rename (p : Equiv.Perm Role) (t : WinnerTerm Role AtomVar WinnerVar)
  | cases (a : RoleTerm Role AtomVar) (branches : Role → WinnerTerm Role AtomVar WinnerVar)

namespace WinnerTerm

noncomputable def eval {Role : Type u} {AtomVar : Type v} {WinnerVar : Type w}
    (atomVal : AtomVar → Role) (winnerVal : WinnerVar → WinnerSet Role) :
    WinnerTerm Role AtomVar WinnerVar → WinnerSet Role
  | .var x => winnerVal x
  | .value S => S
  | .inject a => WinnerSet.singleton (a.eval atomVal)
  | .choice r s t => WinnerSet.choice r (s.eval atomVal winnerVal) (t.eval atomVal winnerVal)
  | .rename p t => WinnerSet.rename p (t.eval atomVal winnerVal)
  | .cases a branches => (branches (a.eval atomVal)).eval atomVal winnerVal

/-- Substitution preserves the two sorts. -/
def subst {Role : Type u} {AtomVar : Type v} {WinnerVar : Type w}
    {AtomVar' : Type v'} {WinnerVar' : Type w'}
    (atoms : AtomVar → RoleTerm Role AtomVar')
    (winners : WinnerVar → WinnerTerm Role AtomVar' WinnerVar') :
    WinnerTerm Role AtomVar WinnerVar → WinnerTerm Role AtomVar' WinnerVar'
  | .var x => winners x
  | .value S => .value S
  | .inject a => .inject (a.subst atoms)
  | .choice r s t => .choice r (s.subst atoms winners) (t.subst atoms winners)
  | .rename p t => .rename p (t.subst atoms winners)
  | .cases a branches => .cases (a.subst atoms) (fun i => (branches i).subst atoms winners)

/-- Embed a native term with role-sorted input variables. -/
def ofNative {Role : Type u} {Var : Type v} :
    KFOL.Term Role Var → WinnerTerm Role Var Empty
  | .winner r => .value (WinnerSet.singleton r)
  | .var x => .inject (.var x)
  | .choice r s t => .choice r (ofNative s) (ofNative t)
  | .rename p t => .rename p (ofNative t)

end WinnerTerm

/-- A finite list of winner-sort formal parameters for the basis templates. -/
abbrev Parameter (Role : Type u) := (Bool × Role) ⊕ Unit

/-- Indices of the finitely many actual equations, not derivability rules. -/
inductive BasisIndex (Role : Type u) where
  | caseConstant (r : Role)
  | caseDiagonal
  | injection
  | injectConstant (r : Role)
  | choiceCases (r : Role)
  | renameCases (p : Equiv.Perm Role)
  | choiceTable (r : Role) (S T : WinnerSet Role)
  | renameTable (p : Equiv.Perm Role) (S : WinnerSet Role)

abbrev Template (Role : Type u) :=
  WinnerTerm Role Unit (Parameter Role) × WinnerTerm Role Unit (Parameter Role)

/-- The explicit finite two-sorted basis. All templates use one role variable. -/
noncomputable def basis {Role : Type u} : BasisIndex Role → Template Role
  | .caseConstant r =>
      (.cases (.constant r) (fun i => .var (.inl (false, i))), .var (.inl (false, r)))
  | .caseDiagonal =>
      (.cases (.var ()) (fun _ => .var (.inr ())), .var (.inr ()))
  | .injection =>
      (.inject (.var ()), .cases (.var ()) (fun i => .value (WinnerSet.singleton i)))
  | .injectConstant r => (.inject (.constant r), .value (WinnerSet.singleton r))
  | .choiceCases r =>
      (.choice r (.cases (.var ()) (fun i => .var (.inl (false, i))))
        (.cases (.var ()) (fun i => .var (.inl (true, i)))),
       .cases (.var ()) (fun i => .choice r (.var (.inl (false, i))) (.var (.inl (true, i)))))
  | .renameCases p =>
      (.rename p (.cases (.var ()) (fun i => .var (.inl (false, i)))),
       .cases (.var ()) (fun i => .rename p (.var (.inl (false, i)))))
  | .choiceTable r S T =>
      (.choice r (.value S) (.value T), .value (WinnerSet.choice r S T))
  | .renameTable p S => (.rename p (.value S), .value (WinnerSet.rename p S))

/-- Sorted equational deduction from the displayed templates. -/
inductive Derives {Role : Type u} :
    {AtomVar : Type v} → {WinnerVar : Type w} →
      WinnerTerm Role AtomVar WinnerVar → WinnerTerm Role AtomVar WinnerVar → Prop
  | axiom {AtomVar : Type v} {WinnerVar : Type w} (index : BasisIndex Role)
      (atoms : Unit → RoleTerm Role AtomVar)
      (winners : Parameter Role → WinnerTerm Role AtomVar WinnerVar) :
      Derives ((basis index).1.subst atoms winners) ((basis index).2.subst atoms winners)
  | refl {AtomVar : Type v} {WinnerVar : Type w} (t : WinnerTerm Role AtomVar WinnerVar) :
      Derives t t
  | symm {AtomVar : Type v} {WinnerVar : Type w} {s t : WinnerTerm Role AtomVar WinnerVar} :
      Derives s t → Derives t s
  | trans {AtomVar : Type v} {WinnerVar : Type w} {s t q : WinnerTerm Role AtomVar WinnerVar} :
      Derives s t → Derives t q → Derives s q
  | choice {AtomVar : Type v} {WinnerVar : Type w} (r : Role)
      {s s' t t' : WinnerTerm Role AtomVar WinnerVar} :
      Derives s s' → Derives t t' → Derives (.choice r s t) (.choice r s' t')
  | rename {AtomVar : Type v} {WinnerVar : Type w} (p : Equiv.Perm Role)
      {s t : WinnerTerm Role AtomVar WinnerVar} :
      Derives s t → Derives (.rename p s) (.rename p t)
  | cases {AtomVar : Type v} {WinnerVar : Type w} (a : RoleTerm Role AtomVar)
      {s t : Role → WinnerTerm Role AtomVar WinnerVar} :
      (∀ r, Derives (s r) (t r)) → Derives (.cases a s) (.cases a t)
  | subst {AtomVar AtomVar' : Type v} {WinnerVar WinnerVar' : Type w}
      {s t : WinnerTerm Role AtomVar WinnerVar} (h : Derives s t)
      (atoms : AtomVar → RoleTerm Role AtomVar')
      (winners : WinnerVar → WinnerTerm Role AtomVar' WinnerVar') :
      Derives (s.subst atoms winners) (t.subst atoms winners)

end KFOL.AtomicLogic
