/- Semantic certificates for the dissemilattice subvariety of the core.
The generation and residual-bound theorems use the external results
identified in appendix-core-basis.tex; they are not axioms here. -/
import Perspectives

set_option autoImplicit false
namespace MinimalChoice.CoreModels

theorem own_associative {α : Type} (r : α) (A B C : S α)
    (hA : NE A) (hB : NE B) (hC : NE C) :
    own r (own r A B) C = own r A (own r B C) := by
  classical
  have hab := join_eq_atom_iff A B hA hB r
  have hbc := join_eq_atom_iff B C hB hC r
  by_cases ha : A = atom r <;> by_cases hb : B = atom r <;>
    by_cases hc : C = atom r <;>
    simp_all [own]
  funext i
  apply propext
  exact or_assoc

theorem own_distributes_join {α : Type} (r : α) (A B C : S α)
    (hB : NE B) (hC : NE C) :
    own r A (join B C) = join (own r A B) (own r A C) := by
  classical
  have hbc := join_eq_atom_iff B C hB hC r
  by_cases ha : A = atom r <;> by_cases hb : B = atom r <;>
    by_cases hc : C = atom r <;>
    simp_all [own] <;>
    funext i <;> apply propext <;> simp only [join] <;> grind

inductive Three where
  | b | n | p
  deriving DecidableEq, Repr

def Three.add : Three → Three → Three
  | .p, _ | _, .p => .p
  | .n, _ | _, .n => .n
  | .b, .b => .b

def Three.mul : Three → Three → Three
  | .b, _ | _, .b => .b
  | .p, _ | _, .p => .p
  | .n, .n => .n

def Three.embed : Three → S (Fin 3)
  | .b => atom 0
  | .n => fun i => i = 0 ∨ i = 1
  | .p => fun _ => True

theorem Three.embed_ne (x : Three) : NE x.embed := by
  refine ⟨0, ?_⟩
  cases x <;> simp [embed, atom]

theorem Three.embed_injective (x y : Three) (he : x.embed = y.embed) : x = y := by
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  cases x <;> cases y <;> simp_all [embed, atom]

theorem Three.embed_add (x y : Three) : (x.add y).embed = join x.embed y.embed := by
  cases x <;> cases y <;> funext i <;> apply propext <;>
    simp [add, embed, atom, join, or_comm]

theorem Three.embed_eq_atom (x : Three) : x.embed = atom 0 ↔ x = .b := by
  constructor
  · exact fun he => embed_injective x .b he
  · intro he
    subst x
    rfl

theorem Three.embed_mul (x y : Three) : (x.mul y).embed = own 0 x.embed y.embed := by
  classical
  simp only [own, embed_eq_atom]
  cases x <;> cases y <;> simp only [mul, reduceCtorEq, or_self, or_true,
    true_or, ↓reduceIte] <;> funext i <;> apply propext <;>
    simp [embed, atom, join]

theorem Three.other_own (r : Fin 3) (hr : r ≠ 0) (x y : Three) :
    (x.add y).embed = own r x.embed y.embed := by
  classical
  have ha (z : Three) : z.embed ≠ atom r := by
    intro he
    have hz : z.embed 0 := by cases z <;> simp [embed, atom]
    have : atom r 0 := he ▸ hz
    exact hr this.symm
  simpa [own, ha x, ha y] using embed_add x y

theorem Three.distributive (x y z : Three) :
    x.mul (y.add z) = (x.mul y).add (x.mul z) := by
  cases x <;> cases y <;> cases z <;> decide

theorem Three.not_dual_distributive :
    Three.n.add (Three.b.mul Three.p) ≠
      (Three.n.add Three.b).mul (Three.n.add Three.p) := by decide

end MinimalChoice.CoreModels

#print axioms MinimalChoice.CoreModels.own_distributes_join
#print axioms MinimalChoice.CoreModels.Three.embed_mul
#print axioms MinimalChoice.CoreModels.Three.other_own
