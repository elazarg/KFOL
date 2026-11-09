module

public import KFOL.Algorithms.FullTermCode.View

/-! # Sparse accumulated permutation arrays, with no ambient-K enumeration -/

@[expose] public section

namespace KFOL.FullTermCode

/-- Missing accumulated action is literally identity and consumes no role
array. An explicit array is carried only after an actual rename occurrence. -/
abbrev Action := Option (List ℕ)

namespace Action

/-- Array lookup is by the actual binary role label; it is not a loop clock. -/
def apply (action : Action) (role : ℕ) : ℕ :=
  match action with
  | none => role
  | some forward => forward.getD role 0

/-- Compose explicit forward arrays by traversing an existing array. Neither
identity case constructs an array of size K from its binary role count. -/
def compose : Action → Action → Action
  | none, right => right
  | left, none => left
  | some left, some right => some (right.map (fun role => left.getD role 0))

/-- Identity testing enumerates only an explicitly stored array's positions. -/
def isIdentity : Action → Bool
  | none => true
  | some forward => forward.zipIdx.all (fun entry => entry.1 == entry.2)

/-- Exact connection to an actual role permutation. A syntactically absent
array represents identity; an explicit array must be its complete forward map. -/
def Represents {K : ℕ} (action : Action) (permutation : Equiv.Perm (Fin K)) : Prop :=
  (action = none ∧ permutation = 1) ∨ action = some (permutationArray permutation)

theorem represents_none {K : ℕ} : Represents none (1 : Equiv.Perm (Fin K)) := Or.inl ⟨rfl,rfl⟩
theorem represents_some {K : ℕ} (permutation : Equiv.Perm (Fin K)) :
    Represents (some (permutationArray permutation)) permutation := Or.inr rfl

/-- Exact numerical-order array composition agrees with permutation product. -/
theorem permutationArray_mul {K : ℕ} (p q : Equiv.Perm (Fin K)) :
    permutationArray (p*q) =
      (permutationArray q).map (fun role => (permutationArray p).getD role 0) := by
  simp only [permutationArray,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def]
  simp [Equiv.Perm.mul_apply]

/-- Sparse composition is faithful, including both physically absent identity
arrays and explicit identity arrays. -/
theorem compose_represents {K : ℕ} {left right : Action} {p q : Equiv.Perm (Fin K)}
    (hl : Represents left p) (hr : Represents right q) :
    Represents (compose left right) (p*q) := by
  rcases hl with ⟨rfl,rfl⟩ | rfl
  · simpa only [compose,one_mul] using hr
  · rcases hr with ⟨rfl,rfl⟩ | rfl
    · simpa only [compose,mul_one] using represents_some p
    · simp only [compose]
      rw [← permutationArray_mul]
      exact represents_some _

theorem apply_of_represents {K : ℕ} {action : Action} {p : Equiv.Perm (Fin K)}
    (h : Represents action p) (i : Fin K) : apply action i.val = (p i).val := by
  rcases h with ⟨rfl,rfl⟩ | rfl
  · rfl
  · exact permutationArray_getD p i

/-- The machine's finite actual-array identity test is exactly permutation
identity; no traversal of Fin K is performed when the array is absent. -/
theorem isIdentity_iff {K : ℕ} {action : Action} {p : Equiv.Perm (Fin K)}
    (h : Represents action p) : isIdentity action = true ↔ p = 1 := by
  rcases h with ⟨rfl,rfl⟩ | rfl
  · simp [isIdentity]
  · simp only [isIdentity,List.all_eq_true,beq_iff_eq]
    constructor
    · intro hall
      apply Equiv.Perm.ext
      intro i
      apply Fin.ext
      have hm := List.getElem_mem (l := (permutationArray p).zipIdx)
        (n := i.val) (by simpa only [List.length_zipIdx,permutationArray_length] using i.isLt)
      have he : ((p i).val,i.val) ∈ (permutationArray p).zipIdx := by
        simpa [permutationArray] using hm
      exact hall _ he
    · intro hp
      subst p
      intro entry hm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
      rw [← he]
      simp [permutationArray]

end Action
end KFOL.FullTermCode
