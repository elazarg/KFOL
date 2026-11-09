module
public import KFOL.Policies.Normalized
public import KFOL.Algorithms.FiniteTermCode
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace KFOL.Complexity.PolicyGuardWeight
open KFOL.Policies
variable {Role Label : Type} [DecidableEq Role]
variable [Fintype (FiniteTermCode.Operation (Symbol Label))]
def nameWeight (j : ℕ) : ℕ := 2 * j.bits.length + 1

def payload (ell : Label → ℕ) (g : Guard Label ℕ) : ℕ :=
  nameWeight g.source + 1 + 2 * (g.many.map nameWeight).sum +
    (g.passes.map (fun p => nameWeight p.2 + 2 * ell p.1)).sum

omit [DecidableEq Role] [Fintype (FiniteTermCode.Operation (Symbol Label))] in
private theorem payload_addMany (ell : Label → ℕ) (g : Guard Label ℕ) (j : ℕ) :
    payload ell (g.addMany j) = payload ell g + 2 * nameWeight j := by
  simp only [payload, Guard.addMany, List.map_cons, List.sum_cons]
  omega
omit [DecidableEq Role] [Fintype (FiniteTermCode.Operation (Symbol Label))] in
private theorem payload_addPass (ell : Label → ℕ) (g : Guard Label ℕ) (d : Label) (j : ℕ) :
    payload ell (g.addPass d j) = payload ell g + nameWeight j + 2 * ell d := by
  simp only [payload, Guard.addPass, List.map_cons, List.sum_cons]
  omega

omit [Fintype (FiniteTermCode.Operation (Symbol Label))] in
private theorem payload_normalize (ell : Label → ℕ) (D : Label → Finset Role) (top : Finset Role)
    (g : Guard Label ℕ) (j : ℕ) : payload ell (g.normalizeAt D top j) ≤ payload ell g + 2 * nameWeight j := by
  unfold Guard.normalizeAt
  split
  · exact (payload_addMany ell g j).le
  · omega

private theorem length_var (j : ℕ) :
    (FiniteTermCode.encode (Symbol Label) (.var j)).length = nameWeight j + 2 := by
  simp [FiniteTermCode.encode_var, Words.delimit_length, Words.BinaryNatCode.encode, nameWeight]
private theorem length_step (s t : Policies.Term Label ℕ) :
    1 + (FiniteTermCode.encode (Symbol Label) s).length + (FiniteTermCode.encode (Symbol Label) t).length ≤
      (FiniteTermCode.encode (Symbol Label) (Term.step s t)).length := by
  simp [Term.step, FiniteTermCode.encode_func, List.ofFn_succ]
  omega
private theorem length_selective (d : Label) (x y z : Policies.Term Label ℕ) :
    1 + (FiniteTermCode.encode (Symbol Label) x).length + (FiniteTermCode.encode (Symbol Label) y).length +
      (FiniteTermCode.encode (Symbol Label) z).length ≤
      (FiniteTermCode.encode (Symbol Label) (Term.selective d x y z)).length := by
  simp [Term.selective, FiniteTermCode.encode_func, List.ofFn_succ]
  omega

theorem root_le (t : Policies.Term Label ℕ) : nameWeight t.root ≤ (FiniteTermCode.encode (Symbol Label) t).length := by
  induction t using Term.induction_policy with
  | var j => rw [Term.root_var, length_var]; omega
  | step s t hs ht => have h := length_step s t; rw [Term.root_step]; omega
  | selective d x y z hx hy hz => have h := length_selective d x y z; rw [Term.root_selective]; omega

theorem leaves_le (t : Policies.Term Label ℕ) : t.leafCount ≤ (FiniteTermCode.encode (Symbol Label) t).length := by
  induction t using Term.induction_policy with
  | var j => rw [length_var]; change 1 ≤ nameWeight j + 2; omega
  | step s t hs ht => have h := length_step s t; change s.leafCount + t.leafCount ≤ _; omega
  | selective d x y z hx hy hz => have h := length_selective d x y z; change x.leafCount + y.leafCount + z.leafCount ≤ _; omega

omit [DecidableEq Role] [Fintype (FiniteTermCode.Operation (Symbol Label))] in
private theorem extension (child total parent c : ℕ) (hc : child ≤ total) (hp : total + 1 ≤ parent) :
    c * child^2 + c * total ≤ c * parent^2 := by
  have hchild := Nat.pow_le_pow_left hc 2
  have hparent := Nat.pow_le_pow_left hp 2
  have hbase : child^2 + total ≤ parent^2 := by nlinarith
  have hm := Nat.mul_le_mul_left c hbase
  simpa only [Nat.mul_add] using hm

theorem payload_le (ell : Label → ℕ) (L : ℕ) (hell : ∀ d, ell d ≤ L)
    (D : Label → Finset Role) (top : Finset Role) (t : Policies.Term Label ℕ)
    (g : Guard Label ℕ) (hg : g ∈ t.normalGuards D top) :
    payload ell g ≤ (5 + 2*L) * (FiniteTermCode.encode (Symbol Label) t).length^2 := by
  induction t using Term.induction_policy generalizing g with
  | var j =>
    have he : g = ⟨j, [], []⟩ := List.mem_singleton.mp hg
    subst g
    rw [length_var]
    simp only [payload, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    nlinarith [Nat.zero_le (nameWeight j), Nat.zero_le (L * (nameWeight j)^2)]
  | step s t hs ht =>
    rw [Term.normalGuards_step] at hg
    have hcode := length_step s t
    rcases List.mem_append.mp hg with hg | hg
    · have hb := ht g hg
      have he := extension (FiniteTermCode.encode (Symbol Label) t).length
        ((FiniteTermCode.encode (Symbol Label) s).length + (FiniteTermCode.encode (Symbol Label) t).length)
        (FiniteTermCode.encode (Symbol Label) (Term.step s t)).length (5+2*L) (by omega) (by omega)
      omega
    · obtain ⟨before, hm, rfl⟩ := List.mem_map.mp hg
      rw [payload_addMany]
      have hb := hs before hm
      have hr := root_le t
      have he := extension (FiniteTermCode.encode (Symbol Label) s).length
        ((FiniteTermCode.encode (Symbol Label) s).length + (FiniteTermCode.encode (Symbol Label) t).length)
        (FiniteTermCode.encode (Symbol Label) (Term.step s t)).length (5+2*L) (by omega) (by omega)
      nlinarith
  | selective d x y z hx hy hz =>
    rw [Term.normalGuards_selective] at hg
    let total := (FiniteTermCode.encode (Symbol Label) x).length + (FiniteTermCode.encode (Symbol Label) y).length +
      (FiniteTermCode.encode (Symbol Label) z).length
    have hcode : total + 1 ≤ (FiniteTermCode.encode (Symbol Label) (Term.selective d x y z)).length := by
      have h := length_selective d x y z; dsimp [total]; omega
    have htotal : 1 ≤ total := by
      have h := FiniteTermCode.length_encode_pos (σ := Symbol Label) x
      dsimp [total]; omega
    have hrx := root_le x
    have hry := root_le y
    rcases List.mem_append.mp hg with hg | hg
    · have hb := hx g hg
      have he := extension (FiniteTermCode.encode (Symbol Label) x).length total
        (FiniteTermCode.encode (Symbol Label) (Term.selective d x y z)).length (5+2*L) (by dsimp [total]; omega) hcode
      omega
    · obtain ⟨middle, hm, rfl⟩ := List.mem_map.mp hg
      rw [payload_addMany]
      rcases List.mem_append.mp hm with hm | hm
      · have hb := hy middle hm
        have he := extension (FiniteTermCode.encode (Symbol Label) y).length total
          (FiniteTermCode.encode (Symbol Label) (Term.selective d x y z)).length (5+2*L) (by dsimp [total]; omega) hcode
        dsimp [total] at he
        nlinarith
      · obtain ⟨passed, hp, rfl⟩ := List.mem_map.mp hm
        obtain ⟨before, hb, rfl⟩ := List.mem_map.mp hp
        have hbound := hz before hb
        have hn := payload_normalize ell D top (before.addPass d y.root) y.root
        rw [payload_addPass] at hn
        have he := extension (FiniteTermCode.encode (Symbol Label) z).length total
          (FiniteTermCode.encode (Symbol Label) (Term.selective d x y z)).length (5+2*L) (by dsimp [total]; omega) hcode
        have hd := hell d
        have hlabel : 2*ell d ≤ 2*L*total := by nlinarith
        dsimp [total] at he htotal hlabel
        nlinarith


omit [DecidableEq Role] [Fintype (FiniteTermCode.Operation (Symbol Label))] in
private theorem sum_le {α : Type} (values : List α) (weight : α → ℕ) (bound : ℕ)
    (h : ∀ value ∈ values, weight value ≤ bound) : (values.map weight).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have hv := h value (by simp)
    have hr := ih (fun v hm => h v (by simp [hm]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem annotation_le (ell : Label → ℕ) (L : ℕ) (hell : ∀ d, ell d ≤ L)
    (D : Label → Finset Role) (top : Finset Role) (t : Policies.Term Label ℕ) :
    nameWeight t.root + ((t.normalGuards D top).map (fun g => 2 * payload ell g + 1)).sum ≤
      (12 + 4*L) * ((FiniteTermCode.encode (Symbol Label) t).length + 1)^3 := by
  let N := (FiniteTermCode.encode (Symbol Label) t).length
  have hs := sum_le (t.normalGuards D top) (fun g => 2 * payload ell g + 1) (2*(5+2*L)*N^2+1) (by
    intro g hg
    have hb := payload_le ell L hell D top t g hg
    dsimp [N]
    nlinarith)
  rw [Term.normalGuards_length] at hs
  have hl := leaves_le t
  have hr := root_le t
  have hmul := Nat.mul_le_mul_right (2*(5+2*L)*N^2+1) hl
  dsimp [N] at hs hmul
  nlinarith
end KFOL.Complexity.PolicyGuardWeight
