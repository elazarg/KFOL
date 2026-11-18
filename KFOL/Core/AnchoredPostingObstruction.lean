module

public import KFOL.Core.SinglePostingObstruction
public import KFOL.Core.SourceReciprocity
public import KFOL.Core.ProfileCutObstruction

/-! # The seven-row obstruction with an eighth input fixed at α -/

@[expose] public section
namespace KFOL.Core.AnchoredPostingObstruction

open SinglePostingObstruction (Input owner tail values)
open MonochromaticCutObstruction (pureProbe)
open MonochromaticCutObstruction.ThreeOwners (observer owner_ne_observer)

variable {Role Var : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

private abbrev Word (Role Var : Type*) := Equational.Term (Equational.CoreSymbol Role) Var

omit [DecidableEq Role] in
/-- A pure loss still omits any observer absent away from the head at a
valuation that keeps all its posted atoms. The original and the tested
observer may differ. -/
private theorem quiet_of_compatible_pure_loss (three : Fin 3 ↪ Role)
    (t : Word Role Var) (j : Var) (T : Var → Bool) (k r : Role) (ne : r ≠ k)
    (quiet : k ∉ (t.realize (pureProbe three k j r ne T)).val)
    (a : Role) (v : Var → WinnerSet Role)
    (away : ∀ i, i ≠ j → a ∉ (v i).val)
    (keep : ∀ i, i ≠ j → T i = true → v i = WinnerSet.singleton r) :
    a ∉ (t.realize v).val := by
  classical
  let s := Equational.Core.decode t
  have core : s.IsCore := Equational.Core.isCore_decode t
  let p : Sources.Pattern k j := fun i => if T i.val then .atom ⟨r,ne⟩ else .neutral
  have loss : k ∉ (s.eval (Sources.probe three k j p)).val := by
    simpa only [s,Equational.Core.eval_decode,p,pureProbe] using quiet
  let w := Function.update v j (Sources.representative three a .neutral)
  have eq := (Sources.probe_loss_iff_cofactor_independent three s core k j p).mp loss v w
    (fun i hi => (Function.update_of_ne hi _ _).symm) (by
      intro i q post
      cases h : T i.val with
      | false => simp [p,h] at post
      | true =>
        have e : r = q.val := by simpa [p,h,Subtype.ext_iff] using post
        exact (keep i.val i.property h).trans (congrArg WinnerSet.singleton e))
  rw [← Equational.Core.eval_decode]
  change a ∉ (s.eval v).val
  rw [eq]
  intro hit
  obtain ⟨i,hi,_⟩ := (Sources.membership_iff_source three s core w a).mp hit
  by_cases h : i = j
  · subst i
    simp [w] at hi
  · exact away i h (by simpa [w,h] using hi)

omit [DecidableEq Role] in
private theorem pure_other_omits (three : Fin 3 ↪ Role) (j i : Var) (r k : Role)
    (ne : r ≠ k) (T : Var → Bool) (hi : i ≠ j) :
    k ∉ (pureProbe three k j r ne T i).val :=
  fun hit => hi ((Sources.mem_probe_iff three _ _ _ i).mp hit)

omit [DecidableEq Role] in
private theorem pure_posted (three : Fin 3 ↪ Role) (j i : Var) (r k : Role)
    (ne : r ≠ k) (T : Var → Bool) (hi : i ≠ j) (h : T i = true) :
    pureProbe three k j r ne T i = WinnerSet.singleton r := by
  simp [pureProbe,Sources.probe,hi,h,Sources.representative]

omit [DecidableEq Role] in
private theorem pureProbe_decide (three : Fin 3 ↪ Role) (j : Var) (r k : Role)
    (ne : r ≠ k) (T : Var → Prop) [DecidablePred T] :
    pureProbe three k j r ne (fun i => decide (T i)) =
      Sources.probe three k j (fun i => if T i.val then .atom ⟨r,ne⟩ else .neutral) := by
  unfold pureProbe
  congr 1
  funext i
  by_cases h : T i.val <;> simp [h]

/-- In the lifted rows the extra input is posted only at the two α-heads.
Every other posting is inherited from the seven-input example. -/
def liftedTail (j : Input) : Input ⊕ Unit → Bool :=
  Sum.elim (tail j) (fun _ => decide (owner j = 0))

noncomputable def liftedProbe (three : Fin 3 ↪ Role) (j : Input) :
    Input ⊕ Unit → WinnerSet Role :=
  pureProbe three (three (observer (owner j))) (.inl j) (three (owner j))
    (three.injective.ne (owner_ne_observer _)) (liftedTail j)

/-- With the eighth input at α and the old input X at d, the seven lifted
losses confine every winner to {α,d}. This conclusion holds for all values
of the other six inputs. -/
theorem cofactor_bound [Fintype Role] (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Input ⊕ Unit))
    (quiet : ∀ j, three (observer (owner j)) ∉ (t.realize (liftedProbe three j)).val)
    (v : Input → WinnerSet Role) (hx : v .x = WinnerSet.singleton (three 2)) :
    (t.realize (Sum.elim v (fun _ => WinnerSet.singleton (three 0)))).val ⊆
      {three 0,three 2} := by
  classical
  let fixed (_ : Unit) := WinnerSet.singleton (three 0)
  obtain ⟨e, eval⟩ := CompletionDepth.Expr.exists_of_core t
  obtain ⟨z, _, hz⟩ := e.exists_erasure three (fun _ => some (three 0))
  have represents := hz fixed (fun _ r => by simp [fixed,WinnerSet.singleton_inj])
  have onlyAlpha : (⋃ i, (fixed i).val) ⊆ {three 0,three 2} := by simp [fixed]
  rw [← eval]
  cases z with
  | dead flag =>
    obtain ⟨c,sub,_,constant⟩ := represents
    change (e.eval (Sum.elim v fixed)).val ⊆ _
    simpa only [show e.eval (Sum.elim v fixed) = c from constant v] using sub.trans onlyAlpha
  | live f mask =>
    obtain ⟨g, hg⟩ := f.exists_core three
    have hrows (j : Input) :
        three (observer (owner j)) ∉ (g.realize (values three j (owner j) (tail j))).val := by
      let r := three (owner j)
      let k := three (observer (owner j))
      have ne : r ≠ k := three.injective.ne (owner_ne_observer _)
      obtain ⟨a,ar,aa⟩ := exists_role_outside_pair three r (three 0)
      let w := pureProbe three a j r ar.symm (tail j)
      have freeze : a ∉ (t.realize (Sum.elim w fixed)).val := by
        apply quiet_of_compatible_pure_loss three t (.inl j) (liftedTail j) k r ne (quiet j)
        · intro i hi
          cases i with
          | inl i => exact pure_other_omits three j i r a ar.symm _ (fun h => hi (congrArg Sum.inl h))
          | inr u => exact aa
        · intro i hi post
          cases i with
          | inl i => exact pure_posted three j i r a ar.symm _ (fun h => hi (congrArg Sum.inl h)) post
          | inr u =>
            have h : owner j = 0 := of_decide_eq_true post
            exact congrArg (fun b => WinnerSet.singleton (three b)) h.symm
      have localLoss : a ∉ (g.realize w).val := by
        rw [hg]
        exact fun hit => freeze (eval (Sum.elim w fixed) ▸ (represents w).1 hit)
      apply quiet_of_compatible_pure_loss three g j (tail j) a r ar.symm localLoss k
      · intro i hi
        exact pure_other_omits three j i r k ne _ hi
      · intro i hi post
        exact pure_posted three j i r k ne _ hi post
    have win := SinglePostingObstruction.forced_profile three g hrows
    have atom : g.realize v = WinnerSet.singleton (three 2) := by
      apply (winnerSet_eq_singleton_iff_profile g (three 2) v).mpr
      exact profile_mono _ _ _ (fun i hi => by
        obtain rfl : i = .x := of_decide_eq_true hi
        exact decide_eq_true hx) g win
    have actual : f.eval v = WinnerSet.singleton (three 2) := (hg v).symm.trans atom
    apply (represents v).2.1.trans (Set.union_subset _ onlyAlpha)
    rw [actual]
    exact Set.singleton_subset_iff.mpr (by simp)

private def originalName : Input → ProfileCutObstruction.Input
  | .a => .A | .a' => .a | .x => .X | .b => .B | .y => .Y | .b' => .b | .z => .Z

private def splitInput : ProfileCutObstruction.Input → Input ⊕ Unit
  | .A => .inl .a | .a => .inl .a' | .X => .inl .x | .B => .inl .b
  | .Y => .inl .y | .b => .inl .b' | .Z => .inl .z | .U => .inr ()

omit [DecidableEq Role] in
private theorem originalName_probe (three : Fin 3 ↪ Role) (j : Input) :
    liftedProbe three j ∘ splitInput =
    pureProbe three (three (observer (owner j))) (originalName j) (three (owner j))
      (three.injective.ne (owner_ne_observer _))
      (fun i => decide (i ∈ ProfileCutObstruction.tail (originalName j))) := by
  funext i
  cases j <;> cases i <;>
    simp [liftedProbe,pureProbe,Sources.probe,liftedTail,splitInput,originalName,
      ProfileCutObstruction.tail,owner,tail,Function.comp_apply]

/-- On the eight-input loss table, the seven original heads suffice
for the bound at the two prescribed singletons. -/
theorem table_cofactor_bound [Fintype Role] (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) ProfileCutObstruction.Input)
    (quiet : ∀ j : ProfileCutObstruction.Input, j ≠ .U →
      let r := ProfileCutObstruction.owner j
      three (observer r) ∉ (t.realize (Sources.probe three (three (observer r)) j
        (fun i => if i.val ∈ ProfileCutObstruction.tail j then
          .atom ⟨three r, three.injective.ne (owner_ne_observer _)⟩ else .neutral))).val)
    (v : ProfileCutObstruction.Input → WinnerSet Role)
    (hu : v .U = WinnerSet.singleton (three 0)) (hx : v .X = WinnerSet.singleton (three 2)) :
    (t.realize v).val ⊆ {three 0,three 2} := by
  have safe (j : Input) :
      three (observer (owner j)) ∉ ((t.relabel splitInput).realize (liftedProbe three j)).val := by
    rw [FirstOrder.Language.Term.realize_relabel,originalName_probe,pureProbe_decide]
    have ne : originalName j ≠ .U := by cases j <;> decide
    have row := quiet (originalName j) ne
    cases j <;> exact row
  have bound := cofactor_bound three (t.relabel splitInput) safe (v ∘ originalName) hx
  rw [FirstOrder.Language.Term.realize_relabel] at bound
  have eq : Sum.elim (v ∘ originalName) (fun _ => WinnerSet.singleton (three 0)) ∘ splitInput = v := by
    funext i
    cases i <;> first | rfl | exact hu.symm
  rwa [eq] at bound

end KFOL.Core.AnchoredPostingObstruction
