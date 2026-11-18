module

public import KFOL.Core.MonochromaticCutObstruction
public import KFOL.Core.SourceNormalForm
public import KFOL.Equational.Native
public import KFOL.Core.Exhaustion

/-! # Realizing pure source observations along posting paths -/

@[expose] public section
namespace KFOL.Core.PurePostingPaths

open MonochromaticCutObstruction (pureProbe pure_atom)
attribute [local instance] Equational.coreStructure

variable {Role Var : Type*}

/-- A path avoiding heads of color r, ending in a reciprocal pair of one
other color. No simplicity assumption is necessary. -/
inductive ReachesPair (owner : Var → Role) (tail : Var → Var → Bool) (r : Role) : Var → Prop
  | pair {i j} (away : owner i ≠ r) (same : owner j = owner i)
      (ij : tail i j = true) (ji : tail j i = true) : ReachesPair owner tail r i
  | step {i j} (away : owner i ≠ r) (ij : tail i j = true)
      (rest : ReachesPair owner tail r j) : ReachesPair owner tail r i

/-- A path may advance when its target does not block the current owner's
choice. Both endpoints of the terminal reciprocal pair must be available. -/
inductive OpenPath (owner : Var → Role) (tail : Var → Var → Bool)
    (available : Var → Role → Prop) : Var → Prop
  | pair {i j} (same : owner j = owner i) (ij : tail i j = true) (ji : tail j i = true)
      (atI : available i (owner i)) (atJ : available j (owner i)) : OpenPath owner tail available i
  | step {i j} (ij : tail i j = true) (atJ : available j (owner i))
      (rest : OpenPath owner tail available j) : OpenPath owner tail available i

/-- The marked input is unposted. Away from it the coloring records exactly
the nonobserver atoms; posting the observer is never an obstruction. -/
def Unposted (h : Var) (k : Role) (p : Sources.Pattern k h) (i : Var) (r : Role) : Prop :=
  ∀ (hi : i ≠ h) (hr : r ≠ k), p ⟨i,hi⟩ ≠ .atom ⟨r,hr⟩

private abbrev Word (Role Var : Type*) := Equational.Term (Equational.CoreSymbol Role) Var

variable [DecidableEq Role] (three : Fin 3 ↪ Role) (owner : Var → Role) (tail : Var → Var → Bool)

private def Quiet (t : Word Role Var) (i : Var) :=
  ∀ (k : Role) (other : owner i ≠ k),
    k ∉ (t.realize (pureProbe three k i (owner i) other (tail i))).val

omit [DecidableEq Role] in
private theorem leaf_quiet {i j : Var} (ne : j ≠ i) : Quiet three owner tail (.var j) i :=
by
  intro k other hm
  change k ∈ (pureProbe three k i (owner i) other (tail i) j).val at hm
  unfold pureProbe at hm
  exact ne ((Sources.mem_probe_iff three k i _ j).mp hm)

omit [DecidableEq Role] in
private theorem posted (noSelf : ∀ i, tail i i = false) {i j : Var} (edge : tail i j = true)
    (k : Role) (other : owner i ≠ k) :
    pureProbe three k i (owner i) other (tail i) j = WinnerSet.singleton (owner i) := by
  have ne : j ≠ i := fun e => by subst j; rw [noSelf] at edge; contradiction
  unfold pureProbe
  rw [Sources.probe_other _ _ _ _ _ ne]
  simp [edge,Sources.representative]

omit [DecidableEq Role] in
private theorem quiet_choice {x y : Word Role Var} {i : Var} (s : Role)
    (hx : Quiet three owner tail x i) (hy : Quiet three owner tail y i) :
    Quiet three owner tail (choiceTerm s x y) i := by
  intro k other hm
  exact ((WinnerSet.choice_subset_union s _ _ hm).elim (hx k other) (hy k other))

omit [DecidableEq Role] in
private theorem advance (noSelf : ∀ i, tail i i = false)
    {i j : Var} (edge : tail i j = true) (x : Word Role Var)
    (quiet : ∀ z, z ≠ i → Quiet three owner tail x z) :
    ∀ z, z ≠ j → Quiet three owner tail (choiceTerm (owner i) x (.var j)) z := by
  intro z zj
  by_cases zi : z = i
  · subst z
    intro k other
    let v := pureProbe three k i (owner i) other (tail i)
    have atom : WinnerSet.choice (owner i) (x.realize v) (v j) =
        WinnerSet.singleton (owner i) :=
      (WinnerSet.choice_eq_owner_iff _ _ _).mpr (Or.inr (posted three owner tail noSelf edge k other))
    change k ∉ (WinnerSet.choice (owner i) (x.realize v) (v j)).val
    rw [atom]
    exact fun hm => other hm.symm
  · exact quiet_choice three owner tail _ (quiet z zi) (leaf_quiet three owner tail zj.symm)

omit [DecidableEq Role] in
private theorem close_pair (noSelf : ∀ i, tail i i = false)
    {i j : Var} (same : owner j = owner i) (ij : tail i j = true) (ji : tail j i = true)
    (x : Word Role Var) (quiet : ∀ z, z ≠ i → Quiet three owner tail x z) :
    ∀ z, Quiet three owner tail
      (choiceTerm (owner i) x (choiceTerm (owner i) (.var i) (.var j))) z := by
  let pair : Word Role Var := choiceTerm (owner i) (.var i) (.var j)
  have active (z) (hz : z = i ∨ z = j) (k) (other : owner z ≠ k) :
      pair.realize (pureProbe three k z (owner z) other (tail z)) = WinnerSet.singleton (owner i) := by
    apply (WinnerSet.choice_eq_owner_iff _ _ _).mpr
    rcases hz with rfl | rfl
    · exact Or.inr (posted three owner tail noSelf ij k other)
    · exact Or.inl ((posted three owner tail noSelf ji k other).trans (congrArg WinnerSet.singleton same))
  intro z
  by_cases hz : z = i ∨ z = j
  · intro k other
    let v := pureProbe three k z (owner z) other (tail z)
    have actual := (WinnerSet.choice_eq_owner_iff (x.realize v) (pair.realize v) (owner i)).mpr
      (Or.inr (active z hz k other))
    change k ∉ (WinnerSet.choice (owner i) (x.realize v) (pair.realize v)).val
    rw [actual]
    have eq : owner z = owner i := hz.elim (fun e => e ▸ rfl) (fun e => e ▸ same)
    exact fun hm => other (eq.trans hm.symm)
  · obtain ⟨hi,hj⟩ := not_or.mp hz
    exact quiet_choice three owner tail _ (quiet z hi)
      (quiet_choice three owner tail _ (leaf_quiet three owner tail (Ne.symm hi))
        (leaf_quiet three owner tail (Ne.symm hj)))

private theorem keep_mark (v : Var → WinnerSet Role) {s k : Role} (x y : Word Role Var)
    (openRight : s ≠ k → y.realize v ≠ WinnerSet.singleton s) (win : k ∈ (x.realize v).val) :
    k ∈ ((choiceTerm s x y).realize v).val := by
  rw [realize_choice_winner]
  by_cases sk : s = k
  · subst s
    exact (WinnerSet.mem_choice_owner _ _ _).mpr (Or.inl win)
  · have openLeft : x.realize v ≠ WinnerSet.singleton s := by
      intro equal
      rw [equal] at win
      exact sk win.symm
    exact (WinnerSet.mem_choice_other _ _ sk _ _).mpr ⟨Or.inl win,openLeft,openRight sk⟩

/-- Advancing the path discharges the one possible outstanding loss at its
current head. The terminal pair discharges both its own losses at once. -/
private theorem OpenPath.finish (noSelf : ∀ i, tail i i = false)
    {available : Var → Role → Prop} (v : Var → WinnerSet Role) (k : Role)
    (unblocked : ∀ i s, available i s → s ≠ k → v i ≠ WinnerSet.singleton s)
    {i : Var} (path : OpenPath owner tail available i) (x : Word Role Var)
    (quiet : ∀ z, z ≠ i → Quiet three owner tail x z) (win : k ∈ (x.realize v).val) :
    ∃ t : Word Role Var, (∀ z, Quiet three owner tail t z) ∧ k ∈ (t.realize v).val := by
  induction path generalizing x with
  | @pair i j same ij ji atI atJ =>
    refine ⟨_,close_pair three owner tail noSelf same ij ji x quiet,keep_mark v x _ ?_ win⟩
    intro different equal
    rcases (WinnerSet.choice_eq_owner_iff (v i) (v j) (owner i)).mp equal with h | h
    · exact unblocked i _ atI different h
    · exact unblocked j _ atJ different h
  | @step i j ij atJ _ ih =>
    exact ih _ (advance three owner tail noSelf ij x quiet)
      (keep_mark v x (.var j) (unblocked j _ atJ) win)

private theorem ReachesPair.finish (noSelf : ∀ i, tail i i = false)
    {h i : Var} {r k : Role} (other : r ≠ k) (T : Var → Bool) (neutral : T h = false)
    (path : ReachesPair owner tail r i) (x : Word Role Var)
    (quiet : ∀ z, z ≠ i → Quiet three owner tail x z)
    (win : k ∈ (x.realize (pureProbe three k h r other T)).val) :
    ∃ t : Word Role Var, (∀ z, Quiet three owner tail t z) ∧
      k ∈ (t.realize (pureProbe three k h r other T)).val := by
  have lift : OpenPath owner tail (fun _ s => s ≠ r) i := by
    clear quiet
    induction path with
    | pair away same ij ji => exact .pair same ij ji away away
    | step away ij _ ih => exact .step ij away ih
  apply lift.finish three owner tail noSelf _ k _ x quiet win
  intro j s away sk equal
  exact away ((pure_atom three k (.var j) h r other s T neutral sk).mp equal).1

/-- An open posting path supplies its head at an arbitrary source coloring
while respecting every designated loss at every observer. -/
theorem exists_marked_path (noSelf : ∀ i, tail i i = false)
    (h : Var) (k : Role) (p : Sources.Pattern k h)
    (path : OpenPath owner tail (Unposted h k p) h) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ j l (other : owner j ≠ l), l ∉ (t.realize (pureProbe three l j (owner j) other (tail j))).val) ∧
      k ∈ (t.realize (Sources.probe three k h p)).val := by
  apply path.finish three owner tail noSelf _ k _ (.var h)
    (fun z zh => leaf_quiet three owner tail zh.symm) ((Sources.mem_probe_iff _ _ _ _ _).mpr rfl)
  intro i s usable sk equal
  by_cases he : i = h
  · subst i
    rw [Sources.probe_source] at equal
    exact sk (WinnerSet.singleton_inj.mp equal).symm
  · rw [Sources.probe_other three k h p i he] at equal
    exact usable he sk ((Sources.representative_atom_iff _ _ _ ⟨s,sk⟩).mp equal)

omit [DecidableEq Role] in
private theorem join_hits {Q : Type*} (rows : Finset Q) (v : Q → Var → WinnerSet Role)
    (k : Q → Role) (base : ∃ t : Word Role Var, ∀ j, Quiet three owner tail t j)
    (one : ∀ q ∈ rows, ∃ t : Word Role Var, (∀ j, Quiet three owner tail t j) ∧ k q ∈ (t.realize (v q)).val) :
    ∃ t : Word Role Var, (∀ j, Quiet three owner tail t j) ∧ ∀ q ∈ rows, k q ∈ (t.realize (v q)).val := by
  classical
  induction rows using Finset.induction_on with
  | empty =>
    obtain ⟨t,ht⟩ := base
    exact ⟨t,ht,by simp⟩
  | insert q rows _ ih =>
    obtain ⟨s,hs,hq⟩ := one q (Finset.mem_insert_self ..)
    obtain ⟨t,ht,rest⟩ := ih (fun w hw => one w (Finset.mem_insert_of_mem hw))
    refine ⟨unionTerm three s t,?_,?_⟩
    · intro j l other
      rw [realize_union_winner]
      exact fun hm => hm.elim (hs j l other) (ht j l other)
    · intro w hw
      rw [realize_union_winner]
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inl hq
      · exact Or.inr (rest _ hw)

/-- One word supplies any finite nonempty family of independently
path-certified positive source observations and omits all designated losses. -/
theorem exists_marked_paths (noSelf : ∀ i, tail i i = false)
    (rows : Finset (Sources.ProbeIndex Role Var)) (nonempty : rows.Nonempty)
    (paths : ∀ q ∈ rows, OpenPath owner tail (Unposted q.2.1 q.1 q.2.2) q.2.1) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ j l (other : owner j ≠ l), l ∉ (t.realize (pureProbe three l j (owner j) other (tail j))).val) ∧
      ∀ q ∈ rows, q.1 ∈ (t.realize (Sources.probeAt three q)).val := by
  have one (q) (hq : q ∈ rows) := exists_marked_path three owner tail noSelf _ _ _ (paths q hq)
  obtain ⟨q,hq⟩ := nonempty
  obtain ⟨s,hs,_⟩ := one q hq
  exact join_hits three owner tail rows (Sources.probeAt three) Sigma.fst ⟨s,hs⟩ one

/-- Construct one core witness for any prescribed positive pure observation,
while omitting all the designated losses at every legitimate observer. -/
theorem exists_pure_witness (noSelf : ∀ i, tail i i = false)
    (recip : ∀ i j, owner i = owner j → tail i j = true → tail j i = true)
    (paths : ∀ r i, owner i ≠ r → ReachesPair owner tail r i)
    (h : Var) (r k : Role) (other : r ≠ k) (T : Var → Bool) (neutral : T h = false)
    (positive : owner h ≠ r ∨ ∃ u, tail h u = true ∧ T u = false) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ j k (other : owner j ≠ k), k ∉ (t.realize (pureProbe three k j (owner j) other (tail j))).val) ∧
      k ∈ (t.realize (pureProbe three k h r other T)).val := by
  have marked : k ∈ (pureProbe three k h r other T h).val := (Sources.mem_probe_iff _ _ _ _ _).mpr rfl
  by_cases away : owner h ≠ r
  · exact (paths r h away).finish three owner tail noSelf other T neutral (.var h)
      (fun z zh => leaf_quiet three owner tail zh.symm) marked
  obtain eq : owner h = r := not_not.mp away
  obtain ⟨u,edge,hu⟩ := positive.resolve_left away
  let seed : Word Role Var := choiceTerm (owner h) (.var h) (.var u)
  have ne : u ≠ h := fun e => by subst u; rw [noSelf] at edge; contradiction
  have hw : k ∈ (seed.realize (pureProbe three k h r other T)).val := by
    have hhead : pureProbe three k h r other T h ≠ WinnerSet.singleton r := by
      unfold pureProbe
      rw [Sources.probe_source]
      exact fun he => other (WinnerSet.singleton_inj.mp he).symm
    have haux : pureProbe three k h r other T u ≠ WinnerSet.singleton r := by
      intro he
      have bit := (pure_atom three k (.var u) h r other r T neutral other).mp he
      have yes : T u = true := bit.2
      rw [hu] at yes
      contradiction
    let v := pureProbe three k h r other T
    change k ∈ (WinnerSet.choice (owner h) (v h) (v u)).val
    rw [eq,WinnerSet.choice,ite_eq_right (not_or.mpr ⟨hhead,haux⟩)]
    exact Or.inl marked
  have hquiet := advance three owner tail noSelf edge (.var h)
    (fun z zh => leaf_quiet three owner tail zh.symm)
  by_cases ur : owner u = r
  · have back := recip h u (eq.trans ur.symm) edge
    have q : ∀ z, Quiet three owner tail seed z := by
      intro z
      by_cases zu : z = u
      · subst z
        intro l ol
        let v := pureProbe three l u (owner u) ol (tail u)
        change l ∉ (WinnerSet.choice (owner h) (v h) (v u)).val
        rw [show owner h = owner u from eq.trans ur.symm]
        rw [(WinnerSet.choice_eq_owner_iff (v h) (v u) (owner u)).mpr (Or.inl (posted three owner tail noSelf back l ol))]
        exact fun hm => ol hm.symm
      · exact hquiet z zu
    exact ⟨seed,q,hw⟩
  · exact (paths r u ur).finish three owner tail noSelf other T neutral seed hquiet hw

/-- An owner wins its singleton test exactly when all unposted source
probes omit another observer on that pure coloring. -/
theorem profile_iff_pure_omissions
    (r k : Role) (other : r ≠ k) (T : Var → Bool) (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile r T t = true ↔
      ∀ h, T h = false → k ∉ (t.realize (pureProbe three k h r other T)).val := by
  constructor
  · intro win h hh
    rw [(pure_atom three k t h r other r T hh other).mpr ⟨rfl, win⟩]
    exact fun mem => other mem.symm
  · contrapose!
    intro loss
    have hfalse := Bool.eq_false_of_not_eq_true loss
    clear loss
    induction t using induction_choice with
    | var h =>
      refine ⟨h, hfalse, ?_⟩
      change k ∈ (pureProbe three k h r other T h).val
      unfold pureProbe
      exact (Sources.mem_probe_iff _ _ _ _ _).mpr rfl
    | choice s x y ix iy =>
      have child : profile r T x = false ∨ profile r T y = false := by
        cases hx : profile r T x <;> cases hy : profile r T y <;>
          simp_all [profile_choice]
      obtain ⟨h, hh, mem⟩ : ∃ h, T h = false ∧
          (k ∈ (x.realize (pureProbe three k h r other T)).val ∨
           k ∈ (y.realize (pureProbe three k h r other T)).val) := by
        rcases child with hx | hy
        · obtain ⟨h, hh, hm⟩ := ix hx
          exact ⟨h, hh, Or.inl hm⟩
        · obtain ⟨h, hh, hm⟩ := iy hy
          exact ⟨h, hh, Or.inr hm⟩
      refine ⟨h, hh, ?_⟩
      by_cases sk : s = k
      · subst s
        exact (WinnerSet.mem_choice_owner _ _ _).mpr mem
      · have no : (choiceTerm s x y).realize (pureProbe three k h r other T) ≠ WinnerSet.singleton s := by
          intro eq
          have yes := (pure_atom three k _ h r other s T hh sk).mp eq
          simp [hfalse] at yes
        have children := not_or.mp (fun hor => no ((WinnerSet.choice_eq_owner_iff _ _ _).mpr hor))
        exact (WinnerSet.mem_choice_other _ _ sk _ _).mpr ⟨mem, children.1, children.2⟩

/-- A bounded word cannot supply a pure observation extending its designated loss. -/
private theorem pure_bound {t : Word Role Var} (safe : ∀ i, Quiet three owner tail t i)
    {h : Var} {r k : Role} (other : r ≠ k) (T : Var → Bool)
    (win : k ∈ (t.realize (pureProbe three k h r other T)).val) :
    owner h ≠ r ∨ ∃ u, tail h u = true ∧ T u = false := by
  classical
  by_contra! fail
  obtain ⟨rfl,cover⟩ := fail
  apply safe h k other
  let pat (U : Var → Bool) : Sources.Pattern k h := fun i =>
    if U i.val then .atom ⟨owner h,other⟩ else .neutral
  have le : pat T ≤ pat (tail h) := by
    intro i
    by_cases e : tail h i.val = true
    · right
      have ht : T i.val = true := Bool.eq_true_of_not_eq_false (cover i.val e)
      simp [pat,e,ht]
    · left
      simp [pat,e]
  have mono := Sources.coefficient_mono three (Equational.Core.decode t) k h le
  change k ∈ ((Equational.Core.decode t).eval (Sources.probe three k h (pat T))).val →
    k ∈ ((Equational.Core.decode t).eval (Sources.probe three k h (pat (tail h)))).val at mono
  simp only [Equational.Core.eval_decode] at mono
  exact mono win

private abbrev Test (Role Var : Type*) :=
  Σ h : Var, Σ r : Role, Σ _k : {k : Role // r ≠ k}, {T : Var → Bool // T h = false}

/-- If deleting any one owner's heads leaves every other head a path to
a monochromatic pair, one bounded word has exactly the prescribed source
coefficient on every pure posting. -/
theorem exists_pure_realizer [Fintype Role] [Fintype Var] [Nonempty Var]
    (noSelf : ∀ i, tail i i = false)
    (recip : ∀ i j, owner i = owner j → tail i j = true → tail j i = true)
    (paths : ∀ r i, owner i ≠ r → ReachesPair owner tail r i) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ h r k (other : r ≠ k) (T : Var → Bool), T h = false →
        (k ∈ (t.realize (pureProbe three k h r other T)).val ↔
          owner h ≠ r ∨ ∃ u, tail h u = true ∧ T u = false) := by
  classical
  let positive (q : Test Role Var) :=
    owner q.1 ≠ q.2.1 ∨ ∃ u, tail q.1 u = true ∧ q.2.2.2.val u = false
  let v (q : Test Role Var) := pureProbe three q.2.2.1.val q.1 q.2.1 q.2.2.1.property q.2.2.2.val
  have one (q : Test Role Var) (hq : positive q) :
      ∃ t : Word Role Var, (∀ j, Quiet three owner tail t j) ∧ q.2.2.1.val ∈ (t.realize (v q)).val :=
    exists_pure_witness three owner tail noSelf recip paths q.1 q.2.1 _ q.2.2.1.property _
      q.2.2.2.property hq
  have base : ∃ t : Word Role Var, ∀ j, Quiet three owner tail t j := by
    let i : Var := Classical.choice inferInstance
    let _ : Nontrivial Role := ⟨three 0,three 1,three.injective.ne (by decide)⟩
    obtain ⟨r,hr⟩ := exists_ne (owner i)
    obtain ⟨t,ht,_⟩ := one ⟨i,r,⟨owner i,hr⟩,⟨fun _ => false,rfl⟩⟩ (Or.inl hr.symm)
    exact ⟨t,ht⟩
  let Q := Finset.univ.filter positive
  obtain ⟨t,ht,accepts⟩ := join_hits three owner tail Q v (fun q => q.2.2.1.val) base
    (fun q hq => one q (Finset.mem_filter.mp hq).2)
  refine ⟨t,fun h r k other T neutral => ⟨pure_bound three owner tail ht other T,?_⟩⟩
  intro hp
  exact accepts ⟨h,r,⟨k,other⟩,⟨T,neutral⟩⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)

end KFOL.Core.PurePostingPaths
