module

public import Mathlib.Data.List.Basic

/-! # One residual per ordered register does not suffice

A rejecting cut covers every currently eligible head. Every posting of
a retained row can be adopted, and the child residual is contained in
the parent's residual after discharging the rows covered by that offer.
Two compulsory paths in the five-row instance reach the same register
in the same adoption order with disjoint possibilities for head three.
-/

@[expose] public section
namespace KFOL.Core.OrderedResidualObstruction

/-- The register is ordered by recency, most recent adoption first. -/
structure Cut {Key Row Offer : Type} (root : Key) (adopt : Key → Offer → Key)
    (head : Row → ℕ) (eligible : Key → ℕ → Bool)
    (posted covers : Row → Offer → Bool) where
  live : Key → Prop
  keep : Key → Row → Prop
  start : live root
  cover : ∀ {k i}, live k → eligible k i = true → ∃ j, keep k j ∧ head j = i
  next : ∀ {k j}, keep k j → ∀ e, posted j e = true → live (adopt k e)
  subset : ∀ {k j}, keep k j → ∀ e, posted j e = true →
    ∀ {i}, keep (adopt k e) i → keep k i ∧ covers i e = false

inductive Row | A | B | C | D | E deriving DecidableEq, Repr
inductive Owner | p | q deriving DecidableEq, Repr
abbrev Offer := Owner × ℕ
abbrev Key := List Offer

def adopt (k : Key) (e : Offer) : Key := e :: k.filter (fun f => decide (f.1 ≠ e.1))

def head : Row → ℕ
  | .A => 0 | .B => 1 | .C => 2 | .D | .E => 3

def posting : Row → Owner → ℕ
  | .A, .p => 4 | .A, .q => 2
  | .B, .q => 12
  | .C, .p => 10
  | .D, .q => 1
  | .E, .p => 1
  | _, _ => 0

def posted (j : Row) (e : Offer) := decide (e.2 ≠ 0 ∧ posting j e.1 = e.2)
def covers (j : Row) (e : Offer) := decide (e.2 &&& posting j e.1 = e.2)

def held (k : Key) (o : Owner) : ℕ :=
  ((k.find? (fun e => e.1 == o)).map Prod.snd).getD 0

theorem held_adopt (k : Key) (e : Offer) (o : Owner) :
    held (adopt k e) o = if e.1 = o then e.2 else held k o := by
  by_cases eq : e.1 = o
  · simp [held,adopt,eq]
  · simp only [adopt,held,List.find?_cons,beq_eq_false_iff_ne.mpr eq,List.find?_filter]
    rw [ite_eq_right eq]
    congr 2
    apply congrArg (fun test => k.find? test)
    funext f
    by_cases same : f.1 = o <;> simp [same,Ne.symm eq]

theorem adopt_congr {j k : Key} (h : ∀ o, held j o = held k o) (e : Offer) (o : Owner) :
    held (adopt j e) o = held (adopt k e) o := by simp only [held_adopt,h]

/-- The unposted query has head zero. Every nonempty register requires
membership in each held coalition. -/
def eligible (k : Key) (i : ℕ) : Bool :=
  let pMask := held k .p
  let qMask := held k .q
  if pMask = 0 ∧ qMask = 0 then decide (i = 0) else
    (pMask == 0 || pMask.testBit i) && (qMask == 0 || qMask.testBit i)

theorem eligible_congr {j k : Key} (h : ∀ o, held j o = held k o) (i : ℕ) :
    eligible j i = eligible k i := by simp only [eligible,h]

abbrev Certificate := Cut ([] : Key) adopt head eligible posted covers

abbrev p2 : Offer := (.p,4)
abbrev p13 : Offer := (.p,10)
abbrev p0 : Offer := (.p,1)
abbrev q1 : Offer := (.q,2)
abbrev q23 : Offer := (.q,12)
abbrev q0 : Offer := (.q,1)

private theorem mark (c : Certificate) {k : Key} (active : c.live k) (i : ℕ)
    (ok : eligible k i = true) : match i with
    | 0 => c.keep k .A | 1 => c.keep k .B | 2 => c.keep k .C
    | _ => c.keep k .D ∨ c.keep k .E := by
  obtain ⟨j,contains,eq⟩ := c.cover active ok
  subst i
  cases j <;> simp only [head] <;> tauto

private theorem next (c : Certificate) {k : Key} {j : Row} (h : c.keep k j)
    (e : Offer) (p : posted j e = true := by decide) : c.live (adopt k e) := c.next h e p

private theorem back (c : Certificate) {k : Key} {j : Row} (h : c.keep k j)
    (e : Offer) {other : Row} (child : c.keep (adopt k e) other)
    (p : posted j e = true := by decide) : c.keep k other := (c.subset h e p child).1

private theorem clash (c : Certificate) {k : Key} {j : Row} (h : c.keep k j)
    (e : Offer) {other : Row} (child : c.keep (adopt k e) other)
    (p : posted j e = true := by decide) (s : covers other e = true := by decide) : False := by
  have eq := (c.subset h e p child).2
  simp [s] at eq

/-- Every one-residual cut would need D and E at the root; neither can
be dropped before the two incompatible branches begin. -/
private theorem root_de (c : Certificate) : c.keep [] .D ∧ c.keep [] .E := by
  have a := mark c c.start 0 (by decide)
  constructor
  · have c' := mark c (next c a p2) 2 (by decide)
    obtain d|e := mark c (next c c' p13) 3 (by decide)
    · exact back c a p2 (back c c' p13 d)
    · have a' := mark c (next c e p0) 0 (by decide)
      exact (clash c a p2 (back c c' p13 (back c e p0 a'))).elim
  · have b := mark c (next c a q1) 1 (by decide)
    obtain d|e := mark c (next c b q23) 3 (by decide)
    · have a' := mark c (next c d q0) 0 (by decide)
      exact (clash c a q1 (back c b q23 (back c d q0 a'))).elim
    · exact back c a q1 (back c b q23 e)

/-- The common ordered register reached by D,B,C and E,A,B,C must retain
a row with head 3. The first path has discharged D and the second E. -/
theorem no_single_residual (c : Certificate) : False := by
  obtain ⟨d,e⟩ := root_de c
  have a₁ := mark c (next c d q0) 0 (by decide)
  have b₁ := back c a₁ q1 (mark c (next c a₁ q1) 1 (by decide))
  have c₁ := mark c (next c b₁ q23) 2 (by decide)
  have a₂ := mark c (next c e p0) 0 (by decide)
  have c₂ := mark c (next c a₂ p2) 2 (by decide)
  have b₂ := back c c₂ p13 (mark c (next c c₂ p13) 1 (by decide))
  have c₃ := mark c (next c b₂ q23) 2 (by decide)
  obtain keepD|keepE := mark c (next c c₁ p13) 3 (by decide)
  · exact clash c d q0 (back c b₁ q23 (back c c₁ p13 keepD))
  · exact clash c e p0 (back c a₂ p2 (back c b₂ q23 (back c c₃ p13 keepE)))

def rows : List Row := [.A,.B,.C,.D,.E]
def owners : List Owner := [.p,.q]

def number : Row → ℕ
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4

def sameRegister (j k : Key) : Bool := owners.all (fun o => held j o == held k o)


abbrev Node := Key × ℕ

/-- The nonempty residuals of a two-copy certificate. The five low bits of
each mask stand for A through E. All absent child registers reached by an
adoption have no eligible head and use the empty residual. -/
def nodes : List Node := [
  ([],31), ([p0],15), ([p2],14), ([p13],10), ([q0],23), ([q1],22), ([q23],20),
  ([p0,q0],1), ([p2,q23],12), ([p13,q1],18), ([p13,q23],8), ([p13,q23],16)]

def selectRow (n : Node) (j : Row) : Bool := n.2.testBit (number j)

def noHead (k : Key) := (List.range 4).all (fun i => !eligible k i)

def childOK (n m : Node) (e : Offer) : Bool :=
  sameRegister m.1 (adopt n.1 e) &&
    rows.all (fun row => !selectRow m row || (selectRow n row && !covers row e))

/-- Every active node covers its eligible heads and every adoption has
a child residual that survives deletion. The common register comparison
forgets recency, so the same two choices also work with recency kept. -/
def checkedNode (n : Node) : Bool :=
  (List.range 4).all (fun i => !eligible n.1 i ||
    rows.any (fun j => head j == i && selectRow n j)) &&
  rows.all (fun j => !selectRow n j || owners.all (fun o =>
    let e := (o,posting j o)
    !posted j e || noHead (adopt n.1 e) || nodes.any (fun m => childOK n m e)))

/-- Closed finite verification of the root, coverage, all adoption edges,
and the bound of two nonempty residuals at every register. -/
theorem two_residuals :
    (([] : Key),31) ∈ nodes ∧
    (∀ n ∈ nodes, checkedNode n = true) ∧
    (∀ n ∈ nodes, (nodes.filter (fun m => sameRegister n.1 m.1)).length ≤ 2) := by decide

/-- The finite check supplies an actual successor for every adoption of a
retained row. An empty successor has no eligible head. In a nonempty
successor every retained row survives the specified adoption. -/
theorem two_slot_obligations {n : Node} (listed : n ∈ nodes) :
    (∀ i : Fin 4, eligible n.1 i = true →
      ∃ j : Row, selectRow n j = true ∧ head j = i.val) ∧
    (∀ j : Row, selectRow n j = true → ∀ o : Owner,
      let e := (o,posting j o)
      posted j e = true →
        (∀ i : Fin 4, eligible (adopt n.1 e) i = false) ∨
        ∃ m ∈ nodes, (∀ role, held m.1 role = held (adopt n.1 e) role) ∧
          ∀ v : Row, selectRow m v = true → selectRow n v = true ∧ covers v e = false) := by
  have allRows (j : Row) : j ∈ rows := by cases j <;> decide
  have allOwners (o : Owner) : o ∈ owners := by cases o <;> decide
  obtain ⟨cover,edges⟩ := Bool.and_eq_true_iff.mp (two_residuals.2.1 n listed)
  constructor
  · intro i hi
    have hit := List.all_eq_true.mp cover i.val (List.mem_range.mpr i.isLt)
    simp only [hi,Bool.not_true,Bool.false_or,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at hit
    obtain ⟨j,_,hj,hsel⟩ := hit
    exact ⟨j,hsel,hj⟩
  · intro j hj o e he
    have atRow := List.all_eq_true.mp edges j (allRows j)
    simp only [hj,Bool.not_true,Bool.false_or] at atRow
    have atOwner := List.all_eq_true.mp atRow o (allOwners o)
    change (!posted j e || noHead (adopt n.1 e) || nodes.any (fun m => childOK n m e)) = true at atOwner
    simp only [he,Bool.not_true,Bool.false_or,Bool.or_eq_true,List.any_eq_true] at atOwner
    rcases atOwner with empty | ⟨m,member,ok⟩
    · left
      intro i
      simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp empty i.val (List.mem_range.mpr i.isLt))
    · right
      obtain ⟨same,survive⟩ := Bool.and_eq_true_iff.mp ok
      refine ⟨m,member,fun role => beq_iff_eq.mp (List.all_eq_true.mp same role (allOwners role)),?_⟩
      intro v hv
      have hit := List.all_eq_true.mp survive v (allRows v)
      simpa only [hv,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true'] using hit

end KFOL.Core.OrderedResidualObstruction
