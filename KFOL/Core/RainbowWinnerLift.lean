module

public import KFOL.Core.Profiles
public import KFOL.Algebra.Basic

/-! # Detecting a winner by positive singleton tests on tagged inputs -/

@[expose] public section
namespace KFOL.Core.RainbowWinnerLift

universe u v
variable {Role : Type u} {Var : Type v}

/-- Inputs carrying the observed winner have one starred copy. An input that
does not carry it may be tagged by any owner whose singleton it does not give. -/
inductive Copy (v : Var → WinnerSet Role) (k : Role)
  | star (j : Var) (carries : k ∈ (v j).val)
  | tag (j : Var) (absent : k ∉ (v j).val) (r : Role) (available : v j ≠ WinnerSet.singleton r)

variable {v : Var → WinnerSet Role} {k : Role}

def Copy.label : Copy v k → Var
  | .star j _ | .tag j _ _ _ => j

/-- The coalition at r contains every copy except those tagged r. -/
def demand [DecidableEq Role] (r : Role) : Copy v k → Bool
  | .star _ _ => true
  | .tag _ _ s _ => decide (s ≠ r)

private abbrev Word (Role : Type*) (X : Type*) := Equational.Term (Equational.CoreSymbol Role) X
attribute [local instance] Equational.coreStructure

/-- The semantic condition for meeting the tests of only the owners in P. -/
private def Available (k : Role) (P : Set Role) (x : WinnerSet Role) : Prop :=
  k ∈ x.val ∨ ∃ s ∉ P, x ≠ WinnerSet.singleton s

private theorem available_less {P : Set Role} {x : WinnerSet Role} {r : Role} :
    Available k P x → Available k (P \ {r}) x :=
  fun h => h.imp_right fun ⟨s, hs, ne⟩ => ⟨s, fun hin => hs hin.1, ne⟩

private theorem available_singleton {P : Set Role} {r : Role} :
    Available k (P \ {r}) (WinnerSet.singleton r) → Available k P (WinnerSet.singleton r) := by
  rintro (hit | ⟨s, hs, ne⟩)
  · exact Or.inl hit
  · exact Or.inr ⟨s, fun hin => hs ⟨hin, fun sr => ne (sr ▸ rfl)⟩, ne⟩

private theorem available_union (P : Set Role) (x y : WinnerSet Role) :
    Available k P (x.union y) ↔ Available k P x ∨ Available k P y := by
  classical
  change ((k ∈ x.val ∨ k ∈ y.val) ∨ ∃ s ∉ P, x.union y ≠ WinnerSet.singleton s) ↔ _
  simp only [Available, ne_eq, WinnerSet.union_eq_singleton_iff, not_and_or]
  grind

/-- A gate needs every foreign test at both children. Its own test, when
requested, may come from either child. -/
private theorem available_choice (P : Set Role) (r : Role) (x y : WinnerSet Role) :
    Available k P (WinnerSet.choice r x y) ↔
      (Available k P x ∧ Available k (P \ {r}) y) ∨
        (Available k (P \ {r}) x ∧ Available k P y) := by
  classical
  have light (u : WinnerSet Role) (ne : u ≠ WinnerSet.singleton r) :
      Available k (P \ {r}) u := Or.inr ⟨r, by simp, ne⟩
  by_cases absorbs : x = WinnerSet.singleton r ∨ y = WinnerSet.singleton r
  · rw [(WinnerSet.choice_eq_owner_iff x y r).mpr absorbs]
    constructor
    · intro h
      have either (u : WinnerSet Role) : Available k (P \ {r}) u := by
        by_cases eq : u = WinnerSet.singleton r
        · exact eq ▸ available_less h
        · exact light u eq
      obtain eq | eq := absorbs
      · exact Or.inl ⟨eq ▸ h, either _⟩
      · exact Or.inr ⟨either _, eq ▸ h⟩
    · rintro (⟨full, rest⟩ | ⟨rest, full⟩)
      · rcases absorbs with eq | eq
        · exact eq ▸ full
        · exact available_singleton (eq ▸ rest)
      · rcases absorbs with eq | eq
        · exact available_singleton (eq ▸ rest)
        · exact eq ▸ full
  · rw [WinnerSet.choice, ite_eq_right absorbs, available_union]
    obtain ⟨hx,hy⟩ := not_or.mp absorbs
    exact ⟨fun h => h.imp (fun h => ⟨h, light _ hy⟩) (fun h => ⟨light _ hx, h⟩),
      fun h => h.imp And.left And.right⟩

private theorem relabel_choice {X Y : Type*} (f : X → Y) (r : Role) (s t : Word Role X) :
    (choiceTerm r s t).relabel f = choiceTerm r (s.relabel f) (t.relabel f) := by
  unfold choiceTerm
  rw [FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

variable [DecidableEq Role]

private def Wins (P : Set Role) (t : Word Role (Copy v k)) :=
  ∀ r ∈ P, profile r (demand r) t = true

private theorem wins_choice (P : Set Role) (r : Role) (x y : Word Role (Copy v k)) :
    Wins P (choiceTerm r x y) ↔
      (Wins P x ∧ Wins (P \ {r}) y) ∨ (Wins (P \ {r}) x ∧ Wins P y) := by
  have sub {t : Word Role (Copy v k)} (h : Wins P t) : Wins (P \ {r}) t :=
    fun s hs => h s hs.1
  have full {t : Word Role (Copy v k)} (light : Wins (P \ {r}) t)
      (own : r ∈ P → profile r (demand r) t = true) : Wins P t := by
    intro s hs
    by_cases eq : s = r
    · exact eq ▸ own (eq ▸ hs)
    · exact light s ⟨hs,eq⟩
  constructor
  · intro win
    have foreign (s : Role) (hs : s ∈ P \ {r}) :
        profile s (demand s) x = true ∧ profile s (demand s) y = true := by
      have ne : r ≠ s := Ne.symm hs.2
      simpa only [profile_choice, ite_eq_right ne, Bool.and_eq_true] using win s hs.1
    have lx : Wins (P \ {r}) x := fun s hs => (foreign s hs).1
    have ly : Wins (P \ {r}) y := fun s hs => (foreign s hs).2
    by_cases hr : r ∈ P
    · have own : profile r (demand r) x = true ∨ profile r (demand r) y = true := by
        simpa only [profile_choice, ite_true, Bool.or_eq_true] using win r hr
      exact own.imp (fun h => ⟨full lx (fun _ => h), ly⟩) (fun h => ⟨lx, full ly (fun _ => h)⟩)
    · exact Or.inl ⟨full lx (fun h => (hr h).elim), ly⟩
  · intro h s hs
    by_cases eq : r = s
    · subst s
      simp only [profile_choice, ite_true, Bool.or_eq_true]
      exact h.imp (fun h => h.1 r hs) (fun h => h.2 r hs)
    · have both := h.elim (fun h => And.intro (sub h.1) h.2) (fun h => And.intro h.1 (sub h.2))
      have hh : s ∈ P \ {r} := ⟨hs,Ne.symm eq⟩
      simp only [profile_choice, ite_eq_right eq, Bool.and_eq_true]
      exact ⟨both.1 s hh, both.2 s hh⟩

private theorem exists_lift (v : Var → WinnerSet Role) (k : Role) (t : Word Role Var) (P : Set Role)
    (h : Available k P (t.realize v)) :
    ∃ w : Word Role (Copy v k), w.relabel Copy.label = t ∧ Wins P w := by
  classical
  induction t using induction_choice generalizing P with
  | var j =>
    by_cases hit : k ∈ (v j).val
    · exact ⟨.var (.star j hit), rfl, fun _ _ => rfl⟩
    · obtain ⟨r, hr, ne⟩ := h.resolve_left hit
      exact ⟨.var (.tag j hit r ne), rfl, fun s hs => decide_eq_true (fun eq => hr (eq ▸ hs))⟩
  | choice r x y ix iy =>
    have join {L R : Set Role}
        (hl : Available k L (x.realize v)) (hr : Available k R (y.realize v))
        (hc : ∀ a b : Word Role (Copy v k), Wins L a → Wins R b → Wins P (choiceTerm r a b)) :
        ∃ w : Word Role (Copy v k), w.relabel Copy.label = choiceTerm r x y ∧ Wins P w := by
      obtain ⟨a, ea, ha⟩ := ix L hl
      obtain ⟨b, eb, hb⟩ := iy R hr
      exact ⟨choiceTerm r a b, by rw [relabel_choice, ea, eb], hc a b ha hb⟩
    rcases (available_choice P r _ _).mp h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact join hx hy (fun a b ha hb => (wins_choice P r a b).mpr (Or.inl ⟨ha,hb⟩))
    · exact join hx hy (fun a b ha hb => (wins_choice P r a b).mpr (Or.inr ⟨ha,hb⟩))

private theorem available_of_wins (w : Word Role (Copy v k)) (P : Set Role) (h : Wins P w) :
    Available k P (w.realize (v ∘ Copy.label)) := by
  induction w using induction_choice generalizing P with
  | var j =>
    cases j with
    | star j carries => exact Or.inl carries
    | tag j absent r ne =>
      refine Or.inr ⟨r, fun hr => ?_, ne⟩
      simpa [demand] using h r hr
  | choice r x y ix iy =>
    apply (available_choice P r _ _).mpr
    exact ((wins_choice P r x y).mp h).imp
      (fun h => ⟨ix _ h.1,iy _ h.2⟩) (fun h => ⟨ix _ h.1,iy _ h.2⟩)

/-- For an arbitrary subfamily of the rainbow demands, a missing owner's
test may be dropped precisely when the value is different from its singleton. -/
theorem exists_retagging_iff (v : Var → WinnerSet Role) (k : Role)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (P : Set Role) :
    (∃ w : Equational.Term (Equational.CoreSymbol Role) (Copy v k),
      w.relabel Copy.label = t ∧ ∀ r ∈ P, profile r (demand r) w = true) ↔
      k ∈ (t.realize v).val ∨ ∃ s ∉ P, t.realize v ≠ WinnerSet.singleton s := by
  constructor
  · rintro ⟨w, rfl, hw⟩
    rw [FirstOrder.Language.Term.realize_relabel]
    exact available_of_wins w P hw
  · exact exists_lift v k t P

/-- A prescribed winner occurs if and only if the leaves of this very word
can be retagged so that every owner's positive coalition wins. The equation
after relabeling preserves every gate and every occurrence of the original
syntax. No finiteness assumptions are needed. -/
theorem mem_realize_iff_exists_retagging (v : Var → WinnerSet Role) (k : Role)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    k ∈ (t.realize v).val ↔ ∃ w : Equational.Term (Equational.CoreSymbol Role) (Copy v k),
      w.relabel Copy.label = t ∧ ∀ r, profile r (demand r) w = true := by
  simpa using (exists_retagging_iff v k t Set.univ).symm

end KFOL.Core.RainbowWinnerLift
