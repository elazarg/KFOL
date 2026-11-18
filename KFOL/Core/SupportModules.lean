module

public import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Finite.Defs

/-! # Modules of a union-closed family of supports

A module allows its nonempty traces to be exchanged between any two
members meeting it. Overlapping modules generate the five sets in the
partitive-family axiom. The ambient input type need not be finite. -/

@[expose] public section
namespace KFOL.Core.SupportModules

variable {V : Type*} {F : Set (Set V)} {B C : Set V}

/-- Replace the trace of a support on a block, keeping its outside fixed. -/
def swap (B S T : Set V) : Set V := (S \ B) ∪ (T ∩ B)

/-- Every nonempty trace on a module can be used in every context in which
the module is active. -/
def IsModule (F : Set (Set V)) (B : Set V) : Prop :=
  B.Nonempty ∧ ∀ ⦃S T⦄, S ∈ F → T ∈ F → (S ∩ B).Nonempty → (T ∩ B).Nonempty →
    swap B S T ∈ F

private abbrev Hits (S B : Set V) := (S ∩ B).Nonempty
private abbrev Agree (M S T : Set V) := ∀ x ∈ M, x ∈ S ↔ x ∈ T

private theorem in_swap {M S T : Set V} {x : V} (h : x ∈ M) : x ∈ swap M S T ↔ x ∈ T := by
  simp [swap, h]

private theorem outside_swap {M S T : Set V} {x : V} (h : x ∉ M) : x ∈ swap M S T ↔ x ∈ S := by
  simp [swap, h]

private theorem split_hit {S : Set V} (h : Hits S (B ∪ C)) : Hits S B ∨ Hits S C := by
  obtain ⟨x,hx,hb | hc⟩ := h
  · exact .inl ⟨x,hx,hb⟩
  · exact .inr ⟨x,hx,hc⟩

private theorem intersection_module (b : IsModule F B) (c : IsModule F C)
    (i : (B ∩ C).Nonempty) : IsModule F (B ∩ C) := by
  refine ⟨i, ?_⟩
  intro S T s t sh th
  obtain ⟨x,xs,xb,xc⟩ := sh
  obtain ⟨y,yt,yb,yc⟩ := th
  have mid := c.2 s t ⟨x,xs,xc⟩ ⟨y,yt,yc⟩
  have out := b.2 s mid ⟨x,xs,xb⟩ ⟨y,(in_swap yc).mpr yt,yb⟩
  convert out using 1
  ext z
  by_cases zb : z ∈ B <;> by_cases zc : z ∈ C <;> simp [swap, zb, zc]

/-- Copy the two active blocks from T. First install an intersection point
in both supports, so that the last swap can restore T's actual B-trace. -/
private theorem copy_union (b : IsModule F B) (c : IsModule F C) {W S T : Set V}
    (w : W ∈ F) (wi : Hits W (B ∩ C)) (s : S ∈ F) (sh : Hits S (B ∪ C))
    (t : T ∈ F) (tb : Hits T B) : swap (B ∪ C) S T ∈ F := by
  obtain ⟨i,iw,ib,ic⟩ := wi
  have ready : ∃ S' ∈ F, Hits S' C ∧ Agree (B ∪ C)ᶜ S' S := by
    rcases split_hit sh with sb | sc
    · refine ⟨_, b.2 s w sb ⟨i,iw,ib⟩, ⟨i,(in_swap ib).mpr iw,ic⟩, ?_⟩
      exact fun x hx => outside_swap (fun h => hx (Or.inl h))
    · exact ⟨S,s,sc,fun _ _ => Iff.rfl⟩
  obtain ⟨S',s',sc,ag⟩ := ready
  have t' := b.2 t w tb ⟨i,iw,ib⟩
  have mark : i ∈ swap B T W := (in_swap ib).mpr iw
  have mid := c.2 s' t' sc ⟨i,mark,ic⟩
  have out := b.2 mid t ⟨i,(in_swap ic).mpr mark,ib⟩ tb
  convert out using 1
  ext z
  by_cases zb : z ∈ B <;> by_cases zc : z ∈ C <;> simp [swap, zb, zc]
  exact (ag z (fun h => h.elim zb zc)).symm

private theorem union_module (b : IsModule F B) (c : IsModule F C)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) (i : (B ∩ C).Nonempty) : IsModule F (B ∪ C) := by
  obtain ⟨x,xb,xc⟩ := i
  obtain ⟨W,w,wx⟩ := full x
  refine ⟨⟨x,Or.inl xb⟩,?_⟩
  intro S T s t sh th
  rcases split_hit th with tb | tc
  · exact copy_union b c w ⟨x,wx,xb,xc⟩ s sh t tb
  · rw [Set.union_comm B C] at sh ⊢
    exact copy_union c b w ⟨x,wx,xc,xb⟩ s sh t tc

/-- Make C active without changing the trace on B. The extra input is used
only outside B, and union closure keeps the temporary context legal. -/
private theorem prepare (b : IsModule F B)
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    {W S : Set V} (w : W ∈ F) (wc : Hits W (C \ B)) (s : S ∈ F) (sh : Hits S (B ∪ C)) :
    ∃ P ∈ F, Hits P C ∧ Agree B P S := by
  obtain ⟨x,xw,xc,xb⟩ := wc
  rcases split_hit sh with sb | sc
  · obtain ⟨y,ys,yb⟩ := sb
    refine ⟨_, b.2 (union s w) s ⟨y,Or.inl ys,yb⟩ ⟨y,ys,yb⟩,
      ⟨x,(outside_swap xb).mpr (Or.inr xw),xc⟩,fun _ h => in_swap h⟩
  · exact ⟨S,s,sc,fun _ _ => Iff.rfl⟩

/-- Assemble one B-trace with the first donor on B outside C and the second
on its intersection with C. A point in B outside C survives the assembly. -/
private theorem mix_trace (b : IsModule F B) (c : IsModule F C)
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    {W S T : Set V} (w : W ∈ F) (wc : Hits W (C \ B)) (s : S ∈ F)
    (sh : Hits S (B ∪ C)) (t : T ∈ F) (th : Hits T (B \ C)) :
    ∃ P ∈ F, Hits P B ∧ Agree (B \ C) P T ∧ Agree (B ∩ C) P S := by
  obtain ⟨x,xt,xb,xc⟩ := th
  obtain ⟨S',s',sc,agreeS⟩ := prepare b union w wc s sh
  obtain ⟨T',t',tc,agreeT⟩ := prepare b union w wc t ⟨x,xt,Or.inl xb⟩
  refine ⟨_, c.2 t' s' tc sc, ⟨x,(outside_swap xc).mpr ((agreeT x xb).mpr xt),xb⟩, ?_, ?_⟩
  · exact fun y hy => (outside_swap hy.2).trans (agreeT y hy.1)
  · exact fun y hy => (in_swap hy.2).trans (agreeS y hy.1)

private theorem difference_module (b : IsModule F B) (c : IsModule F C)
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) (a : (B \ C).Nonempty) (d : (C \ B).Nonempty) :
    IsModule F (B \ C) := by
  obtain ⟨j,jc,jb⟩ := d
  obtain ⟨W,w,jw⟩ := full j
  refine ⟨a, ?_⟩
  intro S T s t sh th
  obtain ⟨x,xs,xb,_⟩ := sh
  obtain ⟨P,p,pb,ta,si⟩ := mix_trace b c union w ⟨j,jw,jc,jb⟩ s ⟨x,xs,Or.inl xb⟩ t th
  have out := b.2 s p ⟨x,xs,xb⟩ pb
  convert out using 1
  ext z
  by_cases zb : z ∈ B <;> by_cases zc : z ∈ C <;> simp [swap, zb, zc]
  · exact (si z ⟨zb,zc⟩).symm
  · exact (ta z ⟨zb,zc⟩).symm

private theorem copy_sides (b : IsModule F B) (c : IsModule F C) (bc : IsModule F (B ∪ C))
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) (d : (C \ B).Nonempty) {S T : Set V}
    (s : S ∈ F) (sh : Hits S (B ∪ C)) (t : T ∈ F) (th : Hits T (B \ C)) :
    swap ((B \ C) ∪ (C \ B)) S T ∈ F := by
  obtain ⟨j,jc,jb⟩ := d
  obtain ⟨W,w,jw⟩ := full j
  obtain ⟨P,p,pb,ta,si⟩ := mix_trace b c union w ⟨j,jw,jc,jb⟩ s sh t th
  obtain ⟨x,xt,xb,xc⟩ := th
  have mid := b.2 t p ⟨x,xt,xb⟩ pb
  have out := bc.2 s mid sh ⟨x,(in_swap xb).mpr ((ta x ⟨xb,xc⟩).mpr xt),Or.inl xb⟩
  convert out using 1
  ext z
  by_cases zb : z ∈ B <;> by_cases zc : z ∈ C <;> simp [swap, zb, zc]
  · exact (si z ⟨zb,zc⟩).symm
  · exact (ta z ⟨zb,zc⟩).symm

/-- Two overlapping modules of a fully supported, union-closed set family
have modular intersection, union, both differences, and symmetric difference. -/
theorem partitive (b : IsModule F B) (c : IsModule F C)
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S)
    (i : (B ∩ C).Nonempty) (a : (B \ C).Nonempty) (d : (C \ B).Nonempty) :
    IsModule F (B ∩ C) ∧ IsModule F (B ∪ C) ∧ IsModule F (B \ C) ∧ IsModule F (C \ B) ∧
      IsModule F ((B \ C) ∪ (C \ B)) := by
  have bc := union_module b c full i
  refine ⟨intersection_module b c i,bc,difference_module b c union full a d,
    difference_module c b union full d a, ⟨a.mono Set.subset_union_left,?_⟩⟩
  intro S T s t sh th
  have sh' : Hits S (B ∪ C) := by
    obtain ⟨x,xs,h|h⟩ := sh
    · exact ⟨x,xs,Or.inl h.1⟩
    · exact ⟨x,xs,Or.inr h.1⟩
  rcases split_hit th with ta | td
  · exact copy_sides b c bc union full d s sh' t ta
  · rw [Set.union_comm (B \ C) (C \ B)]
    rw [Set.union_comm B C] at sh' bc
    exact copy_sides c b bc union full a s sh' t td

theorem singleton_module (F : Set (Set V)) (x : V) : IsModule F {x} := by
  refine ⟨⟨x,rfl⟩,?_⟩
  intro S T s _ sh th
  have xs : x ∈ S := by simpa using sh
  have xt : x ∈ T := by simpa using th
  have eq : swap {x} S T = S := by
    ext z
    by_cases zx : z = x
    · subst z
      simp [swap, xs, xt]
    · simp [swap, zx]
  rwa [eq]

theorem univ_module [Nonempty V] (F : Set (Set V)) : IsModule F Set.univ := by
  refine ⟨Set.univ_nonempty,?_⟩
  intro S T _ t _ _
  simpa [swap] using t

/-- Inputs belonging to every nonempty legal support. -/
def compulsory (F : Set (Set V)) : Set V :=
  {x | ∀ S ∈ F, S.Nonempty → x ∈ S}

/-- A pair swap introduces a requested input. Union restores any displaced
input from the original support. -/
theorem insert_mem_of_pair_modules
    (pair : ∀ x y : V, x ≠ y → IsModule F {x,y})
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) {S : Set V} (s : S ∈ F) (ne : S.Nonempty) (x : V) :
    insert x S ∈ F := by
  classical
  by_cases xs : x ∈ S
  · simpa [Set.insert_eq_of_mem xs] using s
  obtain ⟨y,ys⟩ := ne
  have xy : x ≠ y := fun h => xs (h ▸ ys)
  obtain ⟨T,t,xt⟩ := full x
  have out := union s ((pair x y xy).2 s t ⟨y,ys,by simp⟩ ⟨x,xt,by simp⟩)
  convert out using 1
  ext z
  by_cases zx : z = x <;> by_cases zy : z = y <;> simp_all [swap]

/-- Retain any second input and delete a noncompulsory one by exchanging
their pair with a donor whose trace contains only the retained input. -/
theorem erase_mem_of_pair_modules
    (pair : ∀ x y : V, x ≠ y → IsModule F {x,y})
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) {S : Set V} (s : S ∈ F)
    {x y : V} (xy : x ≠ y) (ys : y ∈ S) (optional : x ∉ compulsory F) :
    S \ {x} ∈ F := by
  classical
  obtain ⟨D,d,ne,dx⟩ : ∃ D ∈ F, D.Nonempty ∧ x ∉ D := by
    simpa [compulsory, not_forall] using optional
  have add := insert_mem_of_pair_modules pair union full d ne y
  have out := (pair x y xy).2 s add ⟨y,ys,by simp⟩ ⟨y,by simp,by simp⟩
  convert out using 1
  ext z
  by_cases zx : z = x <;> by_cases zy : z = y <;> simp_all [swap]

/-- On a finite set of inputs, if every pair is a module, the nonempty legal
supports are exactly the supersets of the compulsory inputs. -/
theorem mem_iff_compulsory_subset [Finite V]
    (pair : ∀ x y : V, x ≠ y → IsModule F {x,y})
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) {T : Set V} (ne : T.Nonempty) :
    T ∈ F ↔ compulsory F ⊆ T := by
  classical
  constructor
  · exact fun t _ h => h T t ne
  · intro core
    let _ := Fintype.ofFinite V
    obtain ⟨y,yt⟩ := ne
    obtain ⟨S,s,ys⟩ := full y
    have augment (D : Finset V) : S ∪ (D : Set V) ∈ F := by
      induction D using Finset.induction_on with
      | empty => simpa using s
      | insert x D _ ih =>
        simpa [Set.union_insert] using
          insert_mem_of_pair_modules pair union full ih ⟨y,Or.inl ys⟩ x
    have all : (Set.univ : Set V) ∈ F := by simpa using augment Finset.univ
    have trim (D : Finset V) (outside : (D : Set V) ⊆ Tᶜ) : (D : Set V)ᶜ ∈ F := by
      induction D using Finset.induction_on with
      | empty => simpa using all
      | insert x D _ ih =>
        have nx : x ∉ T := outside (by simp)
        have sub : (D : Set V) ⊆ Tᶜ := fun z hz => outside (by simp [hz])
        have keep : y ∈ (D : Set V)ᶜ := fun hy => sub hy yt
        have out := erase_mem_of_pair_modules pair union full (ih sub)
          (fun (h : x = y) => nx (h ▸ yt)) keep (fun hc => nx (core hc))
        convert out using 1
        ext z
        simp [and_comm]
    let D := Finset.univ.filter (fun z : V => z ∉ T)
    have eq : (D : Set V) = Tᶜ := by ext z; simp [D]
    have out := trim D (by rw [eq])
    simpa [eq] using out

/-- All pairs being modules forces every nonempty block to be a module. -/
theorem module_of_pair_modules [Finite V]
    (pair : ∀ x y : V, x ≠ y → IsModule F {x,y})
    (union : ∀ ⦃S T⦄, S ∈ F → T ∈ F → S ∪ T ∈ F)
    (full : ∀ x, ∃ S ∈ F, x ∈ S) {B : Set V} (ne : B.Nonempty) : IsModule F B := by
  refine ⟨ne,?_⟩
  intro S T s t sh th
  obtain ⟨x,xs,xb⟩ := sh
  obtain ⟨y,yt,yb⟩ := th
  apply (mem_iff_compulsory_subset pair union full ⟨y,(in_swap yb).mpr yt⟩).mpr
  intro z hz
  by_cases zb : z ∈ B
  · exact (in_swap zb).mpr (hz T t ⟨y,yt⟩)
  · exact (outside_swap zb).mpr (hz S s ⟨x,xs⟩)

end KFOL.Core.SupportModules
