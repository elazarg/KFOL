module

public import KFOL.Complexity.CoreExtractionBounds

/-! # Concrete sparse annotation invariants and original-byte storage bounds -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM
open KFOL.FullTermCode FullTermSize

theorem byteBound_cons (N value : ℕ) (values : List ℕ) :
    ByteBound N (value::values) ↔ (encNat value).length ≤ N ∧ ByteBound N values := by
  simp only [ByteBound,List.mem_cons,forall_eq_or_imp]

theorem byteBound_append (N : ℕ) (left right : List ℕ) :
    ByteBound N (left++right) ↔ ByteBound N left ∧ ByteBound N right := by
  simp only [ByteBound,List.mem_append,or_imp,forall_and]

/-- The normalized raw core contains no rename node. -/
def RawPublic : Raw → Prop
  | .var _ => True
  | .func (.winner _) _ => True
  | .func (.choice _) children => RawPublic (children 0) ∧ RawPublic (children 1)
  | .func (.rename _) _ => False

theorem mapRoles_public (forward : List ℕ) (raw : Raw) : RawPublic raw → RawPublic (mapRoles forward raw) := by
  induction raw with
  | var => exact fun _ => trivial
  | @func n operation children ih =>
    cases operation with
    | winner => exact fun _ => trivial
    | choice => exact fun h => ⟨ih 0 h.1,ih 1 h.2⟩
    | rename => exact False.elim

theorem mapRoles_byteBound {N : ℕ} {forward : List ℕ} (hforward : ByteBound N forward)
    (raw : Raw) : ByteBound N (labels raw) → ByteBound N (labels (mapRoles forward raw)) := by
  induction raw with
  | var name => exact id
  | @func n operation children ih =>
    cases operation with
    | winner role =>
      intro _
      change ByteBound N [forward.getD role 0]
      exact (byteBound_cons _ _ _).2 ⟨byteBound_getD hforward _,by simp [ByteBound]⟩
    | choice owner =>
      intro h
      have hl : ByteBound N (labels (children 0)) := fun v hv => h v (by simp [labels,hv])
      have hr : ByteBound N (labels (children 1)) := fun v hv => h v (by simp [labels,hv])
      change ByteBound N ((forward.getD owner 0)::
        (labels (mapRoles forward (children 0)) ++ labels (mapRoles forward (children 1))))
      exact (byteBound_cons _ _ _).2 ⟨byteBound_getD hforward _,
        (byteBound_append _ _ _).2 ⟨ih 0 hl,ih 1 hr⟩⟩
    | rename original =>
      intro h
      have hs := (byteBound_append N original (labels (children 0))).1 h
      change ByteBound N (original ++ labels (mapRoles forward (children 0)))
      exact (byteBound_append _ _ _).2 ⟨hs.1,ih 0 hs.2⟩

/-- A sparse explicit action has at most N stored entries and N bits per
entry; physically absent identity has no entries. -/
def ActionBound (N : ℕ) : Action → Prop
  | none => True
  | some forward => forward.length ≤ N ∧ ByteBound N forward

theorem actionBound_of_weight {N : ℕ} {forward : List ℕ} (h : weight forward ≤ N) :
    ActionBound N (some forward) :=
  ⟨(length_le_length_encList encNat forward).trans h,byteBound_of_weight forward h⟩

theorem actionBound_compose {N : ℕ} {forward : List ℕ} (hforward : ActionBound N (some forward))
    {right : Action} (hright : ActionBound N right) : ActionBound N (Action.compose (some forward) right) := by
  cases right with
  | none => exact hforward
  | some original =>
    change (original.map (fun role => forward.getD role 0)).length ≤ N ∧
      ByteBound N (original.map (fun role => forward.getD role 0))
    refine ⟨by simpa only [List.length_map] using hright.1,?_⟩
    intro role hrole
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp hrole
    exact byteBound_getD hforward.2 index

/-- All cached annotations are bounded by original constructor count and the
actual source-label pool. The statement holds for arbitrary raw input, not
only well-formed K-role permutations. -/
theorem annotate_invariant (N : ℕ) (raw : Raw) (hsource : weight (labels raw) ≤ N) :
    nodes (annotate raw).1 ≤ nodes raw ∧ RawPublic (annotate raw).1 ∧
    ByteBound N (labels (annotate raw).1) ∧ (annotate raw).2.2.length ≤ nodes raw ∧
    ∀ action ∈ (annotate raw).2.2, ActionBound N action := by
  revert hsource
  induction raw with
  | var name =>
    intro h
    refine ⟨le_rfl,trivial,byteBound_of_weight [name] h,le_rfl,?_⟩
    intro action ha
    have he : action = none := by simpa only [annotate,List.mem_singleton] using ha
    rw [he]
    trivial
  | @func n operation children ih =>
    cases operation with
    | winner role =>
      intro h
      exact ⟨le_rfl,trivial,byteBound_of_weight [role] h,by simp [annotate,nodes],by simp [annotate]⟩
    | choice owner =>
      intro h
      have hl : weight (labels (children 0)) ≤ N := by
        simp only [labels,weight_cons,weight_append] at h
        omega
      have hr : weight (labels (children 1)) ≤ N := by
        simp only [labels,weight_cons,weight_append] at h
        omega
      have hleft := ih 0 hl
      have hright := ih 1 hr
      have howner : (encNat owner).length ≤ N :=
        byteBound_of_weight _ h owner (by simp [labels])
      refine ⟨?_,?_,?_,?_,?_⟩
      · change 1+nodes (annotate (children 0)).1+nodes (annotate (children 1)).1 ≤
          1+nodes (children 0)+nodes (children 1)
        omega
      · exact ⟨hleft.2.1,hright.2.1⟩
      · change ByteBound N (owner::(labels (annotate (children 0)).1 ++ labels (annotate (children 1)).1))
        exact (byteBound_cons _ _ _).2 ⟨howner,(byteBound_append _ _ _).2 ⟨hleft.2.2.1,hright.2.2.1⟩⟩
      · change ((annotate (children 0)).2.2 ++ (annotate (children 1)).2.2).length ≤ _
        rw [List.length_append]
        change _ ≤ 1+nodes (children 0)+nodes (children 1)
        omega
      · intro action ha
        change action ∈ (annotate (children 0)).2.2 ++ (annotate (children 1)).2.2 at ha
        exact (List.mem_append.mp ha).elim (hleft.2.2.2.2 action) (hright.2.2.2.2 action)
    | rename forward =>
      intro h
      have hforward : weight forward ≤ N := by simp only [labels,weight_append] at h; omega
      have hchild : weight (labels (children 0)) ≤ N := by simp only [labels,weight_append] at h; omega
      have hc := ih 0 hchild
      refine ⟨?_,mapRoles_public _ _ hc.2.1,?_,?_,?_⟩
      · change nodes (mapRoles forward (annotate (children 0)).1) ≤ 1+nodes (children 0)
        rw [nodes_mapRoles]
        omega
      · exact mapRoles_byteBound (byteBound_of_weight forward hforward) _ hc.2.2.1
      · change ((annotate (children 0)).2.2.map (Action.compose (some forward))).length ≤ _
        rw [List.length_map]
        change _ ≤ 1+nodes (children 0)
        omega
      · intro action ha
        change action ∈ (annotate (children 0)).2.2.map (Action.compose (some forward)) at ha
        obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ha
        exact actionBound_compose (actionBound_of_weight hforward) (hc.2.2.2.2 original ho)

/-- Without rename nodes there is exactly one numeric label per core node. -/
theorem labels_length_of_public (raw : Raw) : RawPublic raw → (labels raw).length = nodes raw := by
  induction raw with
  | var => exact fun _ => rfl
  | @func n operation children ih =>
    cases operation with
    | winner => exact fun _ => rfl
    | choice =>
      intro h
      simp [labels,nodes,ih 0 h.1,ih 1 h.2]
      omega
    | rename => exact False.elim

theorem encode_public_bound (N : ℕ) (raw : Raw) (hpublic : RawPublic raw)
    (hbytes : ByteBound N (labels raw)) : (encode raw).length ≤ 22*nodes raw*(N+1) := by
  have hcode := encode_le_nodes_weight raw
  have hweight := weight_of_byteBound hbytes
  rw [labels_length_of_public raw hpublic] at hweight
  nlinarith

noncomputable abbrev annotationEncoding := encPair FullTermMachines.termEncoding
  (encPair encBool (encList actionEncoding))

theorem actionEncoding_length_bound (N : ℕ) (action : Action) (h : ActionBound N action) :
    (actionEncoding action).length ≤ 1+N*(2*N+1) := by
  cases action with
  | none => change 0 ≤ 1+N*(2*N+1); omega
  | some forward =>
    have hw := weight_of_byteBound h.2
    have hm := Nat.mul_le_mul_right (2*N+1) h.1
    change weight forward+1 ≤ 1+N*(2*N+1)
    omega

theorem actionsEncoding_length_bound (N : ℕ) (actions : List Action)
    (h : ∀ action ∈ actions, ActionBound N action) :
    (encList actionEncoding actions).length ≤ actions.length*(2*(1+N*(2*N+1))+1) := by
  induction actions with
  | nil => simp
  | cons action actions ih =>
    have ha := actionEncoding_length_bound N action (h action (by simp))
    have hs := ih (fun a ha => h a (by simp [ha]))
    simp only [length_encList,List.map_cons,List.sum_cons,List.length_cons]
    rw [← length_encList actionEncoding actions]
    nlinarith

/-- The complete native annotation encoding is cubically bounded by original
raw tree bytes, including malformed raw labels and arrays. No K appears. -/
theorem annotation_encoding_bound (raw : Raw) :
    (annotationEncoding (annotate raw)).length ≤ 100*((encode raw).length+1)^3 := by
  let N := (encode raw).length
  have hi := annotate_invariant N raw (labels_weight_le_encode raw)
  have hn := nodes_le_encode raw
  have hcore := encode_public_bound N (annotate raw).1 hi.2.1 hi.2.2.1
  have hcoreCount : nodes (annotate raw).1 ≤ N := hi.1.trans hn
  have hcoreMul := Nat.mul_le_mul_right (N+1) hcoreCount
  have hactions := actionsEncoding_length_bound N (annotate raw).2.2 hi.2.2.2.2
  have hactionCount : (annotate raw).2.2.length ≤ N := hi.2.2.2.1.trans hn
  have hactionMul := Nat.mul_le_mul_right (2*(1+N*(2*N+1))+1) hactionCount
  have hbool (b : Bool) : (encBool b).length = 1 := by cases b <;> rfl
  simp only [annotationEncoding,length_encPair,FullTermMachines.termEncoding,
    Function.Embedding.coeFn_mk,hbool]
  change _ ≤ 100*(N+1)^3
  nlinarith [hcore,hcoreMul,hactions,hactionMul]

end KFOL.Complexity.CoreExtraction
