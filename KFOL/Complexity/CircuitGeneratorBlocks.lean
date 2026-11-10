module
public import KFOL.Complexity.CircuitGeneratorBuilders
/-! Native polynomial-time construction of the static clause and consistency blocks. Numeric positions originate in physical list lengths. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM ComputableInPolyTime

@[fun_prop] theorem lengthBinary_polyTime {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (List.length (α := α)) (encList enc) encNat :=
  unary_to_binary.comp (length_list enc)

noncomputable abbrev slotsEncoding := encPair encUnary (encPair encNat encNat)
@[fun_prop] theorem slots_polyTime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => slots p.1 p.2.1 p.2.2) slotsEncoding (encList encNat) := by
  have hs : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.2)
      (encPair slotsEncoding encUnary) encNat := by fun_prop
  have ho : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.1)
      (encPair slotsEncoding encUnary) encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.2)
      (encPair slotsEncoding encUnary) encNat := unary_to_binary.comp (snd _ _)
  have hnode := binary_add.comp (ho.prod (binary_mul' hs hi))
  have h := mapWithInput (f := fun (p : ℕ × (ℕ × ℕ)) i => p.2.1 + p.2.2 * i)
    (range.comp (fst encUnary (encPair encNat encNat))) hnode
  simpa only [slots, Function.comp_def] using h

noncomputable abbrev blockEncoding := encPair (encList encNat) (encPair encNat (encPair encNat encNat))
noncomputable abbrev branchEncoding := encPair (encList (encPair encNat encNat)) (encPair encNat encNat)
noncomputable abbrev consistencyEncoding := encPair (encList (encPair encNat encNat))
  (encPair encNat (encPair encNat encNat))

@[fun_prop] theorem retainedNodes_polyTime : ComputableInPolyTime
    (fun p : List ℕ × ℕ => retainedNodes p.1 p.2)
    (encPair (encList encNat) encNat) gatesEncoding := by
  have hp : ComputableInPolyTime (fun p : (List ℕ × ℕ) × ℕ => p.1.2)
      (encPair (encPair (encList encNat) encNat) encNat) encNat := by fun_prop
  have h := mapWithInput (f := fun (p : List ℕ × ℕ) ref => resetGate p.2 ref)
    (fst (encList encNat) encNat) (resetGate_polyTime.comp (hp.prod (snd _ _)))
  exact h

@[fun_prop] theorem branchNodes_polyTime : ComputableInPolyTime
    (fun p : List (ℕ × ℕ) × (ℕ × ℕ) => branchNodes p.1 p.2.1 p.2.2)
    branchEncoding gatesEncoding := by
  let input := encPair branchEncoding (encPair (encPair encNat encNat) encUnary)
  have hm : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => p.1.2.1) input encNat := by fun_prop
  have ho : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => p.1.2.2) input encNat := by fun_prop
  have hl : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => p.2.1.1) input encNat := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => p.2.1.2) input encNat := by fun_prop
  have hi : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) => p.2.2) input encNat :=
    unary_to_binary.comp (by fun_prop)
  have hposition := binary_add.comp (ho.prod (binary_mul' (const 2) hi))
  have hnode := cons' (resetGate_polyTime.comp (hm.prod hl))
    (cons' (resetGate_polyTime.comp (hposition.prod hr)) (const []))
  have hz := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.zipIdx (encPair encNat encNat))).comp
    (fst (encList (encPair encNat encNat)) (encPair encNat encNat))
  have h := flatMapWithInput (f := fun (p : List (ℕ × ℕ) × (ℕ × ℕ)) (item : (ℕ × ℕ) × ℕ) =>
    [resetGate p.2.1 item.1.1,resetGate (p.2.2 + 2 * item.2) item.1.2]) hz hnode
  exact h

@[fun_prop] theorem clauseNodes_polyTime : ComputableInPolyTime
    (fun p : List ℕ × (ℕ × (ℕ × ℕ)) => clauseNodes p.1 p.2.1 p.2.2.1 p.2.2.2)
    blockEncoding gatesEncoding := by
  have hrefs := fst (encList encNat) (encPair encNat (encPair encNat encNat))
  have hp : ComputableInPolyTime (fun p : List ℕ × (ℕ × (ℕ × ℕ)) => p.2.1) blockEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : List ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.1) blockEncoding encNat := by fun_prop
  have ho : ComputableInPolyTime (fun p : List ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.2) blockEncoding encNat := by fun_prop
  have hn := (length_list encNat).comp hrefs
  have hnb := unary_to_binary.comp hn
  have hslots := slots_polyTime.comp (hn.prod (ho.prod (const 1)))
  have hcomb := combNodes_polyTime.comp (hslots.prod (hr.prod (binary_add.comp (ho.prod hnb))))
  have hretained := retainedNodes_polyTime.comp (hrefs.prod hp)
  exact listAppend' hretained hcomb

@[fun_prop] theorem consistencyNodes_polyTime : ComputableInPolyTime
    (fun p : List (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => consistencyNodes p.1 p.2.1 p.2.2.1 p.2.2.2)
    consistencyEncoding gatesEncoding := by
  have hrefs := fst (encList (encPair encNat encNat)) (encPair encNat (encPair encNat encNat))
  have hm : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => p.2.1) consistencyEncoding encNat := by fun_prop
  have hb : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => p.2.2.1) consistencyEncoding encNat := by fun_prop
  have ho : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => p.2.2.2) consistencyEncoding encNat := by fun_prop
  have hn := (length_list (encPair encNat encNat)).comp hrefs
  have hnb := unary_to_binary.comp hn
  have hslots := slots_polyTime.comp (hn.prod ((binary_add.comp (ho.prod (const 1))).prod (const 2)))
  have hcomb := combNodes_polyTime.comp (hslots.prod (hb.prod
    (binary_add.comp (ho.prod (binary_mul' (const 2) hnb)))))
  exact listAppend' (branchNodes_polyTime.comp (hrefs.prod (hm.prod ho))) hcomb
end KFOL.Complexity.CircuitGenerator
