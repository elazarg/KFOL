module

public import KFOL.Complexity.CircuitRecords
public import KFOL.Complexity.FiniteTermDecoding
public import KFOL.Complexity.RawRecords

/-! Complete native flat-code bridge for original shared graph records. -/

@[expose] public section

namespace KFOL.Complexity.CircuitMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words KFOL.FiniteTermCode

variable {σ : ℕ → Type} [Fintype (Operation σ)]

noncomputable def encodeRawGate (gate : RawGate σ) : List Bool :=
  gate.1.elim (false :: BinaryNatCode.encode gate.2.1)
    (fun operation => true :: pair (encodeOperation σ operation) (Algorithms.LabelDictionary.encode gate.2.2))

private theorem dictionary_encode_polyTime : ComputableInPolyTime Algorithms.LabelDictionary.encode
    (encList encNat) encBits := by
  have hlabel := (Framing.delimit_polyTime.comp Dictionary.encode_polyTime).comp (snd (encList encNat) encNat)
  have h := flatMapToBitsWithInput (f := fun (_ : List ℕ) j => delimit (BinaryNatCode.encode j))
    (id' (encIn := encList encNat)) hlabel
  convert h using 1
  funext labels
  simp only [Algorithms.LabelDictionary.encode, List.map_map, List.flatMap_def, Function.comp_def]

theorem encodeRawGate_polyTime : ComputableInPolyTime (encodeRawGate (σ := σ)) gateEncoding encBits := by
  have ho : ComputableInPolyTime (fun gate : RawGate σ => gate.1)
      gateEncoding (encOption FiniteTermMachines.operationEncoding) := by fun_prop
  have hj : ComputableInPolyTime (fun gate : RawGate σ => gate.2.1) gateEncoding encNat := by fun_prop
  have hinput := bitsCons (const false) (Dictionary.encode_polyTime.comp hj)
  let inner := encPair (gateEncoding (σ := σ)) (FiniteTermMachines.operationEncoding (σ := σ))
  have hop := (ComputableInPolyTime.of_eq (f := encodeOperation σ) (encIn := FiniteTermMachines.operationEncoding)
    (encOut := encBits) (fun _ => rfl)).comp (snd (gateEncoding (σ := σ)) FiniteTermMachines.operationEncoding)
  have hrefs : ComputableInPolyTime (fun p : RawGate σ × Operation σ => p.1.2.2)
      inner (encList encNat) := by fun_prop
  have hfunc := bitsCons (const true) (Framing.pair_polyTime.comp (hop.prod (dictionary_encode_polyTime.comp hrefs)))
  exact ho.optionElimWithInput (body := fun (gate : RawGate σ) operation =>
    true :: pair (encodeOperation σ operation) (Algorithms.LabelDictionary.encode gate.2.2)) hinput hfunc

noncomputable def encodeRawGates (gates : List (RawGate σ)) : List Bool :=
  ((gates.map encodeRawGate).map delimit).flatten

theorem encodeRawGates_polyTime : ComputableInPolyTime (encodeRawGates (σ := σ)) (encList gateEncoding) encBits := by
  have hgate := (Framing.delimit_polyTime.comp encodeRawGate_polyTime).comp
    (snd (encList (gateEncoding (σ := σ))) (gateEncoding (σ := σ)))
  have h := flatMapToBitsWithInput (f := fun (_ : List (RawGate σ)) gate => delimit (encodeRawGate gate)) id' hgate
  convert h using 1
  funext gates
  simp only [encodeRawGates, List.map_map, List.flatMap_def, Function.comp_def]

noncomputable def encodeData (data : RawEquation σ) : List Bool :=
  pair (encodeRawGates data.1) (pair (BinaryNatCode.encode data.2.1) (BinaryNatCode.encode data.2.2))

theorem encodeData_polyTime : ComputableInPolyTime (encodeData (σ := σ)) dataEncoding encBits := by
  have hg := encodeRawGates_polyTime.comp (fst (encList (gateEncoding (σ := σ))) (encPair encNat encNat))
  have hl : ComputableInPolyTime (fun data : RawEquation σ => data.2.1) dataEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun data : RawEquation σ => data.2.2) dataEncoding encNat := by fun_prop
  exact Framing.pair_polyTime.comp (hg.prod
    (Framing.pair_polyTime.comp ((Dictionary.encode_polyTime.comp hl).prod (Dictionary.encode_polyTime.comp hr))))

@[simp] theorem encodeRawGate_view (gate : Circuit.Gate σ ℕ) : encodeRawGate (viewGate gate) = Circuit.Code.encodeGate σ gate := by
  cases gate <;> rfl

@[simp] theorem encodeData_view (equation : Circuit.Equation σ ℕ) : encodeData (view equation) = Circuit.Code.encode σ equation := by
  simp only [encodeData, view, encodeRawGates, List.map_map, Function.comp_def, encodeRawGate_view,
    Circuit.Code.encode, Circuit.Code.encodeGates]


noncomputable def decodeFunction (body : List Bool) : Option (Operation σ × List ℕ) := do
  let (opcode, word) ← unpair? body
  let operation ← decodeOperation σ opcode
  let refs ← Algorithms.LabelDictionary.decode word
  return (operation, refs)

noncomputable def decodeRawGate : List Bool → Option (RawGate σ)
  | [] => none
  | false :: body => (BinaryNatCode.decode? body).map (fun j => (none, (j, [])))
  | true :: body => do
      let (operation, refs) ← decodeFunction body
      if refs.length = operation.1 then some (some operation, (0, refs)) else none

noncomputable def decodeRawGates (word : List Bool) : Option (List (RawGate σ)) := do
  let blocks ← undelimitBlocks word
  blocks.mapM (decodeRawGate (σ := σ))

noncomputable def decodeData (word : List Bool) : Option (RawEquation σ) := do
  let (stream, outputs) ← unpair? word
  let gates ← decodeRawGates stream
  let (leftCode, rightCode) ← unpair? outputs
  let left ← BinaryNatCode.decode? leftCode
  let right ← BinaryNatCode.decode? rightCode
  return (gates, (left, right))

theorem decodeRawGate_eq (word : List Bool) :
    decodeRawGate (σ := σ) word = (Circuit.Code.decodeGate σ word).map viewGate := by
  cases word with
  | nil => rfl
  | cons bit word =>
    cases bit with
    | false => simp only [decodeRawGate, Circuit.Code.decodeGate, Option.map_map]; rfl
    | true =>
      cases hp : unpair? word with
      | none => simp [decodeRawGate, decodeFunction, Circuit.Code.decodeGate, hp]
      | some pair =>
        cases ho : decodeOperation σ pair.1 with
        | none => simp [decodeRawGate, decodeFunction, Circuit.Code.decodeGate, hp, ho]
        | some operation =>
          cases hr : Algorithms.LabelDictionary.decode pair.2 with
          | none => simp [decodeRawGate, decodeFunction, Circuit.Code.decodeGate, hp, ho, hr]
          | some refs =>
            by_cases hlen : refs.length = operation.1
            · simp [decodeRawGate, decodeFunction, Circuit.Code.decodeGate, hp, ho, hr, hlen, viewGate]
              apply List.ext_getElem (by simpa only [List.length_ofFn] using hlen)
              intro i hi hi'
              simp
            · simp [decodeRawGate, decodeFunction, Circuit.Code.decodeGate, hp, ho, hr, hlen]

private theorem mapM_decodeRawGate (blocks : List (List Bool)) :
    blocks.mapM (decodeRawGate (σ := σ)) = (blocks.mapM (Circuit.Code.decodeGate σ)).map (List.map viewGate) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    rw [List.mapM_cons, decodeRawGate_eq, List.mapM_cons]
    cases hh : Circuit.Code.decodeGate σ block with
    | none => rfl
    | some gate =>
      rw [ih]
      cases ht : blocks.mapM (Circuit.Code.decodeGate σ) <;> rfl

theorem decodeRawGates_eq (word : List Bool) :
    decodeRawGates (σ := σ) word = (Circuit.Code.decodeGates σ word).map (List.map viewGate) := by
  unfold decodeRawGates Circuit.Code.decodeGates
  cases h : undelimitBlocks word with
  | none => rfl
  | some blocks => exact mapM_decodeRawGate blocks

theorem decodeData_eq (word : List Bool) :
    decodeData (σ := σ) word = (Circuit.Code.decode σ word).map view := by
  unfold decodeData Circuit.Code.decode
  cases hp : unpair? word with
  | none => rfl
  | some pair =>
    rcases pair with ⟨stream, outputs⟩
    dsimp only [Bind.bind, Pure.pure, Option.bind]
    rw [decodeRawGates_eq]
    cases hg : Circuit.Code.decodeGates σ stream with
    | none => rfl
    | some gates =>
      dsimp only [Option.map, Option.bind]
      cases ho : unpair? outputs with
      | none => rfl
      | some outputPair =>
        rcases outputPair with ⟨leftCode, rightCode⟩
        dsimp only [Bind.bind, Pure.pure, Option.bind]
        cases hl : BinaryNatCode.decode? leftCode <;> cases hr : BinaryNatCode.decode? rightCode <;> rfl


set_option maxHeartbeats 1200000 in
private theorem decodeFunction_polyTime : ComputableInPolyTime (decodeFunction (σ := σ)) encBits
    (encOption (encPair FiniteTermMachines.operationEncoding (encList encNat))) := by
  let outer := encPair encBits (encPair encBits encBits)
  have hop : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => decodeOperation σ p.2.1)
      outer (encOption FiniteTermMachines.operationEncoding) :=
    FiniteTermMachines.decodeOperation_polyTime.comp (by fun_prop)
  have hrefs : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => Algorithms.LabelDictionary.decode p.2.2)
      outer (encOption (encList encNat)) := Dictionary.dictionary_decode_polyTime.comp (by fun_prop)
  have hpair := optionPairWithInput_polyTime hop hrefs
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => (decodeOperation σ p.1).bind
      (fun operation => (Algorithms.LabelDictionary.decode p.2).map (fun refs => (operation, refs))))
    (const none) hpair
  convert h using 1
  funext body
  unfold decodeFunction
  cases hp : unpair? body with
  | none => rfl
  | some p =>
    rcases p with ⟨opcode, word⟩
    change (do
      let operation ← decodeOperation σ opcode
      let refs ← Algorithms.LabelDictionary.decode word
      pure (operation, refs)) = _
    simp only [Option.elim_some]
    cases ho : decodeOperation σ opcode <;> cases hr : Algorithms.LabelDictionary.decode word <;> rfl

theorem decodeRawGate_polyTime : ComputableInPolyTime (decodeRawGate (σ := σ)) encBits (encOption gateEncoding) := by
  have hvar := Dictionary.decode_polyTime.comp bitsTail
  have hj : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
      (encPair encBits encNat) encNat := snd _ _
  have hin : ComputableInPolyTime (fun p : List Bool × ℕ => ((none, (p.2, [])) : RawGate σ))
      (encPair encBits encNat) gateEncoding := (const none).prod (hj.prod (const []))
  have hinput := hvar.optionMapWithInput (f := fun (_ : List Bool) j => ((none, (j, [])) : RawGate σ)) hin
  let inner := encPair encBits (encPair (FiniteTermMachines.operationEncoding (σ := σ)) (encList encNat))
  have hop : ComputableInPolyTime (fun p : List Bool × (Operation σ × List ℕ) => p.2.1)
      inner FiniteTermMachines.operationEncoding := by fun_prop
  have hrefs : ComputableInPolyTime (fun p : List Bool × (Operation σ × List ℕ) => p.2.2)
      inner (encList encNat) := by fun_prop
  have harity : ComputableInPolyTime (fun op : Operation σ => op.1)
      FiniteTermMachines.operationEncoding encUnary := .of_finite _
  have heq := decide_eq' ((length_list encNat).comp hrefs) (harity.comp hop)
  have hrecord : ComputableInPolyTime
      (fun p : List Bool × (Operation σ × List ℕ) => ((some p.2.1, (0, p.2.2)) : RawGate σ))
      inner gateEncoding := ((optionSome FiniteTermMachines.operationEncoding).comp hop).prod ((const 0).prod hrefs)
  have hbody := heq.ite ((optionSome (gateEncoding (σ := σ))).comp hrecord) (const none)
  have hfunction := ((decodeFunction_polyTime (σ := σ)).comp bitsTail).optionElimWithInput
    (body := fun (_ : List Bool) p => if p.2.length = p.1.1 then some (some p.1, (0, p.2)) else none)
    (const none) (by simpa only [Function.comp_def, decide_eq_true_eq] using hbody)
  have h := bitsIsEmpty.ite (const none) ((headD (encA := encBool) (encL := encBits) false).ite hfunction hinput)
  convert h using 1
  funext word
  cases word with
  | nil => rfl
  | cons bit word =>
    cases bit with
    | false => rfl
    | true =>
      change (do
        let p ← decodeFunction (σ := σ) word
        if p.2.length = p.1.1 then some (some p.1, (0, p.2)) else none) =
        (decodeFunction (σ := σ) word).elim none
          (fun p => if p.2.length = p.1.1 then some (some p.1, (0, p.2)) else none)
      cases hf : decodeFunction (σ := σ) word with
      | none => rfl
      | some p => rcases p with ⟨operation, refs⟩; rfl

theorem decodeRawGates_polyTime : ComputableInPolyTime (decodeRawGates (σ := σ)) encBits (encOption (encList gateEncoding)) := by
  have hgates : ComputableInPolyTime (fun blocks : List (List Bool) => blocks.mapM (decodeRawGate (σ := σ)))
      (encList encBits) (encOption (encList gateEncoding)) :=
    mapMWithInput_polyTime id' (decodeRawGate_polyTime.comp (snd _ _)) (none, (0, []))
  have hbody := hgates.comp (snd encBits (encList encBits))
  have h := BlockScan.undelimitBlocks_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) blocks => blocks.mapM (decodeRawGate (σ := σ))) (const none) hbody
  convert h using 1
  funext word
  unfold decodeRawGates
  cases undelimitBlocks word <;> rfl


private def decodeOutputs (word : List Bool) : Option (ℕ × ℕ) := do
  let (leftCode, rightCode) ← unpair? word
  let left ← BinaryNatCode.decode? leftCode
  let right ← BinaryNatCode.decode? rightCode
  return (left, right)

private theorem decodeOutputs_polyTime : ComputableInPolyTime decodeOutputs encBits (encOption (encPair encNat encNat)) := by
  let outer := encPair encBits (encPair encBits encBits)
  have hl : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => BinaryNatCode.decode? p.2.1)
      outer (encOption encNat) := Dictionary.decode_polyTime.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => BinaryNatCode.decode? p.2.2)
      outer (encOption encNat) := Dictionary.decode_polyTime.comp (by fun_prop)
  have hp := optionPairWithInput_polyTime hl hr
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => (BinaryNatCode.decode? p.1).bind
      (fun left => (BinaryNatCode.decode? p.2).map (fun right => (left, right)))) (const none) hp
  convert h using 1
  funext word
  unfold decodeOutputs
  cases hp : unpair? word with
  | none => rfl
  | some p =>
    rcases p with ⟨leftCode, rightCode⟩
    change (do
      let left ← BinaryNatCode.decode? leftCode
      let right ← BinaryNatCode.decode? rightCode
      pure (left, right)) = _
    simp only [Option.elim_some]
    cases hl : BinaryNatCode.decode? leftCode <;> cases hr : BinaryNatCode.decode? rightCode <;> rfl

theorem decodeData_polyTime : ComputableInPolyTime (decodeData (σ := σ)) encBits (encOption dataEncoding) := by
  let outer := encPair encBits (encPair encBits encBits)
  have hg : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => decodeRawGates (σ := σ) p.2.1)
      outer (encOption (encList gateEncoding)) := decodeRawGates_polyTime.comp (by fun_prop)
  have hout : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => decodeOutputs p.2.2)
      outer (encOption (encPair encNat encNat)) := decodeOutputs_polyTime.comp (by fun_prop)
  have hp := optionPairWithInput_polyTime hg hout
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => (decodeRawGates (σ := σ) p.1).bind
      (fun gates => (decodeOutputs p.2).map (fun outputs => (gates, outputs)))) (const none) hp
  convert h using 1
  funext word
  unfold decodeData
  cases hp : unpair? word with
  | none => rfl
  | some p =>
    rcases p with ⟨stream, outputs⟩
    change (do
      let gates ← decodeRawGates (σ := σ) stream
      let outputCodes ← unpair? outputs
      let left ← BinaryNatCode.decode? outputCodes.1
      let right ← BinaryNatCode.decode? outputCodes.2
      pure (gates, (left, right))) = _
    simp only [Option.elim_some]
    unfold decodeOutputs
    cases hg : decodeRawGates (σ := σ) stream with
    | none => rfl
    | some gates =>
      cases ho : unpair? outputs with
      | none => rfl
      | some codes =>
        rcases codes with ⟨leftCode, rightCode⟩
        change (do
          let left ← BinaryNatCode.decode? leftCode
          let right ← BinaryNatCode.decode? rightCode
          pure (gates, (left, right))) = _
        dsimp only [Bind.bind, Pure.pure, Option.bind]
        cases hl : BinaryNatCode.decode? leftCode <;> cases hr : BinaryNatCode.decode? rightCode <;> rfl

end KFOL.Complexity.CircuitMachine
