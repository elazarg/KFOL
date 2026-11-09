module
public import KFOL.Algorithms.FullTermCode
public import KFOL.Complexity.FiniteTermMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
@[expose] public section
namespace KFOL.Complexity.FullTermMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
noncomputable def termEncoding : Raw ↪ List Bool := ⟨encode, encode_injective⟩
noncomputable def operationEncoding : Operation ↪ List Bool := ⟨encodeOperation, encodeOperation_injective⟩
theorem encode_polyTime : ComputableInPolyTime encode termEncoding encBits := .of_eq (fun _ => rfl)
theorem var_polyTime : ComputableInPolyTime (fun j : ℕ => (.var j : Raw)) encNat termEncoding := by
  have h := bitsCons (const false) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime)
  exact h.of_enc_eq (fun _ => rfl)
noncomputable def construct (operation : Operation) (children : List Raw) : Raw :=
  .func operation.2 (fun i => children.getD i.val (.var 0))
theorem construct_ofFn {n : ℕ} (function : RawSymbol n) (children : Fin n → Raw) :
    construct ⟨n,function⟩ (List.ofFn children) = .func function children := by
  unfold construct
  congr 1
  funext i
  simp

theorem arity_polyTime : ComputableInPolyTime (fun operation : Operation => operation.1) operationEncoding encUnary := by
  have hc : ComputableInPolyTime encodeOperation operationEncoding encBits := .of_eq (fun _ => rfl)
  have hfirst := (headD (encA := encBool) (encL := encBits) false).comp hc
  have hsecond := (headD (encA := encBool) (encL := encBits) false).comp (bitsTail.comp hc)
  have h := hfirst.ite (const (encOut := encUnary) 1) (hsecond.ite (const 2) (const 0))
  convert h using 1
  funext operation
  rcases operation with ⟨n,symbol⟩
  cases symbol <;> rfl

private def arityTag (operation : Operation) : Fin 3 := ⟨operation.1, by have h := arity_le_two operation; omega⟩
private def arityEncoding : Fin 3 ↪ List Bool := ⟨fun i => encUnary i.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩
private def constructWord (n : Fin 3) (input : Operation × List Raw) : List Bool :=
  true :: (Words.delimit (encodeOperation input.1) ++ (List.ofFn (fun i : Fin n.val => encode (input.2.getD i.val (.var 0)))).flatten)

private theorem constructWord_polyTime (n : Fin 3) : ComputableInPolyTime (constructWord n)
    (encPair operationEncoding (encList termEncoding)) encBits := by
  have hc : ComputableInPolyTime (fun p : Operation × List Raw => encodeOperation p.1)
      (encPair operationEncoding (encList termEncoding)) encBits := (ComputableInPolyTime.of_eq (encIn := operationEncoding) (encOut := encBits) (fun _ => rfl)).comp (fst operationEncoding (encList termEncoding))
  have hchild : ∀ i : Fin n.val, ComputableInPolyTime
      (fun p : Operation × List Raw => encode (p.2.getD i.val (.var 0)))
      (encPair operationEncoding (encList termEncoding)) encBits := by
    intro i
    exact encode_polyTime.comp ((listGetD (encA := termEncoding) (encL := encList termEncoding) (.var 0)).comp
      ((snd operationEncoding (encList termEncoding)).prod (const i.val)))
  exact bitsCons (const true) (bitsAppend (Framing.delimit_polyTime.comp hc) (bitsFlatten (ComputableInPolyTime.ofFn hchild)))

theorem construct_polyTime : ComputableInPolyTime (fun p : Operation × List Raw => construct p.1 p.2)
    (encPair operationEncoding (encList termEncoding)) termEncoding := by
  have ht : ComputableInPolyTime (fun p : Operation × List Raw => arityTag p.1)
      (encPair operationEncoding (encList termEncoding)) arityEncoding :=
    (arity_polyTime.comp (fst _ _)).of_enc_eq (fun _ => rfl)
  have h := ht.finite_cases (branch := fun n p => constructWord n p) constructWord_polyTime
  exact h.of_enc_eq (fun _ => rfl)

private theorem dictionary_encode_polyTime : ComputableInPolyTime Algorithms.LabelDictionary.encode (encList encNat) encBits := by
  have hlabel := (Framing.delimit_polyTime.comp Dictionary.encode_polyTime).comp (snd (encList encNat) encNat)
  have h := flatMapToBitsWithInput (f := fun (_ : List ℕ) j => Words.delimit (Words.BinaryNatCode.encode j)) id' hlabel
  convert h using 1
  funext labels
  simp only [Algorithms.LabelDictionary.encode, List.map_map, List.flatMap_def, Function.comp_def]

theorem winnerOperation_polyTime : ComputableInPolyTime (fun r : ℕ => (⟨0,.winner r⟩ : Operation)) encNat operationEncoding := by
  have h := bitsCons (const false) (bitsCons (const false) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime))
  exact h.of_enc_eq (fun _ => rfl)
theorem choiceOperation_polyTime : ComputableInPolyTime (fun r : ℕ => (⟨2,.choice r⟩ : Operation)) encNat operationEncoding := by
  have h := bitsCons (const false) (bitsCons (const true) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime))
  exact h.of_enc_eq (fun _ => rfl)
theorem renameOperation_polyTime : ComputableInPolyTime (fun p : List ℕ => (⟨1,.rename p⟩ : Operation)) (encList encNat) operationEncoding := by
  have h := bitsCons (const true) (bitsCons (const false) (Framing.delimit_polyTime.comp dictionary_encode_polyTime))
  exact h.of_enc_eq (fun _ => rfl)

private theorem operationPayload_polyTime : ComputableInPolyTime operationPayload encBits (encOption encBits) := by
  have hrest : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.2) (encPair encBits (encPair encBits encBits)) encBits := by fun_prop
  have hpayload : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.1) (encPair encBits (encPair encBits encBits)) encBits := by fun_prop
  have hempty := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := encBool))).comp hrest
  have hsome := (optionSome encBits).comp hpayload
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => if p.2.isEmpty then some p.1 else none) (const none)
    (hempty.ite hsome (const none))
  convert h using 1
  funext word
  unfold operationPayload
  cases Words.unpair? word with
  | none => rfl
  | some p => cases p.2.isEmpty <;> rfl

theorem decodeOperation_polyTime : ComputableInPolyTime decodeOperation encBits (encOption operationEncoding) := by
  have htail : ComputableInPolyTime (fun word : List Bool => word.tail.tail) encBits encBits := bitsTail.comp bitsTail
  have hp := operationPayload_polyTime.comp htail
  have hn := hp.optionElimWithInput (body := fun (_ : List Bool) payload => Words.BinaryNatCode.decode? payload)
    (const none) (Dictionary.decode_polyTime.comp (snd encBits encBits))
  have hl := hp.optionElimWithInput (body := fun (_ : List Bool) payload => Algorithms.LabelDictionary.decode payload)
    (const none) (Dictionary.dictionary_decode_polyTime.comp (snd encBits encBits))
  have hw := hn.optionMapWithInput (f := fun (_ : List Bool) r => (⟨0,.winner r⟩ : Operation))
    (winnerOperation_polyTime.comp (snd encBits encNat))
  have hc := hn.optionMapWithInput (f := fun (_ : List Bool) r => (⟨2,.choice r⟩ : Operation))
    (choiceOperation_polyTime.comp (snd encBits encNat))
  have hr := hl.optionMapWithInput (f := fun (_ : List Bool) array => (⟨1,.rename array⟩ : Operation))
    (renameOperation_polyTime.comp (snd encBits (encList encNat)))
  have hfirst := headD (encA := encBool) (encL := encBits) false
  have hsecond := hfirst.comp bitsTail
  have htwo := unary_le.comp ((const 2).prod length_bits)
  have h := htwo.ite (hfirst.ite (hsecond.ite (const none) hr) (hsecond.ite hc hw)) (const none)
  convert h using 1
  funext word
  cases word with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => cases first <;> rfl
    | cons second rest =>
      cases first <;> cases second <;>
        simp only [decodeOperation, Function.comp_def, List.tail_cons, List.headD_cons,
          List.length_cons, decide_eq_true_eq, Nat.reduceLeDiff, ite_true, Bool.false_eq_true,
          ite_false]
      all_goals
        cases operationPayload rest with
        | none => rfl
        | some payload =>
          first
          | change (Words.BinaryNatCode.decode? payload).bind (fun r => some (⟨0,.winner r⟩ : Operation)) =
              (Words.BinaryNatCode.decode? payload).map (fun r => (⟨0,.winner r⟩ : Operation))
            cases Words.BinaryNatCode.decode? payload <;> rfl
          | change (Words.BinaryNatCode.decode? payload).bind (fun r => some (⟨2,.choice r⟩ : Operation)) =
              (Words.BinaryNatCode.decode? payload).map (fun r => (⟨2,.choice r⟩ : Operation))
            cases Words.BinaryNatCode.decode? payload <;> rfl
          | change (Algorithms.LabelDictionary.decode payload).bind (fun r => some (⟨1,.rename r⟩ : Operation)) =
              (Algorithms.LabelDictionary.decode payload).map (fun r => (⟨1,.rename r⟩ : Operation))
            cases Algorithms.LabelDictionary.decode payload <;> rfl

/-- A public finite control tag records the fixed arity, without enumerating
the infinite label/array operation alphabet. -/
def operationKind (operation : Operation) : Fin 3 :=
  ⟨operation.1,by have h := arity_le_two operation; omega⟩
def kindEncoding : Fin 3 ↪ List Bool :=
  ⟨fun i => encUnary i.val,fun _ _ h => Fin.ext (encUnary.injective h)⟩

theorem operationKind_polyTime : ComputableInPolyTime operationKind operationEncoding kindEncoding :=
  arity_polyTime.of_enc_eq (fun _ => rfl)

/-- The stored role label; rename nodes have no such label. -/
def roleLabel : Operation → ℕ
  | ⟨_, .winner role⟩ => role
  | ⟨_, .choice owner⟩ => owner
  | ⟨_, .rename _⟩ => 0

/-- The physically stored array; winner/choice nodes have no such array. -/
def forwardArray : Operation → List ℕ
  | ⟨_, .winner _⟩ => []
  | ⟨_, .choice _⟩ => []
  | ⟨_, .rename forward⟩ => forward

theorem roleLabel_polyTime : ComputableInPolyTime roleLabel operationEncoding encNat := by
  have hc : ComputableInPolyTime encodeOperation operationEncoding encBits := .of_eq (fun _ => rfl)
  have hp := operationPayload_polyTime.comp (bitsTail.comp (bitsTail.comp hc))
  have hn := hp.optionElimWithInput
    (body := fun (_ : Operation) payload => Words.BinaryNatCode.decode? payload)
    (const none) (Dictionary.decode_polyTime.comp (snd operationEncoding encBits))
  have hv := hn.optionGetDWithInput (const 0)
  have htest := decide_eq' operationKind_polyTime (const (1:Fin 3))
  have h := htest.ite (const 0) hv
  convert h using 1
  funext operation
  rcases operation with ⟨n,symbol⟩
  cases symbol <;> simp [Function.comp_def,roleLabel,operationKind,encodeOperation]

theorem forwardArray_polyTime : ComputableInPolyTime forwardArray operationEncoding (encList encNat) := by
  have hc : ComputableInPolyTime encodeOperation operationEncoding encBits := .of_eq (fun _ => rfl)
  have hp := operationPayload_polyTime.comp (bitsTail.comp (bitsTail.comp hc))
  have hn := hp.optionElimWithInput
    (body := fun (_ : Operation) payload => Algorithms.LabelDictionary.decode payload)
    (const none) (Dictionary.dictionary_decode_polyTime.comp (snd operationEncoding encBits))
  have hv := hn.optionGetDWithInput (const [])
  have htest := decide_eq' operationKind_polyTime (const (1:Fin 3))
  have h := htest.ite hv (const [])
  convert h using 1
  funext operation
  rcases operation with ⟨n,symbol⟩
  cases symbol <;> simp [Function.comp_def,forwardArray,operationKind,encodeOperation]

end KFOL.Complexity.FullTermMachines
