import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomDecode

/-! # 公理呈现的逆向编码合同及组合 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

/-- 编码函数连同其相对于既有解码器的左逆定理。 -/
structure AxiomCodec {T : SetTheory} {presentation : AxiomPresentation T}
    (decoder : AxiomDecoder presentation) where
  encode : presentation.Certificate → Tree
  roundtrip : ∀ certificate, decoder (encode certificate) = some certificate

namespace AxiomCodec

def singleton (formula : SetSentence) : AxiomCodec (AxiomDecoder.singleton formula) where
  encode := fun _ => leaf 0
  roundtrip := fun certificate => by cases certificate; rfl

def union {T U : SetTheory} {left : AxiomPresentation T} {right : AxiomPresentation U}
    {decodeLeft : AxiomDecoder left} {decodeRight : AxiomDecoder right}
    (leftCodec : AxiomCodec decodeLeft) (rightCodec : AxiomCodec decodeRight) :
    AxiomCodec (AxiomDecoder.union decodeLeft decodeRight) where
  encode := fun certificate => match certificate with
    | .inl value => .node 0 [leftCodec.encode value]
    | .inr value => .node 1 [rightCodec.encode value]
  roundtrip := by
    intro certificate
    cases certificate with
    | inl value => exact congrArg (Option.map Sum.inl) (leftCodec.roundtrip value)
    | inr value => exact congrArg (Option.map Sum.inr) (rightCodec.roundtrip value)

def insert (formula : SetSentence) {T : SetTheory} {presentation : AxiomPresentation T}
    {decoder : AxiomDecoder presentation} (codec : AxiomCodec decoder) :
    AxiomCodec (AxiomDecoder.insert formula decoder) := union (singleton formula) codec

def indexed {Index : Type} {family : Index → SetTheory}
    {presentations : ∀ index, AxiomPresentation (family index)}
    {decodeIndex : Tree → Option Index} {decoders : ∀ index, AxiomDecoder (presentations index)}
    (encodeIndex : Index → Tree) (indexRoundtrip : ∀ index, decodeIndex (encodeIndex index) = some index)
    (codecs : ∀ index, AxiomCodec (decoders index)) :
    AxiomCodec (AxiomDecoder.indexed decodeIndex decoders) where
  encode := fun certificate => .node 0 [encodeIndex certificate.1, (codecs certificate.1).encode certificate.2]
  roundtrip := by
    intro ⟨index, certificate⟩
    change (decodeIndex (encodeIndex index)).bind
      (fun i => (decoders i ((codecs index).encode certificate)).bind (fun c => some (Sigma.mk (β := fun i => (presentations i).Certificate) i c))) = some ⟨index, certificate⟩
    rw [indexRoundtrip]
    change (decoders index ((codecs index).encode certificate)).bind (fun c => some (Sigma.mk (β := fun i => (presentations i).Certificate) index c)) = some ⟨index, certificate⟩
    rw [(codecs index).roundtrip]
    rfl

end AxiomCodec
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
