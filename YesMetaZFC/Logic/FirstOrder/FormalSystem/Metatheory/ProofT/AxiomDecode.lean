import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacket

/-! # 按公理呈现结构组合的可计算解码器 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

/-- 解码成功即获得原有公理证书，不要求输入理论成员证明。 -/
abbrev AxiomDecoder {T : SetTheory} (presentation : AxiomPresentation T) :=
  Tree → Option presentation.Certificate

namespace AxiomDecoder
/-- 固定公理的唯一合法数据树是零叶子。 -/
def singleton (formula : SetSentence) : AxiomDecoder (AxiomPresentation.singleton formula)
  | .node 0 [] => some ()
  | _ => none

/-- 理论并保留左右分支，标签分别是零和一。 -/
def union {T U : SetTheory} {left : AxiomPresentation T} {right : AxiomPresentation U}
    (decodeLeft : AxiomDecoder left) (decodeRight : AxiomDecoder right) :
    AxiomDecoder (AxiomPresentation.union left right)
  | .node 0 [child] => (decodeLeft child).map Sum.inl
  | .node 1 [child] => (decodeRight child).map Sum.inr
  | _ => none

def insert (formula : SetSentence) {T : SetTheory} {presentation : AxiomPresentation T}
    (decoder : AxiomDecoder presentation) : AxiomDecoder (AxiomPresentation.insert formula presentation) :=
  union (singleton formula) decoder

/-- 参数索引先解码，再在其依赖证书族中递归。 -/
def indexed {Index : Type} {family : Index → SetTheory}
    {presentations : ∀ index, AxiomPresentation (family index)}
    (decodeIndex : Tree → Option Index) (decoders : ∀ index, AxiomDecoder (presentations index)) :
    AxiomDecoder (AxiomPresentation.indexed presentations)
  | .node 0 [indexTree, child] => do
      let index ← decodeIndex indexTree
      let certificate ← decoders index child
      return ⟨index, certificate⟩
  | _ => none
end AxiomDecoder
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
