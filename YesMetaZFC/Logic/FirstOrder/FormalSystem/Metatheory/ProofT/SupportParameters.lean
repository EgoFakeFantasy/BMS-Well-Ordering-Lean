import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomDecoderShape
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomDecode

/-! # 十一类实际参数化支撑公理的识别入口

每个入口直接取原理论并中的参数分支。这里识别原证书是否合法，
尚不输出其指定闭句的 quotation，也不包含外围重复的 union 路径。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportParameters
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

-- 展开原依赖呈现后，类型检查仍须识别 singleton 与其成员等式定义相同。
attribute [local implicit_reducible] Theory.singleton Theory.union
attribute [local implicit_reducible]
  IntrinsicAxiomCertificate.presentation_relation_domain
  IntrinsicAxiomCertificate.presentation_relation_range
  IntrinsicAxiomCertificate.presentation_cartesian_product
  IntrinsicAxiomCertificate.presentation_relation_converse
  IntrinsicAxiomCertificate.presentation_relation_composition
  IntrinsicAxiomCertificate.presentation_identity
  IntrinsicAxiomCertificate.presentation_mapping_collection
  IntrinsicAxiomCertificate.presentation_index_order_separation
  IntrinsicAxiomCertificate.presentation_power_set_bijection_separation
  IntrinsicAxiomCertificate.presentation_symmetric_difference_separation
  IntrinsicAxiomCertificate.presentation_inductive_core_separation

inductive Kind where
  | domain | range | cartesianProduct | converse | composition | identity
  | mappingCollection | indexOrder | powerSetBijection | symmetricDifference | inductiveCore
  deriving Repr, DecidableEq

def kinds : List Kind := [.domain, .range, .cartesianProduct, .converse, .composition, .identity,
  .mappingCollection, .indexOrder, .powerSetBijection, .symmetricDifference, .inductiveCore]

def Kind.arity : Kind → Nat
  | .domain | .range | .converse | .identity | .powerSetBijection | .inductiveCore => 1
  | .cartesianProduct | .composition | .mappingCollection | .symmetricDifference => 2
  | .indexOrder => 4

/-- 使用原完整解码器，输入被包入其既有的左分支标签。 -/
def actual (kind : Kind) (input : Tree) : Bool :=
  let branch := Tree.node 0 [input]
  match kind with
  | .domain => (IntrinsicAxiomDecode.decode_relation_domain branch).isSome
  | .range => (IntrinsicAxiomDecode.decode_relation_range branch).isSome
  | .cartesianProduct => (IntrinsicAxiomDecode.decode_cartesian_product branch).isSome
  | .converse => (IntrinsicAxiomDecode.decode_relation_converse branch).isSome
  | .composition => (IntrinsicAxiomDecode.decode_relation_composition branch).isSome
  | .identity => (IntrinsicAxiomDecode.decode_identity branch).isSome
  | .mappingCollection => (IntrinsicAxiomDecode.decode_mapping_collection branch).isSome
  | .indexOrder => (IntrinsicAxiomDecode.decode_index_order_separation branch).isSome
  | .powerSetBijection => (IntrinsicAxiomDecode.decode_power_set_bijection_separation branch).isSome
  | .symmetricDifference => (IntrinsicAxiomDecode.decode_symmetric_difference_separation branch).isSome
  | .inductiveCore => (IntrinsicAxiomDecode.decode_inductive_core_separation branch).isSome

/-- 对所有原始输入逐分支相等，包含每个非法字段及缺损尾证书。 -/
theorem actual_eq_decode (kind : Kind) (input : Tree) :
    actual kind input = (SyntaxParameters.decode kind.arity input).isSome := by
  rw [AxiomDecoderShape.parameters_correct]
  cases kind
  all_goals
    dsimp only [actual, Kind.arity, IntrinsicAxiomDecode.decode_relation_domain,
      IntrinsicAxiomDecode.decode_relation_range, IntrinsicAxiomDecode.decode_cartesian_product,
      IntrinsicAxiomDecode.decode_relation_converse, IntrinsicAxiomDecode.decode_relation_composition,
      IntrinsicAxiomDecode.decode_identity, IntrinsicAxiomDecode.decode_mapping_collection,
      IntrinsicAxiomDecode.decode_index_order_separation, IntrinsicAxiomDecode.decode_power_set_bijection_separation,
      IntrinsicAxiomDecode.decode_symmetric_difference_separation, IntrinsicAxiomDecode.decode_inductive_core_separation]
    rw [AxiomDecoderShape.union_left_correct]
    simp only [AxiomDecoderShape.indexed_correct, AxiomDecoderShape.singleton_correct]
    rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportParameters
