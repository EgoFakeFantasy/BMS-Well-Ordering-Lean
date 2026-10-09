import BMSConstructibleBridge.SecondOrderComparisonDecodePreservation
import BMSConstructibleBridge.SecondOrderComparisonStaticSupport

/-! # 编码阶段行在实际解码历史中的良序与初段保持

这些是内部归纳的三个分支引理，不是完整历史不变量。后继分支以真正
旧良序证明原部分图有输出，从而排除缺省分支；极限分支消费前驱相容性。
编码标签的合法性由实际数码取得，不能再作为未填配置条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStagePreservation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderCoherentUnion (extension_l stage_l cover_l graph_l edge_l coherent_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem tags_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid) :
    PowerlessEvaluationTags.tags_l (ℳ := 𝒱) (zero_l K) t₁ t₂ t₃ := by
  rw [hCoding.one, hCoding.two, hCoding.three]
  exact ⟨PowerlessBMSQuotientSuccessor.zero_l K,
    PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ),
    PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderEvaluationRule.numeral_l ℳ 1),
    PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderEvaluationRule.numeral_l ℳ 2)⟩

theorem zero_order_l (K : source_coding_l hℳ) {B r C f P₀ Q : type_l hℳ}
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r C f P₀)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hEncoded : SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) K.omega (zero_l K) U.val f P₀)
    (hQ : SecondOrderComparisonDecode.graph_l K C f W Q) : wellOrder_l (ℳ := 𝒱) B Q :=
  SecondOrderComparisonDecodePreservation.wellOrder_l K hSupport.enumeration hSupport.onto
    ((SecondOrderComparisonEncodeSyntax.reading_l K U W hU f P₀).mp hEncoded)
    hQ hSupport.base hSupport.initialOrder

theorem zero_graph_l (K : source_coding_l hℳ) {B r C f P₀ Q : type_l hℳ}
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r C f P₀)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hEncoded : SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) K.omega (zero_l K) U.val f P₀)
    (hQ : SecondOrderComparisonDecode.graph_l K C f W Q) : Q = P₀ := by
  apply SecondOrderComparisonRoundtrip.decode_encode_l K hSupport.enumeration hSupport.onto
    ?_ ((SecondOrderComparisonEncodeSyntax.reading_l K U W hU f P₀).mp hEncoded) hQ
  intro p hp
  obtain ⟨x, y, hx, hy, hPair⟩ := hSupport.initialBound p hp
  exact ⟨x, y, hSupport.base x hx, hSupport.base y hy, hPair⟩

theorem successor_order_l (K : source_coding_l hℳ)
    {C f A P D Q t₁ t₂ t₃ Pair Valid : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    (hDC : subset_l (ℳ := 𝒱) D C) (hP : wellOrder_l (ℳ := 𝒱) A P)
    (hTrans : ∀ x y, mem_l hℳ x A → mem_l hℳ y x → mem_l hℳ y A)
    (hDef : SecondOrderMemberDef.spec_l hℳ A D)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hOutput : SecondOrderCanonicalOrderComparisonTotalized.output_l (𝒩 := 𝒱)
      K.omega A P (zero_l K) t₁ t₂ t₃ Pair Valid D f U.val)
    (hQ : SecondOrderComparisonDecode.graph_l K C f W Q) :
    wellOrder_l (ℳ := 𝒱) D Q ∧ extension_l (ℳ₀ := 𝒱) A P D Q ∧
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
        K.omega A P (zero_l K) t₁ t₂ t₃ Pair Valid D Q := by
  obtain ⟨V, hV, hValid⟩ := hCoding.valid
  obtain ⟨E, hStep, hOrder, hExtension⟩ := SecondOrderCanonicalOrderAmbientTotal.exists_l
    K rfl rfl (tags_l K hCoding) hCoding.pairMap hCoding.pair hV hValid hP hTrans hDef
  obtain ⟨U₀, hEncoded₀, _⟩ := SecondOrderComparisonStageTotal.encoded_exists_unique_l K f E
  have hExists : ∃ X, SecondOrderCanonicalOrderComparisonSyntax.output_l (𝒩 := 𝒱)
      K.omega A P (zero_l K) t₁ t₂ t₃ Pair Valid D f X := ⟨U₀, E, hStep, hEncoded₀⟩
  obtain ⟨E', hStep', hEncoded⟩ :=
    (SecondOrderCanonicalOrderComparisonTotalized.agrees_l hExists U.val).mp hOutput
  have hEq := SecondOrderCanonicalOrderUniform.unique_l K rfl rfl hCoding.one hCoding.two hCoding.three
    hCoding.pairMap hCoding.pair hV hValid hStep' hStep
  subst E'
  have hW := (SecondOrderComparisonEncodeSyntax.reading_l K U W hU f E).mp hEncoded
  have hDecode := (SecondOrderCanonicalOrderComparison.decode_l K hf hOnto hDC hStep hW).2
  have hQE := SecondOrderComparisonDecode.unique_l K hQ hDecode
  exact ⟨hQE.symm ▸ hOrder, hQE.symm ▸ hExtension, hQE.symm ▸ hStep⟩

theorem limit_graph_l (K : source_coding_l hℳ) {C f D I F G Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    (hDC : subset_l (ℳ := 𝒱) D C) (hCover : cover_l (ℳ₀ := 𝒱) D I F)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hOutput : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱) K.omega (zero_l K) I F G f U.val)
    (hQ : SecondOrderComparisonDecode.graph_l K C f W Q) : graph_l (ℳ₀ := 𝒱) I F G Q := by
  obtain ⟨L, hGraph, hEncoded⟩ := hOutput
  have hBound : ∀ p, mem_l hℳ p L → ∃ x y,
      mem_l hℳ x C ∧ mem_l hℳ y C ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
    intro p hp
    obtain ⟨x, y, ⟨i, A, R, hi, hx, hy, _⟩, hxy⟩ := (hGraph p).mp hp
    exact ⟨x, y, hDC x ((hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩),
      hDC y ((hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩), hxy⟩
  have hW := (SecondOrderComparisonEncodeSyntax.reading_l K U W hU f L).mp hEncoded
  have hQL := SecondOrderComparisonRoundtrip.decode_encode_l K hf hOnto hBound hW hQ
  exact hQL.symm ▸ hGraph

theorem limit_order_l (K : source_coding_l hℳ) {C f D I J F G X Y Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    (hDC : subset_l (ℳ := 𝒱) D C)
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) D I F)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hOutput : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱) K.omega (zero_l K) I F G f U.val)
    (hQ : SecondOrderComparisonDecode.graph_l K C f W Q) :
    wellOrder_l (ℳ := 𝒱) D Q ∧ ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R →
      extension_l (ℳ₀ := 𝒱) A R D Q := by
  have hGraph := limit_graph_l K hf hOnto hDC hCover U W hU hOutput hQ
  obtain ⟨T, hT, hOrder, hRead⟩ := SecondOrderWellOrderCoherentUnion.graph_exists_l
    hJ hF hG hCoherent hStages hCover
  have hTL := SecondOrderWellOrderCoherentUnion.graph_unique_l hT hGraph
  subst T
  refine ⟨hOrder, ?_⟩
  intro i A R hi
  refine ⟨fun x hx => (hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩, ?_, ?_⟩
  · intro x y hx hy
    exact (hRead x y).trans (SecondOrderWellOrderCoherentUnion.restrict_l hJ hG hCoherent hi hx hy)
  · intro x y hx _ hyx
    exact SecondOrderWellOrderCoherentUnion.initial_l hJ hF hCoherent hi hx ((hRead y x).mp hyx)

#print axioms tags_l
#print axioms zero_order_l
#print axioms zero_graph_l
#print axioms successor_order_l
#print axioms limit_graph_l
#print axioms limit_order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStagePreservation
