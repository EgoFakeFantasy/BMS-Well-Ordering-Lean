import BMSConstructibleBridge.SecondOrderStageIndexOrder
import BMSConstructibleBridge.SecondOrderComparisonInvariant
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 实际前驱归纳假设填满极限比较保持

从真实配置及每个前驱的不变量推出相容性和阶段良序，再把全历史函数
限制到同一前驱域。没有将“前驱历史相容”另作假设；极限输出仍是原正文
的同一个输出。这里只完成极限归纳分支，不是最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitInvariant

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderCoherentUnion (stage_l extension_l)
open SecondOrderComparisonNativeRow (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

set_option maxHeartbeats 1000000 in
theorem order_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    {A : SecondOrderGraph.code_l ℳ} {B F r G q δ D X Q : type_l hℳ}
    {Root Index Prec : SecondOrderModel.set_l ℳ}
    (hConfig : SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Root Index Prec)
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r (v p.C) (v p.f) (v p.P₀))
    (hG : map_l (ℳ := 𝒱) G K.omega q)
    (hδ : subset_l (ℳ := 𝒱) δ (v A))
    (hD : SecondOrderStageLayerFunction.predecessor_l δ (v p.J) D)
    (hUnion : PowerlessRelativeHierarchySemantics.union_l hℳ F δ X)
    (hIH : ∀ b, mem_l hℳ b δ →
      SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G b)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hOutput : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱)
      K.omega (zero_l K) D (v p.T) G (v p.f) U.val)
    (hQ : SecondOrderComparisonDecode.graph_l K (v p.C) (v p.f) W Q) :
    wellOrder_l (ℳ := 𝒱) X Q ∧ ∀ i Y R,
      stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G i Y R →
      (∃ b, value_l (ℳ := 𝒱) (v p.J) i b ∧ mem_l hℳ b δ) →
      extension_l (ℳ₀ := 𝒱) Y R X Q := by
  have hDI : subset_l (ℳ := 𝒱) D (v p.I) := by
    intro i hi
    obtain ⟨b, hib, _⟩ := (hD i).mp hi
    exact (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.indexMap hib).1
  obtain ⟨N, hN, hNRead⟩ := SecondOrderStageIndexOrder.exists_l
    (hℳ := hℳ) hConfig.ordinal hConfig.indexMap hConfig.indexInjective
  have hND : wellOrder_l (ℳ := 𝒱) D N := PowerlessRelativeClassAmbientWellOrder.of_subset_l hN hDI
  obtain ⟨T', hT', hTRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hConfig.layerMap hDI
  obtain ⟨G', hG', hGRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hG
    (fun i hi => hConfig.indexSubset i (hDI i hi))
  have hStage (i Y R : type_l hℳ) : stage_l (ℳ₀ := 𝒱) D T' G' i Y R ↔
      mem_l hℳ i D ∧ value_l (ℳ := 𝒱) (v p.T) i Y ∧ value_l (ℳ := 𝒱) G i R := by
    constructor
    · rintro ⟨hi, hiY, hiR⟩
      exact ⟨hi, ((hTRead i Y).mp hiY).2, ((hGRead i R).mp hiR).2⟩
    · rintro ⟨hi, hiY, hiR⟩
      exact ⟨hi, (hTRead i Y).mpr ⟨hi, hiY⟩, (hGRead i R).mpr ⟨hi, hiR⟩⟩
  have hStages : ∀ i Y R, stage_l (ℳ₀ := 𝒱) D T' G' i Y R → wellOrder_l (ℳ := 𝒱) Y R := by
    intro i Y R hi
    obtain ⟨hiD, hiY, hiR⟩ := (hStage i Y R).mp hi
    obtain ⟨b, hib, hb⟩ := (hD i).mp hiD
    exact (hIH b hb i Y R ⟨⟨hDI i hiD, hiY, hiR⟩, hib⟩).1
  have hCoherent : SecondOrderWellOrderCoherentUnion.coherent_l (ℳ₀ := 𝒱) D N T' G' := by
    intro i j Y R Z S hi hj hij
    obtain ⟨hiD, hiY, hiR⟩ := (hStage i Y R).mp hi
    obtain ⟨hjD, hjZ, hjS⟩ := (hStage j Z S).mp hj
    obtain ⟨b, c, hib, hjc, hbc⟩ := (hNRead i j (hDI i hiD) (hDI j hjD)).mp hij
    obtain ⟨c', hjc', hc'⟩ := (hD j).mp hjD
    have hEq := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.indexMap hjc' hjc
    have hc : mem_l hℳ c δ := hEq ▸ hc'
    exact (hIH c hc j Z S ⟨⟨hDI j hjD, hjZ, hjS⟩, hjc⟩).2 i Y R
      ⟨⟨hDI i hiD, hiY, hiR⟩, b, hib, hbc⟩
  have hCover := SecondOrderStageLayerFunction.limit_cover_l hConfig.indexMap hConfig.indexOnto
    hδ hD hConfig.layerRead hUnion
  have hCover' : SecondOrderWellOrderCoherentUnion.cover_l (ℳ₀ := 𝒱) X D T' := by
    intro x
    refine (hCover x).trans ⟨?_, ?_⟩
    · rintro ⟨i, Y, hi, hiY, hx⟩
      exact ⟨i, Y, hi, (hTRead i Y).mpr ⟨hi, hiY⟩, hx⟩
    · rintro ⟨i, Y, hi, hiY, hx⟩
      exact ⟨i, Y, hi, ((hTRead i Y).mp hiY).2, hx⟩
  have hXC : subset_l (ℳ := 𝒱) X (v p.C) := by
    intro x hx
    obtain ⟨b, Y, _, hbY, hxY⟩ := (hUnion x).mp hx
    exact hSupport.layers Y (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.hierarchy.1 hbY).2 x hxY
  have hOutput' : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱)
      K.omega (zero_l K) D T' G' (v p.f) U.val := by
    obtain ⟨L, hGraph, hEncoded⟩ := hOutput
    refine ⟨L, fun z => (hGraph z).trans ?_, hEncoded⟩
    apply exists_congr
    intro x
    apply exists_congr
    intro y
    apply and_congr _ Iff.rfl
    constructor
    · rintro ⟨i, Y, R, hi, hx, hy, hxy⟩
      exact ⟨i, Y, R, (hStage i Y R).mpr hi, hx, hy, hxy⟩
    · rintro ⟨i, Y, R, hi, hx, hy, hxy⟩
      exact ⟨i, Y, R, (hStage i Y R).mp hi, hx, hy, hxy⟩
  obtain ⟨hOrder, hInitial⟩ := SecondOrderComparisonStagePreservation.limit_order_l K
    (hℳ := hℳ) (C := v p.C) (f := v p.f) (D := X) (I := D) (J := N)
    (F := T') (G := G') (X := r) (Y := q) (Q := Q)
    hSupport.enumeration hSupport.onto hXC hND hT' hG' hCoherent hStages hCover' U W hU hOutput' hQ
  refine ⟨hOrder, ?_⟩
  intro i Y R hi hEarlier
  exact hInitial i Y R ((hStage i Y R).mpr ⟨(hD i).mpr hEarlier, hi.2.1, hi.2.2⟩)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitInvariant
