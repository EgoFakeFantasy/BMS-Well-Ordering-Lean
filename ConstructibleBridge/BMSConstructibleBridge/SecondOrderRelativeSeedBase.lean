import BMSConstructibleBridge.SecondOrderRootNormalization
import BMSConstructibleBridge.SecondOrderPairSet
import BMSConstructibleBridge.SecondOrderTransitiveSuperset

/-! # 同时保持两个指定对象的传递零根基图

先将两对象配对，再取传递超集，最后作零根规范化。可分别用于候选实数
和内部 ω；所有见证留在命题存在式中，没有抽取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeSeedBase

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (X Y : SecondOrderGraph.code_l ℳ) :
    ∃ B : set_l ℳ, ∃ hB : SecondOrderDomain.wf_l B (zero_l ℳ),
      SecondOrderGraph.mem_l X ⟨B, zero_l ℳ, hB⟩ ∧
      SecondOrderGraph.mem_l Y ⟨B, zero_l ℳ, hB⟩ ∧
      SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩ := by
  obtain ⟨C, hC⟩ := SecondOrderPairSet.exists_l hℳ X Y
  obtain ⟨T, hCT, hTrans⟩ := SecondOrderTransitiveSuperset.exists_l hℳ C
  obtain ⟨B, hB, hEq⟩ := SecondOrderRootNormalization.normal_exists_l hℳ T
  let A : SecondOrderGraph.code_l ℳ := ⟨B, zero_l ℳ, hB⟩
  have hMembers (Z : SecondOrderGraph.code_l ℳ) : SecondOrderGraph.mem_l Z A ↔ SecondOrderGraph.mem_l Z T :=
    SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ Z) hEq
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · exact (hMembers X).mpr (hTrans C X hCT ((hC X).mpr (Or.inl (SecondOrderGraph.refl_l hℳ X))))
  · exact (hMembers Y).mpr (hTrans C Y hCT ((hC Y).mpr (Or.inr (SecondOrderGraph.refl_l hℳ Y))))
  · intro U V hU hV
    exact (hMembers V).mpr (hTrans U V ((hMembers U).mp hU) hV)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeSeedBase
