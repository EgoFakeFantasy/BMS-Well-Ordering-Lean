import BMSConstructibleBridge.PowerlessFiniteEvaluationQuery
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps

/-! # 用给定非零极限层本身界定有限求值历史

有限历史检查显式包含从内部有限长度到该层的映射规格。每条这样的
映射本身属于该层，所以稳定查询中的全有限序列集可以换成该层本身。
这里只替换候选历史的成员守卫，不声称整个序列集属于该层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationHistoryBound

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 全部原商查询坐标上成立；候选历史的内部长度不要求外部标准。 -/
theorem query_iff_l (K : source_coding_l hℳ)
    {B β C e N T A S t₁ t₂ t₃ Q k f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hωC : mem_l hℳ K.omega C)
    (hQ : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega C Q) :
    PowerlessFiniteEvaluationQuery.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C K.omega e N T A S t₁ t₂ t₃ Q k f ↔
    PowerlessFiniteEvaluationQuery.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C K.omega e N T A S t₁ t₂ t₃ C k f := by
  constructor
  · rintro ⟨m, hm, H, _, hk, hHistory, hQuery⟩
    have hHC : mem_l hℳ H C :=
      PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase hLimit hC K hωC
        (fun _ hx => hx) hm hHistory.1
    exact ⟨m, hm, H, hHC, hk, hHistory, hQuery⟩
  · rintro ⟨m, hm, H, _, hk, hHistory, hQuery⟩
    exact ⟨m, hm, H, (hQ H).mpr ⟨m, hm, hHistory.1⟩, hk, hHistory, hQuery⟩

#print axioms query_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationHistoryBound
