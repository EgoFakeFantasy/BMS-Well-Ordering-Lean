import BMSConstructibleBridge.PowerlessRelativeLimitRowFamilyBounded
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 指定非零极限层中的精确行族闭包

实际 Class 参数 I、A、Q 均已在指定 W 中。先将 A、I 封装为无序对，
与 Q 共同下降到一个严格较早的真实层 C；两次原 Def 后继仍低于顶层。
行族的既有有限界因此给出 Y∈W，而不是只给 Y∈Def(Def(W))。

规格量化全部 raw 指标与行对象，Y 本身不预先要求 Class，也不要求
A 非空。把行族识别为原 Def(A) 时，空域分支仍须由调用端另外处理。
这里不假设全部 Class 可数、Ω 正规或完整 Collection，不给 member-W
中原 global_m 所需的 ω 枚举，也不宣称统一历史或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRowFamilyClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W Y : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 全 raw 精确行族留在原指定层；所有参数的 W 成员界都是实际输入。 -/
theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {I A Q : type_l hℳ B}
    (hIW : mem_l hℳ I.val W) (hAW : mem_l hℳ A.val W) (hQW : mem_l hℳ Q.val W)
    (hY : ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y ↔
      ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒱) A.val Q.val i Z) :
    mem_l hℳ Y W := by
  -- 无序对将两个参数放进同一有限封装，避免不受顶层约束的 Class 共同界。
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ A.val I.val
  have hPW := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hW hAW hIW hP
  obtain ⟨α, C, hα, hC, hPC, hQC⟩ :=
    PowerlessRelativeLimitClosure.common_l hℳ hBase hLimit hW hPW hQW
  have hTransC := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hAC : mem_l hℳ A.val C := hTransC P hPC A.val ((hP A.val).mpr (Or.inl rfl))
  have hIC : mem_l hℳ I.val C := hTransC P hPC I.val ((hP I.val).mpr (Or.inr rfl))
  obtain ⟨α₁, C₁, hα₁, hC₁, hDef₁⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hα hC
  obtain ⟨α₂, C₂, hα₂, hC₂, hDef₂⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hα₁ hC₁
  have hYC₂ := PowerlessRelativeLimitRowFamilyBounded.member_l (hBase := hBase)
    (Y := Y) hTransC hDef₁ hDef₂ hIC hAC hQC hY
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW Y).mpr
    ⟨α₂, C₂, hα₂, hC₂, hYC₂⟩

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRowFamilyClosure
