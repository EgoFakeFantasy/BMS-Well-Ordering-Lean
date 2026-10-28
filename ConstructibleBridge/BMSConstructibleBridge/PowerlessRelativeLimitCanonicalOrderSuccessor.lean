import BMSConstructibleBridge.PowerlessRelativeLimitCanonicalStepCertificate
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalMemberDefStep
import BMSConstructibleBridge.SecondOrderCanonicalOrderUniform

/-! # 同一原规范后继输出的实际层界

对象语言为纯隶属 ℒ，背景为原 Z₂ 图商。固定同一 K、标签、配数和合法性
图，实际 Sat 与原 Def 认同产生规范候选；其有限证书在指定极限层 C 内
构造。原环境步骤的唯一性随后认同任意 raw 输出 E，不假设 E 已是 Class。

Sat 的正确性和成员界由调用端的已构造规范 Sat 函数读取，并非最终 BMS
句的新增公理。本模块提供预算归纳的真实后继步骤，不构造长历史、统一
枚举族或完整 Collection，也不把此语义辅助结果当作最终对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalOrderSuccessor

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒞" => structure_l hℳ B hBase

variable (hBase)

theorem member_l (K : source_coding_l hℳ) {β C E : SecondOrderQuotient.type_l hℳ}
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω A P e t₁ t₂ t₃ Pair Valid Sat D : type_l hℳ B)
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid Sat)
    (hDef : SecondOrderMemberDef.spec_l hℳ A.val D.val)
    (hωC : mem_l hℳ ω.val C) (hAC : mem_l hℳ A.val C)
    (hPC : mem_l hℳ P.val C) (hSatC : mem_l hℳ Sat.val C)
    (hDC : mem_l hℳ D.val C) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hStep : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
      ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E) :
    mem_l hℳ E C ∧
      PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱)
        C ω.val A.val P.val Sat.val D.val E ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B E ∧
      wellOrder_l (ℳ := 𝒱) D.val E := by
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  obtain ⟨L, hCandidate⟩ := PowerlessRelativeClassCanonicalMemberDefStep.of_spec_l
    K hΩ hP hω he hTags hPairMap hPair hV hValid hSat hDef
  obtain ⟨E', hE'C, hBounded, hClassStep, hOrder⟩ :=
    PowerlessRelativeLimitCanonicalStepCertificate.exists_l hBase hLimit hC
      ω A P Sat D (hω.symm ▸ K.omega_spec) hωC hAC hPC hSatC hDC hP ⟨L, hCandidate⟩
  have hRaw : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
      ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E'.val :=
    SecondOrderCanonicalOrderUniform.step_ambient_l K hω he hPairMap hPair ⟨Sat, hSat, hClassStep⟩
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  have hEq : E = E'.val := SecondOrderCanonicalOrderUniform.unique_l
    K hω he ht₁ ht₂ ht₃ hPairMap hPair hV hValid hStep hRaw
  rw [hEq]
  exact ⟨hE'C, hBounded, E'.property, hOrder⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalOrderSuccessor
