import BMSConstructibleBridge.PowerlessRelativeLimitFiniteSequencesDirect
import BMSConstructibleBridge.PowerlessRelativeLimitTriangular
import BMSConstructibleBridge.PowerlessRelativeLimitValidity
import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax

/-! # 含 ω 的指定极限层中的完整静态编码包

空集和标签是原 K 的有限数码；Seq(ω)、三角图、合法性图逐个实际放回
给定层。静态规格仍在原相对类解释，不预设该层的完整源理论模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitStaticCoding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem exists_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω : type_l hℳ B) (hωC : mem_l hℳ ω.val C) (hωEq : ω.val = K.omega) :
    ∃ e t₁ t₂ t₃ T N F : type_l hℳ B,
      mem_l hℳ e.val C ∧ mem_l hℳ t₁.val C ∧ mem_l hℳ t₂.val C ∧ mem_l hℳ t₃.val C ∧
        mem_l hℳ T.val C ∧ mem_l hℳ N.val C ∧ mem_l hℳ F.val C ∧
          PowerlessSatisfactionExistenceSyntax.static_l («𝒩» := 𝒩) ω e t₁ t₂ t₃ T N F := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  let num (n : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
    ⟨(numberCode_l K n).val, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hωEq.symm ▸ (numberCode_l K n).property)⟩
  have hNumC (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (num n).val C :=
    hTrans ω.val hωC (num n).val (hωEq.symm ▸ (numberCode_l K n).property)
  let n₀ := SecondOrderModel.zero_l ℳ
  let n₁ := SecondOrderModel.succ_l n₀
  let n₂ := SecondOrderModel.succ_l n₁
  let n₃ := SecondOrderModel.succ_l n₂
  let e := num n₀
  let t₁ := num n₁
  let t₂ := num n₂
  let t₃ := num n₃
  have hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒩) e t₁ t₂ t₃ :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mpr
      (PowerlessBMSQuotientSuccessor.zero_l K),
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mpr
        (PowerlessBMSQuotientSuccessor.successor_l K n₀),
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mpr
        (PowerlessBMSQuotientSuccessor.successor_l K n₁),
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mpr
        (PowerlessBMSQuotientSuccessor.successor_l K n₂)⟩
  obtain ⟨s, hsC, hs⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l hBase hLimit hC
    (hωEq.symm ▸ K.omega_spec) hωC hωC
  let N : type_l hℳ B := ⟨s, ⟨β, C, hC, hsC⟩⟩
  have hNRaw : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val := by
    simpa only [hωEq] using hs
  obtain ⟨T, hTC, hT, hMap, hSpec⟩ := PowerlessRelativeLimitTriangular.exists_l
    (hBase := hBase) K hLimit hC ω e N hωC (hNumC n₀) hsC hωEq rfl hNRaw
  obtain ⟨f, hfC, hf⟩ := PowerlessRelativeLimitValidity.query_exists_l hBase hLimit hC
    hωC (hNumC n₀) hsC hTC (hNumC n₁) (hNumC n₂) (hNumC n₃)
  let F : type_l hℳ B := ⟨f, ⟨β, C, hC, hfC⟩⟩
  have hValid : PowerlessFormulaValiditySpecification.spec_l («𝒩» := 𝒩) ω e N T t₁ t₂ t₃ F := by
    intro c l
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c l).trans
      ((hf c.val l.val).trans (PowerlessFormulaValiditySpecification.query_absolute_l
        (hBase := hBase) ω e N T t₁ t₂ t₃ c l).symm)
  have hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω ω N := fun a =>
    (hs a.val).trans (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l
      (hBase := hBase) ω ω a).symm
  exact ⟨e, t₁, t₂, t₃, T, N, F, hNumC n₀, hNumC n₁, hNumC n₂, hNumC n₃,
    hTC, hsC, hfC, hTags, hT,
    PowerlessRelativeClassConstructorTotal.functional_of_spec_l K hωEq rfl hMap hSpec, hN, hValid⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitStaticCoding
