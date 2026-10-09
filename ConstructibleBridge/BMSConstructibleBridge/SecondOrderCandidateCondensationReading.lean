import BMSConstructibleBridge.SecondOrderCandidateSourceClassSeed
import BMSConstructibleBridge.PowerlessRelativeCandidateCondensationReading

/-! # 真实候选的 source/base 终端条件消去

消费原 ClassSeed.exists_l 返回的同一精确种子和同一首截断，不把 source/base
再列为新假设。输入图族存在树来自既有原 Z₂ 对象存在模式；沿该树读取的
I/T/H/J 保持不变。本模块是候选语义装配，正式消去规则由所导入模块的
Derives 提供；仍未构造完整源公理、严格高度或最终 BMS 对象良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateCondensationReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 实际候选的精确基底资格用于消去终端条件；不要求完整候选源模型。 -/
theorem read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B S Ω W : SecondOrderQuotient.type_l hℳ}
    {A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega}
    {X : ℳ.Carrier .set} (P₀ : PowerlessRelativeClassStructure.type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B₀ C₀ W₀ ω₀ A₀ Q₀ e₀ s₀ s₁ s₂ a₀ P₁ R₀ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hB₀ : B₀.eval η = B) (hω₀ : ω₀.eval η = K.omega)
    (hA₀ : A₀.eval η = A.val) (hW₀ : W₀.eval η = W)
    (h : (PowerlessRelativeSourceFamilyCandidateCondensation.conclusion_m Φ
      B₀ C₀ W₀ ω₀ A₀ Q₀ e₀ s₀ s₁ s₂ a₀ P₁ R₀ τ).satisfies η) :
    (PowerlessRelativeCandidateCondensationReading.conclusion_m Φ B₀ W₀ ω₀
      (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ)).satisfies η := by
  have hBase x hx y hy := hSeed.1.2.1.2.1 x y hx hy
  have hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B₀ ω₀ W₀).satisfies η := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B₀ ω₀ W₀).mpr
    simpa only [hB₀, hω₀, hW₀] using
      (show (∀ x, SecondOrderQuotient.mem_l hℳ x B →
          ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B) ∧
        SecondOrderOmega.omega_l hℳ K.omega ∧
        ∃ α, PowerlessRelativeOrdinalCutoff.first_l B K.omega α ∧
          PowerlessRelativeHierarchySemantics.level_l hℳ B α W from
        ⟨hBase, K.omega_spec, Ω, hΩ, hW⟩)
  have hAdjoin : (SecondOrderFunctionAppendDerives.adjoin_m ω₀ A₀ B₀).satisfies η := by
    apply (PowerlessRelativeSourceFamilyCandidateCondensation.base_formula_l η ω₀ A₀ B₀).mpr
    simpa only [hB₀, hω₀, hA₀, ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l]
      using hSeed.2.1
  exact PowerlessRelativeCandidateCondensationReading.read_l hℳ K Φ
    B₀ C₀ W₀ ω₀ A₀ Q₀ e₀ s₀ s₁ s₂ a₀ P₁ R₀ τ η hSource hAdjoin h

#print axioms read_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateCondensationReading
