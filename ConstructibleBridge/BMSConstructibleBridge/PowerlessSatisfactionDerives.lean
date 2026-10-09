import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification

/-! # 完整公共 Sat 存在句的原 Z₂ 推导

共同静态见证实际由原二阶模型构造，随后逐域存在求值图。对象句既不
假设 PowerlessTheory，也不加入收集公理；相对化保留传递基与内部 ω 守卫。
此结论是后续严格先前层应用的输入，不是最终固定行数 BMS 良序性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    PowerlessSatisfactionExistenceSyntax.statement_l (𝒩 := structure_l hℳ B hBase) ω := by
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, T, N, F, hωEq, he, hT, hSpec, hN, hF, hDomains⟩ :=
    PowerlessRelativeClassSatisfaction.exists_l hω
  obtain ⟨_, _, _, hSystem, _, _⟩ := hDomains ω
  have hNClass : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω ω N := by
    intro f
    have hN' := hN f.val
    rw [← hωEq] at hN'
    exact hN'.trans (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l
      (hBase := hBase) ω ω f).symm
  refine ⟨e, t₁, t₂, t₃, T, N, F, ?_, ?_⟩
  · exact ⟨hSystem.1, hSystem.2.1, hSystem.2.2.1, hNClass,
      PowerlessFormulaValiditySpecification.instance_l K hω hωEq he hSystem.1 hT hSpec hV hN hF⟩
  · intro A
    obtain ⟨S, G, R, hSystemA, hS, hR⟩ := hDomains A
    exact ⟨R, PowerlessRelativeClassSatisfactionSpecification.instance_l hR K hωEq hS hF
      hSystemA he hT hSpec hV⟩

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    PowerlessSatisfactionExistenceSyntax.sentence_m.TrueIn (structure_l hℳ B hBase) :=
  PowerlessSatisfactionExistenceSyntax.sentence_formula_l.mpr (fun _ hω => exists_l hω)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m
      PowerlessSatisfactionExistenceSyntax.sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionDerives
