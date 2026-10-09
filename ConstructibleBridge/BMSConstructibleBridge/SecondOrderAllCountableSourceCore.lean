import BMSConstructibleBridge.SecondOrderAllCountableProjectSeparation
import BMSConstructibleBridge.SecondOrderAllCountableProjectCollection
import BMSConstructibleBridge.PowerlessRelativeClassInfinity

/-! # 全类可数分支的实际完整 PowerlessTheory 模型

逐项消费原理论的六条基础公理及全部原 Separation / Collection
模式。载体仍是实际相对构造类，不新增抽象模型公理；全类可数
条件尚未消去，因此不是无条件候选源或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceCore

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SetTheory.Definitional.Project
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : FirstOrder.Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

theorem models_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a) :
    FirstOrder.Theory.Models ClassModel PowerlessTheory.theory_m := by
  have hExt := PowerlessRelativeClassStructure.ext_l hℳ B hBase
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  cases hψ with
  | extensionality =>
    simp only [FirstOrder.Formula.TrueIn, fo_sentence, PowerlessTheory.extensionality_m,
      SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
      FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
      SetTheory.Definitional.Project.Formula.extensionalEq,
      SetTheory.Definitional.Project.Formula.pairArguments]
    change ∀ A B : CType, (∀ x : CType, mem_l hℳ x.val A.val ↔ mem_l hℳ x.val B.val) → A = B
    exact hExt.eq_of_same_members
  | empty =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessRelativeClassBasicAxioms.empty_l hℳ B hBase)
  | pairing =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessRelativeClassStructure.pairing_l hℳ B hBase)
  | union =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessRelativeClassBasicAxioms.union_l hℳ B hBase)
  | infinity =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessRelativeClassInfinity.models_l hℳ B hBase)
  | foundation =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessRelativeClassStructure.foundation_l hℳ B hBase)
  | separation φ =>
    exact SecondOrderAllCountableProjectSeparation.source_models_l
      K hCoding hGuard hS hAll φ
  | collection φ =>
    exact SecondOrderAllCountableProjectCollection.source_models_l
      K hCoding hGuard hS hAll φ

#print axioms models_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceCore
