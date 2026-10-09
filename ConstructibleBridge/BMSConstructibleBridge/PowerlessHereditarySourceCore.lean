import BMSConstructibleBridge.PowerlessHereditaryProjectSchemas
import BMSConstructibleBridge.PowerlessHereditaryWeakTheory

/-! # 实际遗传子模型的完整无幂集核心

纯隶属 ℒ，背景原 Z₂。逐项消费原 PowerlessTheory 六条基础公理和
全部原 Project 分离、收集模式；载体是原实际遗传域而非另造抽象模型。
保留传递、非空且自身遗传的基底守卫，不加入全类可数或 Type 选择。
该模型解释尚须接入源算术及原 BMS 候选的对应才能取得最终原目标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySourceCore

open Logic FirstOrder PowerlessBMSQuotientCoding
open SetTheory.Definitional.Project
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.type_l PowerlessHereditaryStructure.structure_l FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase
local notation "N" => PowerlessHereditaryStructure.type_l hℳ B

theorem models_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B) :
    Theory.Models 𝒩₁ PowerlessTheory.theory_m := by
  have hExt := PowerlessHereditaryStructure.ext_l hℳ B hBase
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  cases hψ with
  | extensionality =>
    simp only [FirstOrder.Formula.TrueIn, fo_sentence, PowerlessTheory.extensionality_m,
      SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
      FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
      SetTheory.Definitional.Project.Formula.extensionalEq,
      SetTheory.Definitional.Project.Formula.pairArguments]
    change ∀ A B : N, (∀ x : N, mem_l hℳ x.val A.val ↔ mem_l hℳ x.val B.val) → A = B
    exact hExt.eq_of_same_members
  | empty =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessHereditaryBasicAxioms.empty_l hℳ B hBase)
  | pairing =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessHereditaryPairing.models_l hℳ B hBase)
  | union =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessHereditaryBasicAxioms.union_l hℳ B hBase)
  | infinity =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessHereditaryStructure.infinity_l hℳ B hBase)
  | foundation =>
    exact (PowerlessTheory.sentence_l hExt _).mpr
      (PowerlessHereditaryStructure.foundation_l hℳ B hBase)
  | separation φ =>
    exact PowerlessHereditaryProjectSchemas.separation_l hB hNonempty φ
  | collection φ =>
    exact PowerlessHereditaryProjectSchemas.collection_l K hB hNonempty φ

#print axioms models_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySourceCore
