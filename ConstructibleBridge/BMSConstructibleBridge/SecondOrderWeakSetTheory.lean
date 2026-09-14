import BMSConstructibleBridge.SecondOrderFoundation
import BMSConstructibleBridge.SecondOrderTransitiveSuperset
import BMSConstructibleBridge.SecondOrderUnion
import BMSConstructibleBridge.SecondOrderInfinityAxiom
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-!
# 已核验的无幂集、无收集集合论片段

明确列出外延、空集、配对、并集、无穷、正则、完整分离及传递超集公理。
它不包含选择、坍缩或可数性。其任意闭句对象推导可沿原图翻译回传至 Z₂；
强完备性回传仍不是一个已输出数值码的原始递归编译器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWeakSetTheory

open Logic FirstOrder

set_option autoImplicit false

universe u

inductive axiom_m : Sentence ℒ → Prop where
  | extensionality : axiom_m SecondOrderAxioms.extensionality_m
  | empty : axiom_m SecondOrderAxioms.empty_m
  | pairing : axiom_m SecondOrderPairSet.formula_m
  | union : axiom_m SecondOrderUnion.formula_m
  | infinity : axiom_m SecondOrderInfinityAxiom.formula_m
  | foundation : axiom_m SecondOrderFoundation.formula_m
  | transitive : axiom_m SecondOrderTransitiveSuperset.formula_m
  | separation {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
      axiom_m (SecondOrderSeparationAxiom.sentence_m φ)

def theory_m : Theory ℒ := axiom_m

/-- 任意二阶模型的同一图商满足逐一列明的全部源公理。 -/
theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    Theory.Models (SecondOrderQuotient.structure_l hℳ) theory_m := by
  intro φ h
  cases h with
  | extensionality => exact SecondOrderQuotient.ext_l hℳ
  | empty => exact SecondOrderQuotient.empty_l hℳ
  | pairing => exact SecondOrderPairSet.models_l hℳ
  | union => exact SecondOrderUnion.models_l hℳ
  | infinity => exact SecondOrderInfinityAxiom.models_l hℳ
  | foundation => exact SecondOrderFoundation.models_l hℳ
  | transitive => exact SecondOrderTransitiveSuperset.models_l hℳ
  | separation φ =>
      exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
        (SecondOrderSeparationAxiom.models_l hℳ φ)

theorem axiom_derives_m (φ : Sentence ℒ) (h : theory_m φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) :=
  SecondOrderAxioms.interpretation_m φ (fun _ hℳ => models_l hℳ φ h)

/-- 回传已有的任意源闭句推导，而不把源理论尚缺的公理加入翻译背景。 -/
theorem derives_m {φ : Sentence ℒ} (h : Derives theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact h.sound (models_l hℳ) Env.empty (by intro ψ hψ; cases hψ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWeakSetTheory
