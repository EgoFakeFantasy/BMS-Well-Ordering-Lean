import BMSConstructibleBridge.SecondOrderWeakSetTheory
import BMSConstructibleBridge.SecondOrderCountabilityAxiom
import BMSConstructibleBridge.SecondOrderMostowskiAxiom

/-!
# TMC 的实际二阶图解释与闭句推导传输

源理论为无幂集、无收集、无选择的完整分离集合论，加传递超集、内部可数性
及 MostColl。ω、函数和有序对在纯隶属语言中展开，空集公理保留为显式条目。

任意二阶模型的原内部图商满足全部源公理，原图翻译回传任意源闭句推导。
这完成该中间理论的对象推导传输，不等于完成 L*、BM4 固定高度推导生成器
或 PRA 中的 (G)；强完备性并未提供原始递归证明码程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC

open Logic FirstOrder

set_option autoImplicit false

universe u

inductive axiom_m : Sentence ℒ → Prop where
  | base {φ : Sentence ℒ} (h : SecondOrderWeakSetTheory.theory_m φ) : axiom_m φ
  | countability : axiom_m SecondOrderCountabilityAxiom.formula_m
  | collapse : axiom_m SecondOrderMostowskiAxiom.formula_m

def theory_m : Theory ℒ := axiom_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    Theory.Models (SecondOrderQuotient.structure_l hℳ) theory_m := by
  intro φ h
  cases h with
  | base h => exact SecondOrderWeakSetTheory.models_l hℳ φ h
  | countability => exact SecondOrderCountabilityAxiom.models_l hℳ
  | collapse => exact SecondOrderMostowskiAxiom.models_l hℳ

theorem axiom_derives_m (φ : Sentence ℒ) (h : theory_m φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) :=
  SecondOrderAxioms.interpretation_m φ (fun _ hℳ => models_l hℳ φ h)

/-- TMC 任意已有闭句对象证明的原图翻译均有 Z₂ 对象证明。 -/
theorem derives_m {φ : Sentence ℒ} (h : Derives theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact h.sound (models_l hℳ) Env.empty (by intro ψ hψ; cases hψ)

/-- 宿主元层的一致性传输；不声称 Z₂ 在内部证明自身或 TMC 一致。 -/
theorem consistency_m (h : ¬Derives SecondOrderArithmetic.theory_m []
    (Formula.falsum : Sentence SecondOrderSyntax.signature_m)) :
    ¬Derives theory_m [] (Formula.falsum : Sentence ℒ) := fun h₁ => h (derives_m h₁)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTMC
