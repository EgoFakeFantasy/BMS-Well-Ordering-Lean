import BMSConstructibleBridge.SecondOrderTMC
import BMSConstructibleBridge.PowerlessBMSQuotientBoundedImageDerives
import BMSConstructibleBridge.PowerlessBMSSetTransitiveImageDerives
import BMSConstructibleBridge.SecondOrderDefinableRelationImageDerives
import BMSConstructibleBridge.SecondOrderFiniteSequencesDerives
import BMSConstructibleBridge.SecondOrderMemberEnumerationDerives
import BMSConstructibleBridge.SecondOrderInternalArithmeticDerives

/-!
# 后续相对可构造层使用的已验证弱背景接口

保留原 TMC 公理，另明确列出已经在原 Z₂ 图商中逐实例验证的两种特殊替换
和有界可定义关系图模式、有限闭包、有限子集集合与有限序列集合，以及非空
集合的 ω 满射、内部公式合法性和求值固定点的纯集合算术闭包。
每个新增条目的原图翻译都有实际 Z₂ 对象证明；
不是把未证的完整 Collection 加入目标 Z₂，也不宣称本接口与 TMC 句法等价。

后续纯集合论构造可以依赖这张显式公理表；任何已有闭句对象证明都能沿同一
原图解释回传。Def、相对 L* 和固定高度 BMS 终局仍需实际构造，不能由本接口省略。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConstructibilityBase

open Logic FirstOrder

set_option autoImplicit false

universe u

inductive axiom_m : Sentence ℒ → Prop where
  | base {φ : Sentence ℒ} (h : SecondOrderTMC.theory_m φ) : axiom_m φ
  | boundedImage {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
      axiom_m (PowerlessBMSQuotientBoundedImageDerives.sentence_m φ)
  | transitiveImage {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
      axiom_m (PowerlessBMSSetTransitiveImageDerives.sentence_m φ)
  | relationImage {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
      axiom_m (SecondOrderDefinableRelationImageDerives.sentence_m φ)
  | finiteClosure : axiom_m SecondOrderFiniteClosureDerives.sentence_m
  | finiteSubsets : axiom_m PowerlessFiniteSubsets.sentence_m
  | finiteSequences : axiom_m PowerlessFiniteSequencesSyntax.sentence_m
  | memberEnumeration : axiom_m SecondOrderMemberEnumerationDerives.sentence_m
  | formulaCodes : axiom_m SecondOrderInternalArithmeticDerives.syntax_sentence_m
  | formulaEvaluation : axiom_m SecondOrderInternalArithmeticDerives.evaluation_sentence_m

def theory_m : Theory ℒ := axiom_m

/-- 新条目由已有原 Z₂ 推导验证，没有附加语义前提。 -/
theorem axiom_derives_m (φ : Sentence ℒ) (h : theory_m φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) := by
  cases h with
  | base h => exact SecondOrderTMC.axiom_derives_m _ h
  | boundedImage φ => exact PowerlessBMSQuotientBoundedImageDerives.derives_m φ
  | transitiveImage φ => exact PowerlessBMSSetTransitiveImageDerives.derives_m φ
  | relationImage φ => exact SecondOrderDefinableRelationImageDerives.derives_m φ
  | finiteClosure => exact SecondOrderFiniteClosureDerives.derives_m
  | finiteSubsets => exact SecondOrderFiniteSubsetsDerives.derives_m
  | finiteSequences => exact SecondOrderFiniteSequencesDerives.derives_m
  | memberEnumeration => exact SecondOrderMemberEnumerationDerives.derives_m
  | formulaCodes => exact SecondOrderInternalArithmeticDerives.syntax_derives_m
  | formulaEvaluation => exact SecondOrderInternalArithmeticDerives.evaluation_derives_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    Theory.Models (SecondOrderQuotient.structure_l hℳ) theory_m := by
  intro φ h
  cases h with
  | base h => exact SecondOrderTMC.models_l hℳ _ h
  | boundedImage φ =>
      exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
        (PowerlessBMSQuotientBoundedImageDerives.models_l hℳ φ)
  | transitiveImage φ =>
      exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
        (PowerlessBMSSetTransitiveImageDerives.models_l hℳ φ)
  | relationImage φ =>
      exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
        (SecondOrderDefinableRelationImageDerives.models_l hℳ φ)
  | finiteClosure => exact SecondOrderFiniteClosureDerives.models_l hℳ
  | finiteSubsets => exact SecondOrderFiniteSubsetsDerives.models_l hℳ
  | finiteSequences => exact SecondOrderFiniteSequencesDerives.models_l hℳ
  | memberEnumeration => exact SecondOrderMemberEnumerationDerives.models_l hℳ
  | formulaCodes => exact SecondOrderInternalArithmeticDerives.syntax_models_l hℳ
  | formulaEvaluation => exact SecondOrderInternalArithmeticDerives.evaluation_models_l hℳ

/-- 只回传已经实际得到的源闭句推导，不接受裸的语义断言代替该证明。 -/
theorem derives_m {φ : Sentence ℒ} (h : Derives theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m φ) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact h.sound (models_l hℳ) Env.empty (by intro ψ hψ; cases hψ)

#print axioms axiom_derives_m
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConstructibilityBase
