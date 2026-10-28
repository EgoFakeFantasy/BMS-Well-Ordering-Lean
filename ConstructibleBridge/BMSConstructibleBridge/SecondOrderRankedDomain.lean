import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderDomainClosure
import BMSConstructibleBridge.SecondOrderInterpretation

/-!
# 有效基础根上添加数值递减节点

原图基础部分可以不是数值递减的，只要其根已经内部无链；其余父根的每个
子根必须属于基础部分或严格数值递减。对原域公式作内部强归纳，得到所有根
无内部下降链。此为显式条件工具；使用者仍须验证具体图的基础与边条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedDomain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing GraphTranslation

set_option autoImplicit false

universe u

theorem wf_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (base : num_l ℳ → Prop)
    (hBase : ∀ n, base n → SecondOrderDomain.wf_l R n)
    (hEdge : ∀ a, ¬base a → ∀ b, relation_l R b a → base b ∨ SecondOrderOrder.lt_l b a) :
    ∀ a, SecondOrderDomain.wf_l R a := by
  classical
  let φ : Formula signature_m [] [.num, .set] :=
    domain_m (.fvar (.there .here)) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ
    (domain_pure_m _ _ rfl rfl) ((Env.empty (M := ℳ)).pushFree R)
    (SecondOrderDomain.wf_l R)
  · intro n
    exact SecondOrderInterpretation.domain_l _ _ _
  · intro a ih
    by_cases ha : base a
    · exact hBase a ha
    · apply SecondOrderDomainClosure.intro_l hℳ R a
      intro b hb
      exact (hEdge a ha b hb).elim (hBase b) (ih b)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedDomain
