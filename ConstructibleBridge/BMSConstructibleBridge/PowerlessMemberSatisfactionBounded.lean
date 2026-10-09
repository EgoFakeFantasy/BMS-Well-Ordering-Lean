import BMSConstructibleBridge.PowerlessSatisfactionSpecificationBounded
import BMSConstructibleBridge.SecondOrderMemberBounded

/-! # 实际传递成员模型中的完整 Sat 检查

在原图商的实际成员结构中核验纯 Δ₀ 检查器，再用环境中的完整数值
序列、赋值序列及配数图守卫，读成环境原完整 Sat 规格。参数通过真实
成员环境取得共同母集界，不借类域语义代替成员模型。

这里只传输给定证书的检查结果：不构造 Sat，不给统一历史或共同层界，
也不宣称成员模型满足完整源理论或 BMS 对象推导已经完成。成员模型
原无界 Sat 规格的双向绝对性不在本接口范围内。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberSatisfactionBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {A : SecondOrderGraph.code_l ℳ}
  {a : SecondOrderModel.num_l ℳ} {ha : SecondOrderPairing.relation_l A.real a A.root}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem spec_l
    (hTrans : ∀ x, mem_l hℳ x (mk_l hℳ A) → ∀ y, mem_l hℳ y x → mem_l hℳ y (mk_l hℳ A))
    {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
    (ω X e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set)
    (hω : omega_l (ℳ := 𝒱) (ω.eval η).val)
    (he : ∀ x, ¬mem_l hℳ x (e.eval η).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) (ω.eval η).val (ω.eval η).val (N.eval η).val)
    (hT : map_l (ℳ := 𝒱) (T.eval η).val (ω.eval η).val (ω.eval η).val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) (ω.eval η).val (X.eval η).val (S.eval η).val) :
    (PowerlessSatisfactionSpecificationBounded.spec_m ω X e N T S t₁ t₂ t₃ F R).satisfies η ↔
      PowerlessSatisfactionSpecification.spec_l («𝒩» := 𝒱)
        (ω.eval η).val (X.eval η).val (e.eval η).val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val
        (T.eval η).val (F.eval η).val (R.eval η).val := by
  have hRead := (SecondOrderMemberBounded.formula_l hTrans
    (PowerlessSatisfactionSpecificationBounded.delta_l ω X e N T S t₁ t₂ t₃ F R) η).trans
      (PowerlessSatisfactionSpecificationBounded.spec_formula_l
        (SecondOrderMemberBounded.env_l η) ω X e N T S t₁ t₂ t₃ F R)
  simp only [SecondOrderMemberBounded.term_l] at hRead
  exact hRead.trans (PowerlessSatisfactionSpecificationBounded.guarded_iff_l hω he hN hT hS)

#print axioms spec_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberSatisfactionBounded
