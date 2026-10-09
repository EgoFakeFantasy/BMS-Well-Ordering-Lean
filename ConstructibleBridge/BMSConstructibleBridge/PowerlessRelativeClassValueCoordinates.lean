import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute

/-! # 类内关系图的原商坐标闭包

传递性沿 Kuratowski 对的成员链取得两个坐标；不要求关系全域或单值。
这是取值绝对性的反向应用所需的域证据，不从宿主谓词抽取数据。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValueCoordinates

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false

universe u

theorem value_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (f : type_l hℳ B) {x y : SecondOrderQuotient.type_l hℳ}
    (h : SecondOrderFunctionObjects.value_l hℳ f.val x y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨p, hp, s, t, _, ht, hPair⟩ := h
  have hpClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase f.property hp
  have htClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hpClass
    ((hPair t).mpr (Or.inr rfl))
  exact ⟨PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass ((ht x).mpr (Or.inl rfl)),
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass ((ht y).mpr (Or.inr rfl))⟩

#print axioms value_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValueCoordinates
