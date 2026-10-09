import BMSConstructibleBridge.PowerlessRelativeClassOmegaWellOrder

/-! # 同一 ω 隶属序图对所有环境子集的最小元

不以类内良序最小元条款作绝对性传输。环境任意非空子集先使用原商
正则性取见证；子集包含于 ω 才把见证及其成员提升入类，然后读取
同一关系图。子集自身完全没有类成员前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaAmbientOrder

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem of_comparison_l {ω R : type_l hℳ B}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hRead : ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) R x y ↔
      SecondOrderQuotient.mem_l hℳ x.val ω.val ∧
      SecondOrderQuotient.mem_l hℳ y.val ω.val ∧ SecondOrderQuotient.mem_l hℳ x.val y.val) :
    wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val R.val := by
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hΩ)
  let lift (x : SecondOrderQuotient.type_l hℳ) (hx : SecondOrderQuotient.mem_l hℳ x ω.val) :
      type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hx⟩
  have hGraph (x y : SecondOrderQuotient.type_l hℳ)
      (hx : SecondOrderQuotient.mem_l hℳ x ω.val) (hy : SecondOrderQuotient.mem_l hℳ y ω.val) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val x y ↔
        SecondOrderQuotient.mem_l hℳ x y :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (lift x hx) (lift y hy)).symm.trans
      ((hRead (lift x hx) (lift y hy)).trans
        ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxx
    exact hOrd.wellOrder.linear.irrefl x hx ((hGraph x x hx hx).mp hxx)
  · intro x y z hxyz hxy hyz
    exact (hGraph x z hxyz.1 hxyz.2.2).mpr
      (hOrd.wellOrder.linear.trans x hxyz.1 y hxyz.2.1 z hxyz.2.2
        ((hGraph x y hxyz.1 hxyz.2.1).mp hxy)
        ((hGraph y z hxyz.2.1 hxyz.2.2).mp hyz))
  · intro x y hxy
    rcases hOrd.wellOrder.linear.compare x hxy.1 y hxy.2 with hEq | hlt | hgt
    · exact Or.inr (Or.inl (SecondOrderQuotient.ext_l hℳ x y hEq))
    · exact Or.inl ((hGraph x y hxy.1 hxy.2).mpr hlt)
    · exact Or.inr (Or.inr ((hGraph y x hxy.2 hxy.1).mpr hgt))
  · intro U hU
    have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ U : SecondOrderQuotient.type_l hℳ,
      (∃ x, SecondOrderQuotient.mem_l hℳ x U) →
        ∃ x, SecondOrderQuotient.mem_l hℳ x U ∧
          ∀ y, SecondOrderQuotient.mem_l hℳ y x → ¬SecondOrderQuotient.mem_l hℳ y U at hFoundation
    obtain ⟨x, hx, hMin⟩ := hFoundation U hU.2
    exact ⟨x, hx, fun y hy hlt =>
      hMin y ((hGraph y x (hU.1 y hy) (hU.1 x hx)).mp hlt) hy⟩

#print axioms of_comparison_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaAmbientOrder
