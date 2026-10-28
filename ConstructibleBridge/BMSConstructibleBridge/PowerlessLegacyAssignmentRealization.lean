import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.SecondOrderFiniteAssignmentLift
import BMSConstructibleBridge.PowerlessLegacyAssignmentRawRealization

/-! # 任意原内部参数码的实际类内表示

复用原商中的完整反转填充与枚举复合，再将同一个有限函数图提升入类。
连接式直接保留全部原商输出的量词，不重新按类内输出证明连接。
不要求枚举图本身属于类，不把 Prop 见证选择成 Type 数据。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRealization

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessLegacyAssignmentSyntax (link_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem exists_l (K : source_coding_l hℳ) {ω A : type_l hℳ B}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω) (hω : ω.val = K.omega)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {c l : SecondOrderModel.num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (L z : SecondOrderModel.num_l ℳ) {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val) :
    ∃ f : type_l hℳ B,
      map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω L) A ∧
        link_l K E c l L z U f.val := by
  obtain ⟨f, hf, hLink⟩ := PowerlessLegacyAssignmentRawRealization.exists_l K hE hc L z hU
  have hfClass := PowerlessRelativeClassFiniteMapLift.member_l hBase ω.property A.property
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hΩ)
    (hω.symm ▸ (numberCode_l K L).property) hf
  let f' : type_l hℳ B := ⟨f, hfClass⟩
  exact ⟨f', (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase)
    f' (number_l hBase K ω hω L) A).mpr hf, hLink⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRealization
