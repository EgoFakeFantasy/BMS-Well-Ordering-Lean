import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.SecondOrderFiniteAssignmentLift
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 任意旧内部参数码的原商赋值实现

背景为原 Z₂ 模型，连接式是原纯隶属语言中的旧赋值正文。实际数码
先反转填充，再沿同一个原商枚举复合；精确连接量化全部内部数字和
全部原商输出，不要求图或陪域属于 Class。给定真实有限操作闭包时，
原内部归纳将同一赋值图送入指定母界；不新增 Type 数据选择或源理论。
这是原 Def 查询行识别的中间工具，尚不等于最终固定高度对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRawRealization

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessLegacyAssignmentSyntax (link_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 不把原枚举或最终图提升到某个未取得资格的 Class 中。 -/
theorem exists_l (K : source_coding_l hℳ)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {c l : SecondOrderModel.num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (L z : SecondOrderModel.num_l ℳ) {U A : type_l hℳ}
    (hU : map_l (ℳ := 𝒱) U K.omega A) :
    ∃ f : type_l hℳ, map_l (ℳ := 𝒱) f (numberCode_l K L).val A ∧
      link_l K E c l L z U f := by
  obtain ⟨d, hd, hPad⟩ := SecondOrderLegacyAssignmentPadding.exists_l hℳ hE hc L z
  obtain ⟨f, hf, hRead⟩ := SecondOrderFiniteAssignmentLift.exists_ambient_l K hd hU
  refine ⟨f, hf, fun i y => (hRead i y).trans ?_⟩
  exact ⟨fun ⟨j, hj, hjy⟩ => ⟨j, (hPad i j).mp hj, hjy⟩,
    fun ⟨j, hj, hjy⟩ => ⟨j, (hPad i j).mpr hj, hjy⟩⟩

/-- 完整内部有限赋值回收同一个图；不要求 W 本身属于 W。 -/
theorem exists_member_l (K : source_coding_l hℳ)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {c l : SecondOrderModel.num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (L z : SecondOrderModel.num_l ℳ) {W U A : type_l hℳ}
    (hU : map_l (ℳ := 𝒱) U K.omega A)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    (hωW : mem_l hℳ K.omega W) (hAW : mem_l hℳ A W) :
    ∃ f : type_l hℳ, mem_l hℳ f W ∧ map_l (ℳ := 𝒱) f (numberCode_l K L).val A ∧
      link_l K E c l L z U f := by
  obtain ⟨f, hf, hLink⟩ := exists_l K hE hc L z hU
  have hfW := PowerlessRelativeFiniteHullAssignments.subset_member_l K
    (I := W) (n := (numberCode_l K L).val) (A := A) (f := f)
    (fun x hx => hTrans K.omega x hωW hx) hClosed (numberCode_l K L).property hf
    (fun x hx => hTrans A x hAW hx)
  exact ⟨f, hfW, hf, hLink⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRawRealization
