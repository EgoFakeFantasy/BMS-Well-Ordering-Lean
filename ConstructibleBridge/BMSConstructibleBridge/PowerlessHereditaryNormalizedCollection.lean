import BMSConstructibleBridge.PowerlessHereditaryFamilyNormalization
import BMSConstructibleBridge.PowerlessHereditaryCodedCollectionDecoded

/-! # 同一原规范化族的解码收集对象

纯隶属语言 ℒ，背景原 Z₂。原带根族的 Class 实数 U 先读取同一
规范化 J，再以实际 ω 作为全索引的 Class 代表，解码原收集对象 X。
接口保留所有图代表上的精确成员规格，不预设 X 的 Class 或遗传资格。
这是接入完整收集模式的语义引理，不能代替最终固定高度对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNormalizedCollection

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem hereditary_l (K : source_coding_l hℳ) (U : type_l hℳ B)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega)
    {H J I : SecondOrderModel.set_l ℳ} (hTrace : setRel_l K ⟨U.val, hU⟩ H)
    (hJ : SecondOrderRootedRealFamilyNormalization.spec_l H J)
    (hI : ∀ n, SecondOrderModel.mem_l n I)
    (hRows : SecondOrderCodedFamilyCollection.rows_wf_l J I)
    (X : SecondOrderQuotient.type_l hℳ)
    (hX : ∀ D, mem_l hℳ (SecondOrderQuotient.mk_l hℳ D) X ↔
      SecondOrderCodedFamilyCollection.member_l J I D) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  obtain ⟨V, _hVHC, hV, hVTrace⟩ :=
    PowerlessHereditaryFamilyNormalization.same_l (hBase := hBase) K U hU hTrace hJ
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  have hOSub : ∀ c, mem_l hℳ c O.val → mem_l hℳ c K.omega := fun _ h => h
  have hOTrace : setRel_l K ⟨O.val, hOSub⟩ I := by
    intro n
    exact ⟨fun _ => hI n, fun _ => (numberCode_l K n).property⟩
  exact PowerlessHereditaryCodedCollectionDecoded.hereditary_l K hBase V O
    hV hOSub hVTrace hOTrace hRows X hX

#print axioms hereditary_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryNormalizedCollection
