import BMSConstructibleBridge.PowerlessClassRealRootDecode
import BMSConstructibleBridge.PowerlessHereditaryCodedCollection

/-! # 原已编码族收集对象的实际遗传资格

原 Z₂ 任意模型中的语义接线。旧构造提供同一精确族收集的类内实数码；
新根解码将它提升为解码对象本身的遗传资格。全体内部图代表的成员读数
识别调用端的原对象 X，不能把 X 换成另一种收集。
这仍须接入原请求、完整遗传 Collection 模式和最终对象推导，不能据此
单独报告固定高度 BMS 的 Z₂ 形式化完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollectionDecoded

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem hereditary_l (K : source_coding_l hℳ) {B : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (U I₀ : type_l hℳ B)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega)
    (hI : ∀ c, mem_l hℳ c I₀.val → mem_l hℳ c K.omega) {H I : SecondOrderModel.set_l ℳ}
    (hUTrace : setRel_l K ⟨U.val, hU⟩ H) (hITrace : setRel_l K ⟨I₀.val, hI⟩ I)
    (hRows : SecondOrderCodedFamilyCollection.rows_wf_l H I)
    (X : SecondOrderQuotient.type_l hℳ)
    (hX : ∀ D, mem_l hℳ (SecondOrderQuotient.mk_l hℳ D) X ↔ SecondOrderCodedFamilyCollection.member_l H I D) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  obtain ⟨W₀, _hWHC, hW, C, hWTrace, _hRoot, hC⟩ :=
    PowerlessHereditaryCodedCollection.exists_l (hBase := hBase) K U I₀ hU hI hUTrace hITrace hRows
  have hHC : PowerlessHereditaryClass.member_l hℳ B (SecondOrderQuotient.mk_l hℳ C) :=
    PowerlessClassRealRootDecode.hereditary_l K hBase W₀.property hW hWTrace C.root C.wf
  have hSame : X = SecondOrderQuotient.mk_l hℳ C := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hX D).trans ((hC D).symm.trans (SecondOrderQuotient.mem_iff_l hℳ D C).symm)
  exact hSame.symm ▸ hHC

#print axioms hereditary_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollectionDecoded
