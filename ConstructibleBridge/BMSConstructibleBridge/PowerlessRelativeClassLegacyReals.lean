import BMSConstructibleBridge.PowerlessRelativeClassLegacyTranslation
import BMSConstructibleBridge.PowerlessRelativeClassRelationReal

/-! # 原旧语法与部分翻译实数的实际 Class 代表

类内二元图与原算术实数参数不同。先取得精确旧合法图和部分翻译图，
再用实际数编码与原实数外延性证明 Class 中的 ω 子集分别表示原 V/C。
因而后续原算术 guard 可以使用原参数，不把集合值图冒充实数。

本模块仍是候选源建设的语义辅助；统一历史和完整源公理尚未交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyReals

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega) :
    ∃ V C : SecondOrderModel.set_l ℳ, SecondOrderInternalFormulaSyntax.spec_l V ∧
      SecondOrderLegacyFormulaTranslation.spec_l C ∧ ∃ A D : type_l hℳ B,
        ∃ hA : ∀ x, mem_l hℳ x A.val → mem_l hℳ x K.omega,
          ∃ hD : ∀ x, mem_l hℳ x D.val → mem_l hℳ x K.omega,
            setRel_l K ⟨A.val, hA⟩ V ∧ setRel_l K ⟨D.val, hD⟩ C := by
  obtain ⟨T, _hT, _hSpec, V, C, hV, hC, N, G, F, _hN, hG, hF⟩ :=
    PowerlessRelativeClassLegacyTranslation.exists_complete_l K hω hωEq
  obtain ⟨A, hA, hRepA⟩ := PowerlessRelativeClassRelationReal.represents_l (hBase := hBase) K G V hG
  have hRead (n m : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val
        (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l C n m :=
    (hF _ _).trans (PowerlessRelativeClassLegacyTranslation.numeric_l K C n m)
  obtain ⟨D, hD, hRepD⟩ := PowerlessRelativeClassRelationReal.represents_l (hBase := hBase) K F C hRead
  exact ⟨V, C, hV, hC, A, D, hA, hD, hRepA, hRepD⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyReals
