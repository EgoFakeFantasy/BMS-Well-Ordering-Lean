import BMSConstructibleBridge.SecondOrderLegacyTranslationFunction
import BMSConstructibleBridge.SecondOrderLegacyValidityBudget
import BMSConstructibleBridge.PowerlessRelativeClassNumericTrace

/-! # 原翻译总化函数的类内二维有限表

同一内部预算的全部 (n,l) 单元由一个实际 Class 有限函数覆盖，其值是
翻译输出码而非布尔数。输出直接落在 ω，无需另取数字上界 Q。
原 V/C 及其无限总化图不要求属于类。非法输入的零仅是默认值；
只有保留 Valid 守卫时，值图才精确表示原部分翻译查询。

这不是完整有界翻译检查器、无限翻译 Class 图或统一历史界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationBudgetTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {D : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D}

theorem exists_l (K : source_coding_l hℳ) {ω : type_l hℳ D}
    (hω : omega_l (ℳ := structure_l hℳ D hBase) ω) (hωEq : ω.val = K.omega)
    (V C : SecondOrderModel.set_l ℳ) (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (B : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ D,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
        (numberCode_l K (SecondOrderModel.mul_l
          (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))).val K.omega ∧
      ∀ n l, bound_l l n B → ∀ q,
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
          (numberCode_l K (SecondOrderPairing.value_l n l)).val (numberCode_l K q).val ↔
            SecondOrderLegacyTranslationFunction.point_l V C n l q) := by
  obtain ⟨E, hE, hSpec⟩ := SecondOrderLegacyTranslationFunction.exists_l hℳ V C hV hC
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassNumericTrace.exists_l K hω hωEq hE
    (SecondOrderModel.mul_l (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))
  refine ⟨f, hf, ?_⟩
  intro n l hB q
  have hCell := SecondOrderLegacyValidityBudget.cell_bound_l hℳ hB
  exact (hRead (SecondOrderPairing.value_l n l) q).trans
    ⟨fun h => (SecondOrderLegacyTranslationFunction.read_l hℳ hSpec n l q).mp h.2,
      fun h => ⟨hCell, (SecondOrderLegacyTranslationFunction.read_l hℳ hSpec n l q).mpr h⟩⟩

theorem legal_l (K : source_coding_l hℳ) {ω : type_l hℳ D}
    (hω : omega_l (ℳ := structure_l hℳ D hBase) ω) (hωEq : ω.val = K.omega)
    (V C : SecondOrderModel.set_l ℳ) (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (B : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ D,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
        (numberCode_l K (SecondOrderModel.mul_l
          (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))).val K.omega ∧
      ∀ n l, bound_l l n B → SecondOrderPairing.relation_l V n l → ∀ q,
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
          (numberCode_l K (SecondOrderPairing.value_l n l)).val (numberCode_l K q).val ↔
            SecondOrderLegacyFormulaTranslation.query_l C n l q) := by
  obtain ⟨f, hf, hRead⟩ := exists_l K hω hωEq V C hV hC B
  refine ⟨f, hf, ?_⟩
  intro n l hB hValid q
  exact (hRead n l hB q).trans
    ⟨fun h => h.elim (fun h => h.2) (fun h => (h.1 hValid).elim),
      fun h => Or.inl ⟨hValid, h⟩⟩

#print axioms exists_l
#print axioms legal_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationBudgetTrace
