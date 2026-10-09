import BMSConstructibleBridge.SecondOrderLegacyValidityBudget
import BMSConstructibleBridge.PowerlessRelativeClassMembershipTrace

/-! # 原二维合法性预算域的类内有限成员表

原实数 V 的全部预算查询 l + n ≤ B 使用同一个配数初段 (B + 1)²。
表 f 是实际类内集合函数，但 V 及其无限布尔图不要求属于类。
这里只证明预算域内的逐点读取；尚不构造 Δ₀ 旧合法性检查器，不收集
无限总图，也不证明公式翻译的输出码界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityBudgetTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {C : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C}

theorem exists_l (K : source_coding_l hℳ) {ω : type_l hℳ C}
    (hω : omega_l (ℳ := structure_l hℳ C hBase) ω) (hωEq : ω.val = K.omega)
    (V : SecondOrderModel.set_l ℳ) (B : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ C,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
        (numberCode_l K (SecondOrderModel.mul_l
          (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))).val K.omega ∧
      ∀ n l, bound_l l n B →
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
          (numberCode_l K (SecondOrderPairing.value_l n l)).val
          (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val ↔
          SecondOrderPairing.relation_l V n l) := by
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassMembershipTrace.exists_l K hω hωEq V
    (SecondOrderModel.mul_l (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))
  refine ⟨f, hf, ?_⟩
  intro n l hB
  have hBound := SecondOrderLegacyValidityBudget.cell_bound_l hℳ hB
  have hOne := SecondOrderModel.nonzero_l hℳ (SecondOrderModel.zero_l ℳ)
  constructor
  · intro hValue
    rcases ((hRead (SecondOrderPairing.value_l n l)
      (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).mp hValue).2 with
      ⟨hMember, _⟩ | ⟨_, hFalse⟩
    · exact hMember
    · exact (hOne hFalse).elim
  · intro hMember
    exact (hRead _ _).mpr ⟨hBound, Or.inl ⟨hMember, rfl⟩⟩

/-- 原全码合法性规格只用于读取对应；原递归正文仍含类外实数参数 V。 -/
theorem validity_l (K : source_coding_l hℳ) {ω : type_l hℳ C}
    (hω : omega_l (ℳ := structure_l hℳ C hBase) ω) (hωEq : ω.val = K.omega)
    (V : SecondOrderModel.set_l ℳ) (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (B : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ C,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
        (numberCode_l K (SecondOrderModel.mul_l
          (SecondOrderModel.succ_l B) (SecondOrderModel.succ_l B))).val K.omega ∧
      ∀ n l, bound_l l n B →
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
          (numberCode_l K (SecondOrderPairing.value_l n l)).val
          (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val ↔
          SecondOrderInternalFormulaSyntax.rule_l V n l) := by
  obtain ⟨f, hf, hRead⟩ := exists_l K hω hωEq V B
  exact ⟨f, hf, fun n l hB => (hRead n l hB).trans (hV n l)⟩

#print axioms exists_l
#print axioms validity_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityBudgetTrace
