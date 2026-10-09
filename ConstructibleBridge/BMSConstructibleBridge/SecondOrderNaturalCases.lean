import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor
import BMSConstructibleBridge.SecondOrderPairObjects

/-! # 无 Collection 的原商后继单射与自然数分支

前驱分支从原模型公理经全部内部数的根码覆盖搬运；后继单射只使用
无序对和正则。内部自然数允许非标准数，未进行宿主 Nat 归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalCases

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem asymmetry_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {a b : type_l hℳ} (hab : mem_l hℳ a b) : ¬mem_l hℳ b a := by
  intro hba
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ P : type_l hℳ, (∃ x, mem_l hℳ x P) → ∃ x, mem_l hℳ x P ∧
    ∀ y, mem_l hℳ y x → ¬mem_l hℳ y P at hFoundation
  obtain ⟨x, hx, hDisjoint⟩ := hFoundation P ⟨a, (hP a).mpr (Or.inl rfl)⟩
  rcases (hP x).mp hx with rfl | rfl
  · exact hDisjoint b hba ((hP b).mpr (Or.inr rfl))
  · exact hDisjoint a hab ((hP a).mpr (Or.inl rfl))

theorem successor_injective_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {a b c : type_l hℳ}
    (ha : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a c)
    (hb : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) b c) : a = b := by
  rcases (hb a).mp ((ha a).mpr (Or.inr rfl)) with h | h
  · rcases (ha b).mp ((hb b).mpr (Or.inr rfl)) with h' | h'
    · exact (asymmetry_l hℳ h h').elim
    · exact h'.symm
  · exact h

theorem cases_l (K : source_coding_l hℳ) {n : type_l hℳ} (hn : mem_l hℳ n K.omega) :
    n = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∨ ∃ a, mem_l hℳ a K.omega ∧
      PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) a n := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hEq : (numberCode_l K i).val = n := congrArg Subtype.val hi
  rw [← hEq]
  rcases SecondOrderModel.predecessor_l hℳ i with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(numberCode_l K j).val, (numberCode_l K j).property,
      PowerlessBMSQuotientSuccessor.successor_l K j⟩

#print axioms successor_injective_l
#print axioms cases_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalCases
