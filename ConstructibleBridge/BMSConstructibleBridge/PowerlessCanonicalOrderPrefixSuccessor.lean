import BMSConstructibleBridge.PowerlessCanonicalOrderRawPrefix
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryRestriction

/-! # 原比较前缀的实际后继图界

前驱图与末值属于指定非零极限层即可。先在同层构造精确值域及加入末值的
实际陪域，再调用单点延拓；原 raw 陪域无须属于 Class 或该层。
这是内部预算归纳的局部步骤，不是任意长 Class 历史的存在断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderPrefixSuccessor

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem member_l {B ξ C α β f g q E : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ ξ)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ β α)
    (hβC : mem_l hℳ β C) (hgC : mem_l hℳ g C) (hEC : mem_l hℳ E C)
    (hf : map_l (ℳ := 𝒱) f α q) (hg : map_l (ℳ := 𝒱) g β q)
    (hRead : ∀ a P, value_l (ℳ := 𝒱) g a P ↔
      mem_l hℳ a β ∧ value_l (ℳ := 𝒱) f a P)
    (hE : value_l (ℳ := 𝒱) f β E) : mem_l hℳ f C := by
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitFunctionRange.exists_l
    hBase hLimit hC hβC hgC hg
  obtain ⟨S, hS⟩ := SecondOrderPairObjects.pair_exists_l hℳ E E
  have hSC := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC hEC hEC hS
  obtain ⟨T, hT⟩ := SecondOrderPairObjects.pair_exists_l hℳ R S
  have hTC := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC hRC hSC hT
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ X : type_l hℳ, ∃ U, ∀ y, mem_l hℳ y U ↔
    ∃ z, mem_l hℳ z X ∧ mem_l hℳ y z at hUnion
  obtain ⟨U, hU⟩ := hUnion T
  have hUC := PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC hTC hU
  have hBoundG a P (hP : value_l (ℳ := 𝒱) g a P) : mem_l hℳ P U :=
    (hU P).mpr ⟨R, (hT R).mpr (Or.inl rfl), (hR P).mpr ⟨a, hP⟩⟩
  have hBoundF a P (hP : value_l (ℳ := 𝒱) f a P) : mem_l hℳ P U := by
    rcases (hSucc a).mp (SecondOrderFunctionProperties.value_mem_l hℳ hf hP).1 with ha | ha
    · exact hBoundG a P ((hRead a P).mpr ⟨ha, hP⟩)
    · subst a
      have hPE := SecondOrderFunctionProperties.value_unique_l hℳ hf hP hE
      exact (hU P).mpr ⟨S, (hT S).mpr (Or.inr rfl),
        (hS P).mpr (Or.inl hPE)⟩
  have hfU := PowerlessCanonicalOrderRawPrefix.codomain_l hℳ hf hBoundF
  have hgU := PowerlessCanonicalOrderRawPrefix.codomain_l hℳ hg hBoundG
  have hβ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) β :=
    SetTheory.Structure.IsOrdinal.mem hα ((hSucc β).mpr (Or.inr rfl))
  exact PowerlessHierarchyLightHistoryRestriction.successor_member_l hℳ hBase
    hLimit hC hUC hβC hgC hβ hSucc hfU hgU hRead

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderPrefixSuccessor
