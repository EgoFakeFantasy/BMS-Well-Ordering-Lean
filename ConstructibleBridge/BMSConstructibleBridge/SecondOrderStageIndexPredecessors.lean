import BMSConstructibleBridge.SecondOrderStageIndexFunction

/-! # 实际阶段编号函数与原内部前驱实数

同一规范根指标上的 J 将原前驱实数精确读成商隶属关系。证明覆盖内部
自然数全域；域外指标由原代表域和 J 的精确图规格排除，不假设外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexPredecessors

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem relation_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : SecondOrderModel.set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    {J : type_l hℳ}
    (hJ : ∀ x y, value_l (ℳ := 𝒱) J x y ↔ ∃ n, ∃ hn : SecondOrderModel.mem_l n D,
      x = (numberCode_l K n).val ∧
        y = SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn))
    (i j : SecondOrderModel.num_l ℳ) :
    SecondOrderPairing.relation_l R i j ↔ ∃ a b,
      value_l (ℳ := 𝒱) J (numberCode_l K i).val a ∧
      value_l (ℳ := 𝒱) J (numberCode_l K j).val b ∧ mem_l hℳ a b := by
  constructor
  · intro hij
    have hi := ((h.predecessors i j).mp hij).1
    have hj := ((h.predecessors i j).mp hij).2.1
    refine ⟨SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h i hi),
      SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h j hj),
      (hJ _ _).mpr ⟨i, hi, rfl, rfl⟩, (hJ _ _).mpr ⟨j, hj, rfl, rfl⟩, ?_⟩
    exact (SecondOrderQuotient.mem_iff_l hℳ _ _).mpr
      ((SecondOrderRootCorrespondence.edge_iff_l hℳ A h hi hj).mp hij)
  · rintro ⟨a, b, hia, hjb, hab⟩
    obtain ⟨m, hm, him, rfl⟩ := (hJ _ _).mp hia
    obtain ⟨n, hn, hjn, rfl⟩ := (hJ _ _).mp hjb
    have him' : i = m := numberCode_injective_l K (Subtype.ext him)
    have hjn' : j = n := numberCode_injective_l K (Subtype.ext hjn)
    subst m
    subst n
    exact (SecondOrderRootCorrespondence.edge_iff_l hℳ A h hm hn).mpr
      ((SecondOrderQuotient.mem_iff_l hℳ _ _).mp hab)

/-- 实际 J 的构造同时给出原前驱关系，后续不另设未填的关系对应契约。 -/
theorem exists_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : SecondOrderModel.set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (hI : setRel_l K I D) :
    ∃ J : type_l hℳ, map_l (ℳ := 𝒱) J I.val (SecondOrderQuotient.mk_l hℳ A) ∧
      (∀ a, mem_l hℳ a (SecondOrderQuotient.mk_l hℳ A) → ∃ i,
        mem_l hℳ i I.val ∧ value_l (ℳ := 𝒱) J i a) ∧ injective_l (ℳ := 𝒱) J ∧
      ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ a b,
        value_l (ℳ := 𝒱) J (numberCode_l K i).val a ∧
        value_l (ℳ := 𝒱) J (numberCode_l K j).val b ∧ mem_l hℳ a b := by
  obtain ⟨J, hJ, hOnto, hInject, hRead⟩ := SecondOrderStageIndexFunction.exists_l K A h I hI
  exact ⟨J, hJ, hOnto, hInject, relation_l K A h hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexPredecessors
