import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.SecondOrderFunctionObjects

/-! # 已给定的有界函数图留在指定极限层

实际图的每个成员必须是域、陪域上的有序对；逐值规格覆盖全部原商坐标。
在层内母积上作 Δ₀ 分离，再由有序对唯一性恢复原图，不替换调用者的图。
这是固定层成员界的语义辅助接口，不是完整源理论模型或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionRelation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    {X Y F : type_l hℳ} (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hMap : map_l (ℳ := 𝒱) F X Y)
    (hValue : ∀ x y : type_l hℳ, value_l (ℳ := 𝒱) F x y ↔
      mem_l hℳ x X ∧ mem_l hℳ y Y ∧ φ.satisfies ((η.pushFree y).pushFree x)) :
    mem_l hℳ F C := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty X Y
  have hProduct : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  have hPC := PowerlessRelativeLimitProduct.member_l hBase hLimit hC hX hY hProduct
  let ξ : Env 𝒱 [] (.set :: .set :: Δ) := (η.pushFree Y).pushFree X
  have hParams' : ∀ s (v : Variable (.set :: .set :: Δ) s), mem_l hℳ (ξ.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hX
    | there v => cases v with
      | here => exact hY
      | there v => exact hParams _ v
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hC
    (PowerlessRelativeClassRelation.body_delta_l hφ) ξ hPC hParams'
  have hEq : R = F := SecondOrderQuotient.ext_l hℳ R F (fun p => by
    have hBody := PowerlessRelativeClassRelation.body_formula_l φ η X Y p
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hxy, hφxy⟩ := hBody.mp ((hR p).mp hp).2
      obtain ⟨q, hq, hqxy⟩ := (hValue x y).mpr ⟨hx, hy, hφxy⟩
      have hpq := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hqxy).mpr ⟨rfl, rfl⟩
      exact hpq.symm ▸ hq
    · intro hp
      obtain ⟨x, y, hx, hy, hxy⟩ := hMap.1 p hp
      have hφxy := ((hValue x y).mp ⟨p, hp, hxy⟩).2.2
      exact (hR p).mpr ⟨(hProduct p).mpr ⟨x, y, hx, hy, hxy⟩,
        hBody.mpr ⟨x, y, hx, hy, hxy, hφxy⟩⟩)
  exact hEq ▸ hRC

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionRelation
