import BMSConstructibleBridge.PowerlessBMSQuotientSubsetFunction

/-! # 固定载体上可定义关系族的实际集合历史

所有输出关系的有序对都落在同一个实际笛卡尔积中，故可复用子集有界
替换，而无需幂集、Collection 或逐数选择实码。仍须由调用者证明该纯
定义在每个内部数上的总性和唯一性；这不是无条件的序历史存在定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBoundedRelationHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (C : type_l hℳ)
    (hTotal : ∀ n, ∃ P, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree P))
    (hUnique : ∀ n P Q,
      φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree P) →
      φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree Q) → P = Q)
    (hProper : ∀ n P, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree P) →
      ∀ p, mem_l hℳ p P → ∃ x y, mem_l hℳ x C ∧ mem_l hℳ y C ∧
        SecondOrderPairObjects.ordered_l hℳ x y p) :
    ∃ b g : type_l hℳ,
      (∀ P, mem_l hℳ P b ↔ ∃ n, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree P)) ∧
      map_l (ℳ := 𝒱) g K.omega b ∧
      ∀ x P, value_l (ℳ := 𝒱) g x P ↔
        mem_l hℳ x K.omega ∧ φ.satisfies ((η.pushFree x).pushFree P) := by
  obtain ⟨D, hD⟩ := SecondOrderDefinableRelationImage.exists_l hℳ
    (show Formula ℒ [] [.set, .set] from .truth) Env.empty C C
  apply PowerlessBMSQuotientSubsetFunction.exists_l K φ η D hTotal hUnique
  intro n P hP p hp
  obtain ⟨x, y, hx, hy, hxy⟩ := hProper n P hP p hp
  exact (hD p).mpr ⟨x, y, hx, hy, trivial, hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBoundedRelationHistory
