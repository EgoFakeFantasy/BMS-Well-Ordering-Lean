import BMSConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers

/-! # 既有类内图的完整环境读值传输

不重新取代原图。前向由原图成员的坐标闭包提升，反向由明确的两个
载体守卫提升；正文仅用已验证 Δ₀ 绝对性。无守卫全称命题不能用此接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationReadAbsolute

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem read_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒞 [] Δ) {X Y R : type_l hℳ B}
    (hRead : ∀ x y : type_l hℳ B, value_l (ℳ := 𝒞) R x y ↔
      SecondOrderQuotient.mem_l hℳ x.val X.val ∧ SecondOrderQuotient.mem_l hℳ y.val Y.val ∧
        φ.satisfies ((η.pushFree y).pushFree x)) :
    ∀ x y : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) R.val x y ↔
      SecondOrderQuotient.mem_l hℳ x X.val ∧ SecondOrderQuotient.mem_l hℳ y Y.val ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  have hClass (x y : type_l hℳ B) : value_l (ℳ := 𝒱) R.val x.val y.val ↔
      SecondOrderQuotient.mem_l hℳ x.val X.val ∧ SecondOrderQuotient.mem_l hℳ y.val Y.val ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y.val).pushFree x.val) :=
    (PowerlessRelativeClassFunctionAbsolute.value_l R x y).symm.trans
      ((hRead x y).trans (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassRelationAmbientMembers.formula_absolute_l hφ η x y))))
  intro x y
  constructor
  · intro hValue
    obtain ⟨hx, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hValue
    exact (hClass ⟨x, hx⟩ ⟨y, hy⟩).mp hValue
  · rintro ⟨hx, hy, hBody⟩
    exact (hClass
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mpr ⟨hx, hy, hBody⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationReadAbsolute
