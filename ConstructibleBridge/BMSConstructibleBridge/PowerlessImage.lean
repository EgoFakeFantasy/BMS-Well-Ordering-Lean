import BMSConstructibleBridge.PowerlessSeparation
import YesMetaZFC.SetTheory.Replacement

/-!
# 无幂集核心的精确函数像

直接复用上游关系像模式与语义定理，只用本核心的收集和分离。
不调用要求完整 ZF 的存在定理，也不把一般多值关系的全部输出当作集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessImage

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {n : Nat}
    (φ : BinarySchema n) (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n)
    (A : (FirstOrderSemantics.reduct ℳ).Domain)
    (h : ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A → ∃ y, φ.denote η x y)
    (h₁ : ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A →
      ∀ y z, φ.denote η x y → φ.denote η x z → y = z) :
    ∃ B, ∀ y, (FirstOrderSemantics.reduct ℳ).mem y B ↔
      ∃ x, (FirstOrderSemantics.reduct ℳ).mem x A ∧ φ.denote η x y := by
  obtain ⟨C, hC⟩ := PowerlessTheory.collection_l hℳ φ η A h
  obtain ⟨B, hB⟩ := PowerlessSeparation.exists_l hℳ φ.imageMembership (η.push A) C
  refine ⟨B, fun y => ?_⟩
  rw [hB y, SetTheory.Definitional.Project.Formula.satisfies_imageMembership_iff]
  constructor
  · rintro ⟨_, x, hx, hy⟩
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    obtain ⟨z, hz, h₂⟩ := hC x hx
    have h₃ := h₁ x hx y z hy h₂
    subst z
    exact ⟨hz, x, hx, hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessImage
