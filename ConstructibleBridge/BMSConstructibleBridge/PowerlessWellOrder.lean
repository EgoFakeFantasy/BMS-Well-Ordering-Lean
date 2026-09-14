import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.ThirdOrderSemantics

/-!
# 内部良序的可定义极小元与归纳

只对由当前纯公式和原参数分离出的子集应用内部极小元条款。
本接口不返回宿主 WellFounded，也不要求模型外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellOrder

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem minimum_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R)
    (h : ∃ x, member_l ℳ x A ∧ φ.satisfies ((PowerlessComprehension.env_l η).pushFree x)) :
    ∃ x, member_l ℳ x A ∧ φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ∧
      ∀ y, member_l ℳ y A → φ.satisfies ((PowerlessComprehension.env_l η).pushFree y) →
        ¬value_l R y x := by
  obtain ⟨B, hB⟩ := PowerlessComprehension.separation_l hℳ φ η A
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, hz, h₁⟩ := hR.2.2.2 B
    ⟨fun y hy => ((hB y).mp hy).1, x, (hB x).mpr hx⟩
  exact ⟨z, ((hB z).mp hz).1, ((hB z).mp hz).2,
    fun y hy h₂ => h₁ y ((hB y).mpr ⟨hy, h₂⟩)⟩

theorem induction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {A R : carrier_l ℳ} (hR : wellOrder_l A R)
    (h : ∀ x, member_l ℳ x A →
      (∀ y, member_l ℳ y A → value_l R y x →
        φ.satisfies ((PowerlessComprehension.env_l η).pushFree y)) →
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree x)) :
    ∀ x, member_l ℳ x A → φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) := by
  intro x hx
  by_contra h₀
  obtain ⟨z, hz, h₁, h₂⟩ := minimum_l hℳ (.neg φ) η hR ⟨x, hx, h₀⟩
  apply h₁
  apply h z hz
  intro y hy h₃
  by_contra h₄
  exact h₂ y hy h₄ h₃

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellOrder
