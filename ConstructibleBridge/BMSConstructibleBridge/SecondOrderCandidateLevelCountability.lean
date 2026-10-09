import BMSConstructibleBridge.SecondOrderCandidateSourceClassSeed
import BMSConstructibleBridge.PowerlessRelativeCutoffLevelCountability

/-! # 原候选的每个实际低层都有真实 Class 计数图

同一个实数候选、同一个 K 及精确基底不改变。基底枚举从原种子规格取得，
内部 ω 的全部成员覆盖由 B=ω∪{A} 的精确读数取得；不预供额外枚举。
主定理在证明内构造低层的实际 Class 单射，未声明单射图属于 W。
通用层可数性对象句已由 CutoffLevelCountability.derives_m 回到原 Z₂。
完整源分离／Collection、算术代表及最终 hSources 消去仍须继续证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateLevelCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem countable_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W γ D : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hγ : mem_l hℳ γ Ω)
    (hD : PowerlessRelativeHierarchySemantics.level_l hℳ B γ D) :
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega D := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.1.2.1.2.1 x y hx hy
  obtain ⟨G, hG, hMap, hOnto⟩ := hSeed.2.2
  have hωB : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x B :=
    fun x hx => (hSeed.2.1 x).mpr (Or.inl hx)
  exact PowerlessRelativeCutoffLevelCountability.countable_l hBase K ⟨G, hG⟩
    K.omega_spec hΩ hW hBW hωB hMap hOnto hγ hD

theorem member_countable_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W Y : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hY : mem_l hℳ Y W) :
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega Y := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.1.2.1.2.1 x y hx hy
  obtain ⟨G, hG, hMap, hOnto⟩ := hSeed.2.2
  exact PowerlessRelativeCutoffLevelCountability.member_countable_l hBase K ⟨G, hG⟩
    K.omega_spec hΩ hW hBW (fun x hx => (hSeed.2.1 x).mpr (Or.inl hx)) hMap hOnto hY

#print axioms countable_l
#print axioms member_countable_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateLevelCountability
