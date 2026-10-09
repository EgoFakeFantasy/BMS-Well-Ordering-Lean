import BMSConstructibleBridge.SecondOrderCandidateSourceClassSeed
import BMSConstructibleBridge.PowerlessRelativeCofinalHistorySeed
import BMSConstructibleBridge.PowerlessRelativeCutoffBelow

/-! # 同一原候选在首截断下的实际历史常量种子

原 Z₂、同一实数候选、同一 K 及精确基底保持不变。阶段 α∈Ω 的 Class
计数性由首截断规格取得，基底枚举由原候选种子取得；两者在证明内组成
实际 C/F。C 包含内部 ω、B、α 的全部成员并包含三个对象，且 C⊆W。
不预供 C/F，不把整个 W 或 Ω 放入种子，不要求 F∈W。

这是主线实际参数装配的语义中间层；通用种子对象存在句已在
CofinalHistorySeed.derives_m 回到原 Z₂。可数程序像、低层计数图的 W 界
及完整源公理仍须继续构造，不能从本种子宣布 hSources 已消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateHistorySeed

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

theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W α : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hα : mem_l hℳ α Ω) :
    ∃ C F : type_l hℳ B, map_l (ℳ := 𝒱) F.val K.omega C.val ∧
      (∀ x : Raw, mem_l hℳ x C.val →
        ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) F.val i x) ∧
      PowerlessRelativeCofinalHistorySeed.seed_l (B := B) K.omega α C.val ∧
      (∀ x, mem_l hℳ x C.val → mem_l hℳ x W) ∧
      (∀ x, mem_l hℳ x K.omega → mem_l hℳ x C.val) ∧
      (∀ x, mem_l hℳ x B → mem_l hℳ x C.val) ∧
      (∀ x, mem_l hℳ x α → mem_l hℳ x C.val) ∧ mem_l hℳ B C.val := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.1.2.1.2.1 x y hx hy
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  have hωBelow := PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K K.omega_spec hΩ
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW K.omega hωBelow
  have hαW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW α hα
  let ω : type_l hℳ B :=
    ⟨K.omega, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClass hωW⟩
  let a : type_l hℳ B :=
    ⟨α, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClass hαW⟩
  obtain ⟨G, hG, hMap, hOnto⟩ := hSeed.2.2
  have hMap' : map_l (ℳ := 𝒱) G ω.val B := hMap
  have hOnto' : ∀ x : Raw, mem_l hℳ x B →
      ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) G i x := hOnto
  obtain ⟨C, F, hF, hFOnto, hC⟩ := PowerlessRelativeCofinalHistorySeed.exists_l
    (hBase := hBase) ω a ⟨G, hG⟩ K.omega_spec hMap' hOnto' (hΩ.2.2 α hα)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hBound := PowerlessRelativeCofinalHistorySeed.subset_l hC
    (hTrans B hBW) (hTrans α hαW) hBW hαW hωW
  have hBC : ∀ x, mem_l hℳ x B → mem_l hℳ x C.val :=
    fun x hx => (hC x).mpr (Or.inl hx)
  have hωC : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x C.val :=
    fun x hx => hBC x ((hSeed.2.1 x).mpr (Or.inl hx))
  exact ⟨C, F, hF, hFOnto, hC, hBound, hωC, hBC,
    (fun x hx => (hC x).mpr (Or.inr (Or.inl hx))),
    (hC B).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateHistorySeed
