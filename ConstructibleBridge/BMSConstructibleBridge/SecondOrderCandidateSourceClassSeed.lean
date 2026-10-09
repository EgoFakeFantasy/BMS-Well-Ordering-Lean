import BMSConstructibleBridge.SecondOrderCandidateSourcePreparation
import BMSConstructibleBridge.PowerlessRelativeClassAmbientBaseGuard
import BMSConstructibleBridge.PowerlessRelativeCutoffClassOrderHistory
import BMSConstructibleBridge.PowerlessRelativeCutoffClassWellOrder

/-! # 每个原候选的实际 Class 初始序图与截断相容历史

保留原候选实数、同一 K、精确基集 ω∪{A} 及真正的 Class 基底满射。
原 arbitrary raw P₀ 不升级 Class：实际重建 Class 初始良序并保持旧候选
语义上下文。随后截断支的 Class 层／比较历史不增加初始序图存在前提。
仍没有统一枚举族、member-W 见证、完整源模型或最终固定高度推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateSourceClassSeed

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem exists_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) (X : ℳ.Carrier .set) :
    ∃ K : source_coding_l h𝒩, ∃ t₁ t₂ t₃ Pair Valid B S : SecondOrderQuotient.type_l h𝒩,
      ∃ A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l h𝒩) K.omega,
        ∃ P₀ : type_l h𝒩 B,
          SecondOrderCandidateSourcePreparation.seed_context_l K t₁ t₂ t₃ Pair Valid B P₀.val S A X := by
  obtain ⟨K, t₁, t₂, t₃, Pair, Valid, B, _P₀, S, A, hSeed⟩ :=
    SecondOrderCandidateSourcePreparation.seed_exists_l h𝒩 X
  have hBase x hx y hy := hSeed.1.2.1.2.1 x y hx hy
  obtain ⟨f, hClass, hf, hOnto⟩ := hSeed.2.2
  have hf' : map_l (ℳ := SecondOrderQuotient.structure_l h𝒩) f K.omega B := hf
  have hOnto' : ∀ y, mem_l h𝒩 y B → ∃ n, mem_l h𝒩 n K.omega ∧
      value_l (ℳ := SecondOrderQuotient.structure_l h𝒩) f n y := hOnto
  obtain ⟨P₀, hGuard⟩ := PowerlessRelativeClassAmbientBaseGuard.exists_l K hBase
    ⟨f, hClass⟩ hf' hOnto' hSeed.1.2.1.1
  exact ⟨K, t₁, t₂, t₃, Pair, Valid, B, S, A, P₀,
    ⟨hSeed.1.1, hGuard, hSeed.1.2.2⟩, hSeed.2⟩

theorem cutoff_history_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ F H : type_l hℳ B, ∃ q : Raw,
      PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F.val W ∧
      map_l (ℳ := 𝒱) H.val Ω q ∧
      (∀ a X P, SecondOrderWellOrderCoherentUnion.stage_l Ω F.val H.val a X P →
        wellOrder_l (ℳ := 𝒱) X P) ∧
      PowerlessRelativeCutoffClassOrderHistory.coherent_l (𝒩 := 𝒱) Ω F.val H.val :=
  PowerlessRelativeCutoffClassOrderHistory.exists_l K P₀ hSeed.1.2.1 K.omega_spec hΩ hW

theorem cutoff_wellOrder_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ R : type_l hℳ B, wellOrder_l (ℳ := 𝒱) W R.val :=
  PowerlessRelativeCutoffClassWellOrder.exists_l K P₀ hSeed.1.2.1 K.omega_spec hΩ hW

#print axioms exists_l
#print axioms cutoff_history_l
#print axioms cutoff_wellOrder_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateSourceClassSeed
