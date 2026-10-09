import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepAmbient
import BMSConstructibleBridge.PowerlessRelativeClassHierarchyBranches
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading

/-! # 类内规范递归的当前分支读回 raw

原 Z₂ 中只要求真正前驱的母序具有 raw 良序资格；不要求当前输出
或整段历史预供 raw 良序。这是原纯公式内部归纳的步接口，使用
同一 Class 图与相同坐标，不假设模型序数的外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAmbient

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem step_l (K : source_coding_l hℳ) (ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g a X P : M)
    (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair N Valid)
    (hPast : ∀ b, mem_l hℳ b a.val → ∀ Y Q, value_l (ℳ := 𝒱) F.val b Y →
      value_l (ℳ := 𝒱) g.val b Q → wellOrder_l (ℳ := 𝒱) Y Q)
    (h : PowerlessCanonicalOrderEquations.step_l (𝒩 := 𝒩₀)
      ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g a X P) :
    PowerlessCanonicalOrderEquations.step_l (𝒩 := 𝒱) ω.val e.val t₁.val t₂.val t₃.val
      Pair.val Valid.val B₀.val P₀.val F.val g.val a.val X.val P.val := by
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, _hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω hStatic
  rcases h with ⟨hEmpty, hXB, hPP₀⟩ | ⟨b, Y, Q, hSucc, hY, hQ, hStep⟩ | ⟨hLimit, hF, hg⟩
  · exact Or.inl ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) a).mp hEmpty,
      congrArg Subtype.val hXB, congrArg Subtype.val hPP₀⟩
  · have hSuccRaw := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) b a).mp hSucc
    have hYRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b Y).mp hY
    have hQRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g b Q).mp hQ
    have hMother := hPast b.val (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSuccRaw)
      Y.val Q.val hYRaw hQRaw
    exact Or.inr (Or.inl ⟨b.val, Y.val, Q.val, hSuccRaw, hYRaw, hQRaw,
      PowerlessRelativeClassCanonicalStepAmbient.uniform_l K hω he hPairMap hPair hMother hStep⟩)
  · exact Or.inr (Or.inr ⟨(PowerlessRelativeClassHierarchyBranches.limit_l (hBase := hBase) a).mp hLimit,
      (PowerlessRelativeClassHierarchyBranches.union_l (hBase := hBase) F a X).mp hF,
      (PowerlessRelativeClassHierarchyBranches.union_l (hBase := hBase) g a P).mp hg⟩)

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAmbient
