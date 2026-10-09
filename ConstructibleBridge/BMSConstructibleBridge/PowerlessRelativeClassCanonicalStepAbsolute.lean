import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepAmbient
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepOriginal
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading

/-! # 固定实际母集的原规范后继双向对应

传递相对类、原 Z₂ 背景。raw 母序、母集传递性与原 Def 都显式
保留；Class 和 raw 使用同一静态包及同一全部参数、输出。这里
不是任意 Class 良序的绝对性，也不先假定完整类源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem iff_l (K : source_coding_l hℳ) (ω A P e t₁ t₂ t₃ Pair N Valid D E : M)
    (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair N Valid)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A.val →
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y A.val)
    (hDef : SecondOrderMemberDef.spec_l hℳ A.val D.val) :
    SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩₀) ω A P e t₁ t₂ t₃ Pair Valid D E ↔
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
        ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E.val := by
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω hStatic
  constructor
  · exact PowerlessRelativeClassCanonicalStepAmbient.uniform_l K hω he hPairMap hPair hP
  · intro h
    obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
    obtain ⟨E₀, hSame, hStep⟩ := PowerlessRelativeClassCanonicalStepOriginal.original_l
      K ω A P e t₁ t₂ t₃ Pair Valid D E.val hω he hStatic.1 hPairMap hPair
        hV (hValid V hV) hP hTrans hDef h
    have hEq : E₀ = E := Subtype.ext hSame
    exact hEq ▸ hStep

#print axioms iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepAbsolute
