import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepReading

/-! # 原规范后继的同一输出具有 Class 资格和原公式真值

在已有 Class 母集及同一原编码包下构造规范候选，原 raw 唯一性
识别任意已有后继输出；随即用逐字段读出取得 Class 原公式真值。
不重选编码，不要求母集已有 Class 内 ω 枚举，也不复制计数式 Def
公式到类中。真正的 raw Def 和母集环境良序守卫仍明确保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepOriginal

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

/-- 输出是给定原 E，不以另一个后继冒充其类内见证。 -/
theorem original_l (K : source_coding_l hℳ)
    (ω A P e t₁ t₂ t₃ Pair Valid D : M) (E : SecondOrderQuotient.type_l hℳ)
    (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒩₀) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A.val →
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y A.val)
    (hDef : SecondOrderMemberDef.spec_l hℳ A.val D.val)
    (hE : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
      ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E) :
    ∃ E₀ : M, E₀.val = E ∧
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩₀)
        ω A P e t₁ t₂ t₃ Pair Valid D E₀ := by
  have hΩ : omega_l (ℳ := 𝒩₀) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  have hTagsRaw : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e.val t₁.val t₂.val t₃.val :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hTags.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mp hTags.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mp hTags.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mp hTags.2.2.2⟩
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFixedCoding.satisfaction_l
    (hBase := hBase) K (A := A) hω he hTagsRaw hPairMap hPair hV hValid
  obtain ⟨E₀, hE₀, _hUnique⟩ := PowerlessRelativeClassCanonicalOrderUniform.exists_unique_l
    K hΩ hP hω he hTags hPairMap hPair hV hValid ⟨R, hR⟩ hTrans hDef
  have hRaw := SecondOrderCanonicalOrderUniform.step_ambient_l K hω he hPairMap hPair hE₀.1
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  have hSame := SecondOrderCanonicalOrderUniform.unique_l K hω he ht₁ ht₂ ht₃
    hPairMap hPair hV hValid hE hRaw
  exact ⟨E₀, hSame.symm, PowerlessRelativeClassCanonicalStepReading.uniform_l hE₀.1⟩

#print axioms original_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepOriginal
