import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfactionForDomain
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionClean
import BMSConstructibleBridge.PowerlessSatisfactionNormalizedMatrix
import BMSConstructibleBridge.PowerlessSatisfactionValueCongruence

/-! # 共尾极限层中全部域的实际规范 Sat 见证

同一层 W 内固定完整静态编码包。每个 A∈W 的完整 Seq 和 Sat 实际进入 W，
再在 W 中清理 Sat 图。全部合法赋值在 W 中的界由原 Z₂ 内部有限函数
归纳取得；母界直接用 W，不假设 Seq(ω,W)∈W，也不把 W 用作属于自己的参数。

本模块实际证明规范矩阵的逐域同层总性，无 Collection 或 Type 选择。
整张统一函数及其有限 Def 开销由后续接口取得；前史和终局仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalNormalizedSatisfaction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β W : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 共尾性显式保留；普通极限性不能替代层内 Sat 总性所需的早极限界。 -/
theorem exists_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (ω : type_l hℳ B) (hωW : mem_l hℳ ω.val W) (hωEq : ω.val = K.omega) :
    ∃ e t₁ t₂ t₃ T N F : type_l hℳ B,
      mem_l hℳ e.val W ∧ mem_l hℳ t₁.val W ∧ mem_l hℳ t₂.val W ∧ mem_l hℳ t₃.val W ∧
        mem_l hℳ T.val W ∧ mem_l hℳ N.val W ∧ mem_l hℳ F.val W ∧
          PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := ClassModel) ω e t₁ t₂ t₃ T N F ∧
            ∀ A : type_l hℳ B, mem_l hℳ A.val W → ∃ R : type_l hℳ B, mem_l hℳ R.val W ∧
              PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
                ω.val A.val e.val N.val T.val W W t₁.val t₂.val t₃.val F.val R.val := by
  obtain ⟨e, t₁, t₂, t₃, T, N, F, heW, ht₁W, ht₂W, ht₃W, hTW, hNW, hFW, hStatic, hAll⟩ :=
    PowerlessRelativeCofinalSatisfactionForDomain.exists_l
      (hBase := hBase) K hLimit hW hCofinal ω hωW hωEq
  obtain ⟨he, _ht₁, _ht₂, _ht₃, hN, hT, hPair, _hF⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hωEq hStatic
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hωRaw : omega_l (ℳ := RawModel) ω.val := hωEq.symm ▸ K.omega_spec
  have heEmpty := (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hStatic.1.1
  have hNω : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val ω.val N.val := by
    simpa only [hωEq] using hN
  have hTω : map_l (ℳ := RawModel) T.val ω.val ω.val := by
    simpa only [hωEq] using hT
  refine ⟨e, t₁, t₂, t₃, T, N, F, heW, ht₁W, ht₂W, ht₃W, hTW, hNW, hFW, hStatic, ?_⟩
  intro A hAW
  obtain ⟨s, hsW, hSeq⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l
    hBase hLimit hW hωRaw hωW hAW
  let S : type_l hℳ B := ⟨s, ⟨β, W, hW, hsW⟩⟩
  obtain ⟨R, hRW, hSat⟩ := hAll A hAW
  have hRawSat := PowerlessRelativeClassSatisfactionAbsolute.spec_l K hωEq he hT hPair hSat
  have hDomain (c f : SecondOrderQuotient.type_l hℳ)
      (hValue : value_l (ℳ := RawModel) R.val c f) : mem_l hℳ c ω.val ∧ mem_l hℳ f S.val := by
    obtain ⟨hc, L, hL, _hValid, hMap⟩ := hRawSat.1 c f hValue
    exact ⟨hc, (hSeq f).mpr ⟨L, hL, hMap⟩⟩
  obtain ⟨Q, hQW, hValues, hClean⟩ := PowerlessRelativeClassSatisfactionClean.exists_l
    hBase hLimit hW ω S R hωW hsW hRW hDomain
  have hQSat := (PowerlessSatisfactionValueCongruence.spec_l
    ω.val A.val e.val t₁.val t₂.val t₃.val T.val F.val R.val Q.val
    (fun c f => (hValues c f).symm)).mp hRawSat
  have hCoverage (f : SecondOrderQuotient.type_l hℳ)
      (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) ω.val A.val f) :
      mem_l hℳ f W := by
    obtain ⟨L, hL, hMap⟩ := hf
    exact PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase hLimit hW K
      (hωEq ▸ hωW) (fun x hx => hTrans A.val hAW x hx) (hωEq ▸ hL) hMap
  exact ⟨Q, hQW, (PowerlessSatisfactionNormalizedMatrix.spec_iff_of_coverage_l
    hωRaw heEmpty hNω hTω hCoverage).mpr ⟨s, hsW, hSeq, hQSat, hClean⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalNormalizedSatisfaction
