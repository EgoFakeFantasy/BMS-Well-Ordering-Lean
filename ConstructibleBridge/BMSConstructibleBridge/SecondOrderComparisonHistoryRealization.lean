import BMSConstructibleBridge.SecondOrderComparisonNativeRow
import BMSConstructibleBridge.SecondOrderComparisonHistoryStageLocal

/-! # 原递归实数的同一张实际比较历史图

逐行正文可能存在量化不同的历史代表和解码见证。ω 子集代表唯一性先
统一历史代表，逐值相同再统一解码读数。因此全部行满足同一实际 G 下的
阶段正文，不能把每行各取一个图误当成共同历史已经装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryRealization

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l environment_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem exists_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (hω : v p.ω = K.omega) (he : v p.e = zero_l K) (S : SecondOrderModel.set_l ℳ)
    (hRows : ∀ n W, SecondOrderSections.spec_l S n W →
      SecondOrderComparisonNativeRow.formula_m.satisfies
        ((((environment_l K p).pushFree S).pushFree n).pushFree W)) :
    ∃ E : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega, ∃ q G,
      setRel_l K E S ∧
      SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱) K.omega (zero_l K) E.val (v p.f) (v p.C) q G ∧
      ∀ n W, SecondOrderSections.spec_l S n W →
        ∃ U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega, setRel_l K U W ∧
          SecondOrderComparisonStageSyntax.output_l K.omega (zero_l K) (v p.t₁) (v p.t₂)
            (v p.t₃) (v p.Pair) (v p.Valid) (v p.I) (v p.J) (v p.T) G (v p.P₀) (v p.f)
            (numberCode_l K n).val U.val := by
  obtain ⟨E, hE⟩ := representative_exists_l K S
  obtain ⟨q, G, hG⟩ := SecondOrderComparisonHistoryDerives.exists_l K E S hE (v p.C) (v p.f)
  refine ⟨E, q, G, hE, hG, ?_⟩
  intro n W hW
  obtain ⟨A, B, hA, hB, hRow⟩ :=
    (SecondOrderComparisonNativeRow.formula_l K p n S W).mp (hRows n W hW)
  rw [SecondOrderComparisonNativeRow.row_l, hω, he] at hRow
  have hARead := (SecondOrderRealTraceSyntax.reading_l K A hRow.1 S).mp hA
  have hAE : v A = E.val := congrArg Subtype.val
    (PowerlessBMSQuotientReals.representative_unique_l K hARead hE)
  rw [hAE] at hRow
  obtain ⟨_, q', G', hG', hOutput⟩ := hRow
  let U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega :=
    ⟨v B, SecondOrderComparisonStageTotal.guard_l K hOutput⟩
  have hU : setRel_l K U W := (SecondOrderRealTraceSyntax.reading_l K B U.property W).mp hB
  exact ⟨U, hU, (SecondOrderComparisonHistoryStage.decoded_congr_l K hG' hG).mp hOutput⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryRealization
