import BMSConstructibleBridge.PowerlessRelativeCutoffHistoryCodedCoverage
import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
import BMSConstructibleBridge.PowerlessMemberOperationClosure
import BMSConstructibleBridge.PowerlessRelativeLimitOperationClosure

/-! # 首 Ω 母层中完整局部覆盖矩阵的实际存在性

每个实际成员 x 都由同一前史点覆盖，整包在纯成员结构中成立。
B、ω、x 是原给定成员；其余十七个见证在 Prop 中取得，不要求
所有 x 共用一个更早 U。矩阵不含 W／Ω 参数，供同一个共同族捕获；
此处尚未把任何见证预供到 I，也没有消去最终 hSources。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W : SecondOrderQuotient.type_l hℳ} {hW₀ : ∃ x, mem_l hℳ x W}

local notation "𝒩₀" => PowerlessMemberStructure.structure_l
  (ℳ := SecondOrderQuotient.structure_l hℳ) W hW₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W

theorem exists_l (K : source_coding_l hℳ) (B ω x : M)
    {Ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ z, mem_l hℳ z B.val → ∀ t, mem_l hℳ t z → mem_l hℳ t B.val)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B.val ω.val Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B.val Ω W) :
    PowerlessCodedHistoryCoverageSyntax.statement_l (𝒩 := 𝒩₀) B ω x := by
  obtain ⟨a, y, A, β, U, D, f, hPoint, ω₀, e, t₁, t₂, t₃, P, N, F, Q, G, t₄, V,
    _C, hωEq, _hCoding, hStatic, hSat, hDef, hNumeric, hA, hLight, hFinite⟩ :=
    PowerlessRelativeCutoffHistoryCodedCoverage.exists_l
      K hBase hω hΩ hW B.property x.property
  have hEq : ω₀ = ω := Subtype.ext hωEq
  subst ω₀
  obtain ⟨_haW, _hyW, _hAW, _hβW, _hUW, _hDW, _hfW,
    haA, _haΩ, _hAΩ, _hβΩ, _hAβ, hLimit, _hCofinal, hU, hBU, _hxU, hωU,
    _hGraph, _hf, _hHistory, _hCapture, _hyLevel, hy, hxy⟩ := hPoint
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW z hz t ht
  have hValue : value_l (ℳ := 𝒩₀) f a y :=
    (PowerlessSourceGraphAbsolute.value_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (A := W) (hA := hW₀) hTrans).mpr hy
  have hUTransRaw : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) U.val :=
    fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU z hz t ht
  have hUClosedRaw := PowerlessRelativeLimitOperationClosure.closed_l hℳ hBase hLimit hU
  have hOuterClosed := PowerlessRelativeLimitOperationClosure.closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW
  have hUTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒩₀) U :=
    (PowerlessMemberOperationClosure.transitive_l (hW := hW₀) hTrans U).mpr hUTransRaw
  have hUClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒩₀) U :=
    (PowerlessMemberOperationClosure.closed_l (hW := hW₀) hTrans hOuterClosed U).mpr hUClosedRaw
  exact ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G,
    haA, hValue, hxy, hBU, hωU, hStatic, hSat, hDef, hNumeric, hA, hLight,
    hFinite, hUTrans, hUClosed⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberCodedCoverage
