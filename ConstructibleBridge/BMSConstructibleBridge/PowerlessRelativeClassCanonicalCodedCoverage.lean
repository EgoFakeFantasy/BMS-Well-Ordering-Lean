import BMSConstructibleBridge.PowerlessCanonicalCodedCoverageSyntax
import BMSConstructibleBridge.PowerlessRelativeClassCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryReading
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange

/-! # 实际 Class 规范比较图的完整覆盖存在

原 Z₂、纯隶属 ℒ。原完整覆盖构造保留同一编码和前史，规范比较递归
产生实际 Class 图。精确值域构造把 raw 陪域替换为实际 Class 值域，
不更换函数图；随后同一阶段上的选定输出进入覆盖矩阵。
全部存在见证留在 Prop，不要求内部枚举图已经属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B

/-- 同一图在其精确 Class 值域上仍是干净总函数。 -/
theorem range_map_l (A g : M) {q : Raw} (hg : map_l (ℳ := 𝒱) g.val A.val q) :
    ∃ R : M, map_l (ℳ := 𝒩₀) g A R := by
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase A g hg
  have hMap : map_l (ℳ := 𝒱) g.val A.val R.val := by
    constructor
    · intro p hp
      obtain ⟨a, P, ha, _hP, hPair⟩ := hg.1 p hp
      exact ⟨a, P, ha, (hR P).mpr ⟨a, p, hp, hPair⟩, hPair⟩
    · intro a ha
      obtain ⟨P, ⟨_hP, hValue⟩, _hUnique⟩ := hg.2 a ha
      refine ⟨P, ⟨(hR P).mpr ⟨a, hValue⟩, hValue⟩, ?_⟩
      rintro Q ⟨_hQ, hQValue⟩
      exact SecondOrderFunctionProperties.value_unique_l hℳ hg hQValue hValue
  exact ⟨R, (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g A R).mpr hMap⟩

theorem exists_l (K : source_coding_l hℳ) (ω x P₀ : M)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hB : ∃ b, mem_l hℳ b B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p) :
    PowerlessCanonicalCodedCoverageSyntax.statement_l (𝒩 := 𝒩₀)
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω x P₀ := by
  obtain ⟨C, a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, Pair, N, Valid, V, Q, G,
    hPoint, hCode, hA, hHistory⟩ :=
      PowerlessRelativeClassCodedCoverage.witnesses_l (hBase := hBase) K ω x hω
  obtain ⟨g, q, hg, hEquations, _hRead⟩ :=
    PowerlessRelativeClassCanonicalHistoryReading.exists_l
      (hBase := hBase) K U f P₀ ω e t₁ t₂ t₃ Pair N Valid Q G hCode hA hHistory hB hSeed hBound
  obtain ⟨R, hMap⟩ := range_map_l (hBase := hBase) A g hg
  obtain ⟨P, ⟨_hPR, hValue⟩, _hUnique⟩ := hMap.2 a hPoint.1
  exact ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, Pair, N, Valid, V, Q, G,
    g, R, P, hPoint, hMap, hEquations, hValue⟩

#print axioms range_map_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverage
