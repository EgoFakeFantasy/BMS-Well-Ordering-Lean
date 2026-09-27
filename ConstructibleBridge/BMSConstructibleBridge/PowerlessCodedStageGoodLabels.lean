import BMSConstructibleBridge.PowerlessCodedStageTheory
import BMSConstructibleBridge.PowerlessStageOrdinal
import BMSConstructibleBridge.PowerlessStabilitySupport

/-!
# 指定有限支持的好标签条件由同一对编码见证覆盖

§16 条目 4 的语义收口：`code_l` 给出的两个自然数码只依赖 k 与 Ξ = StabilitySupport.basis_m k，
对全部"自身层满足 Ξ"的标签同时生效；反射端点的高处层实际携带这对码。
公式正文仍只含固定 AST 的 holds_m，不展开 Ξ，也不引入标准性假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageGoodLabels

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessCodedStageTheory

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

/-- 同一对码覆盖全部满足 Ξ 的标签：码由 k 单独决定，与所选标签及其层无关。 -/
theorem good_labels_uniform_l (k : Nat) :
    ∃ c N : carrier_l ℳ, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      ∀ {α A S F : carrier_l ℳ}, ∀ hA₀ : ∃ x, member_l ℳ x A,
        PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F →
        Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) →
        holds_l ω e T t₁ t₂ t₃ c N α := by
  obtain ⟨c, N, hc, hN, h⟩ :=
    PowerlessCodedStageTheory.code_l hℳ hω ht hT (PowerlessStabilitySupport.basis_m k)
  exact ⟨c, N, hc, hN, fun hA₀ hA h𝒜 => (h hA₀ hA).mpr h𝒜⟩

/-- 高处层实际提供编码见证：低处标签 α 的层满足 Ξ 时，同一对码属于 β 的层，且编码条件对 α 成立。 -/
theorem endpoint_codes_l {α β A B : carrier_l ℳ} (k : Nat)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hβ : PowerlessStagePair.limit_l β) (hωβ : member_l ℳ ω β)
    {S F : carrier_l ℳ} (hA₀ : ∃ x, member_l ℳ x A)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
    (h𝒜 : Theory.Models (structure_l A hA₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k))) :
    ∃ c N : type_l B, member_l ℳ c.val ω ∧ member_l ℳ N.val ω ∧
      holds_l ω e T t₁ t₂ t₃ c.val N.val α := by
  obtain ⟨c, N, hc, hN, h⟩ := good_labels_uniform_l hℳ hω ht hT k
  refine ⟨⟨c, PowerlessStageOrdinal.subset_l hℳ hω ht hT hB c
      (PowerlessOrdinal.transitive_l hβ.1 ω c hωβ hc)⟩,
    ⟨N, PowerlessStageOrdinal.subset_l hℳ hω ht hT hB N
      (PowerlessOrdinal.transitive_l hβ.1 ω N hωβ hN)⟩, hc, hN, h hA₀ hA h𝒜⟩

#print axioms good_labels_uniform_l
#print axioms endpoint_codes_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageGoodLabels
