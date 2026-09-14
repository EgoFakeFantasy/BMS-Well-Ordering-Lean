import BMSConstructibleBridge.PowerlessStageOrdinal
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-!
# 内部自然数、ω 与编码标签在实际 C 层中的位置

全部内部自然数已在 Cω 中，而 ω 本身恰不在 Cω 中；任何高于 ω
的实际层都含 ω 和四个标签。本模块不声称三角数图 T 等集合参数
已经落级，其定义与有限图闭包仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageParameters

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : ThirdOrderSemantics.omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem naturals_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : subset_l ω α) : subset_l ω A :=
  fun n hn => PowerlessStageOrdinal.subset_l hℳ hω ht hT hA n (hωα n hn)

theorem omega_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) : member_l ℳ ω A :=
  PowerlessStageOrdinal.subset_l hℳ hω ht hT hA ω hωα

theorem tags_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : subset_l ω α) :
    member_l ℳ e A ∧ member_l ℳ t₁ A ∧ member_l ℳ t₂ A ∧ member_l ℳ t₃ A := by
  obtain ⟨he, h₁, h₂, h₃⟩ := PowerlessEvaluationTags.natural_l hℳ hω ht
  have h := naturals_l hℳ hω ht hT hA hωα
  exact ⟨h e he, h t₁ h₁, h t₂ h₂, h t₃ h₃⟩

theorem proper_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) :
    member_l ℳ ω A ∧ member_l ℳ e A ∧ member_l ℳ t₁ A ∧ member_l ℳ t₂ A ∧ member_l ℳ t₃ A :=
  ⟨omega_l hℳ hω ht hT hA hωα,
    tags_l hℳ hω ht hT hA (fun n hn => PowerlessOrdinal.transitive_l hA.1 ω n hωα hn)⟩

theorem first_l {A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ ω A) :
    subset_l ω A ∧ ¬member_l ℳ ω A := by
  refine ⟨naturals_l hℳ hω ht hT hA (fun _ hx => hx), ?_⟩
  intro h
  have h₀ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hA (PowerlessOmegaOrdinal.ordinal_l hℳ hω)).mp h
  exact PowerlessNatural.asymmetry_l hℳ h₀ h₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageParameters
