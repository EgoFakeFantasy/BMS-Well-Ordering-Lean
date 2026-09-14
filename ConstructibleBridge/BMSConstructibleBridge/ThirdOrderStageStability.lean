import BMSConstructibleBridge.PowerlessCoreStageStability
import BMSConstructibleBridge.ThirdOrderStageSystem
import BMSConstructibleBridge.PowerlessLevyAgreementAbsolute
import BMSConstructibleBridge.PowerlessStageStability

/-!
# Cκ 中原有限层稳定关系的绝对性

原 stable_m 的六个系统见证由实际成员性取回；分类证书及全部赋值图
也由已证明的闭包取得。结论未作 BM4 复杂度重编号，不替代后续反射合同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageStability

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U κ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val) (hκ : ThirdOrderOmegaOne.first_l ω.val κ)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val κ U)

include hℳ hω hκ ht hT hU

theorem limit_l {α : type_l U} :
    PowerlessStagePair.limit_l (ℳ := structure_l U hU₀) α ↔ PowerlessStagePair.limit_l α.val :=
  PowerlessCoreStageStability.limit_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)

theorem proper_l {α β : type_l U} :
    PowerlessStagePair.proper_l (ℳ := structure_l U hU₀) ω α β ↔
      PowerlessStagePair.proper_l ω.val α.val β.val :=
  PowerlessCoreStageStability.proper_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)

theorem agreement_l {A F G n : type_l U} :
    PowerlessLevyAgreement.agreement_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ A F G n ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val G.val n.val :=
  PowerlessCoreStageStability.agreement_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem stable_l {n α β : type_l U} :
    PowerlessStageStability.stable_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n α β ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val α.val β.val :=
  PowerlessCoreStageStability.stable_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem source_l {hU₀ : ∃ x, member_l ℳ x U}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n α β : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageStability.stable_m w z V s₁ s₂ s₃ n α β).satisfies η ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (n.eval η).val (α.eval η).val (β.eval η).val :=
  PowerlessCoreStageStability.source_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) η w z V s₁ s₂ s₃ n α β hw hz hV hs₁ hs₂ hs₃

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageStability
