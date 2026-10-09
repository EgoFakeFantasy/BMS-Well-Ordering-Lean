import BMSConstructibleBridge.SecondOrderCofinalLimitDerives
import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds
import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfaction

/-! # 实际共尾层中的有限参数与 Sat 共同收纳

先取外部有限环境的共同层，再构造更大的共尾极限阶段。所有见证均实际
存在，不再要求调用者假设共尾层。环境包括给定赋值域 A，不能将本结论
误作预先固定 C 对全部 A∈C 的统一闭包，更不是任意内部集合族的 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeCofinalLimitBounds (cofinal_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem parameters_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) :
    ∃ β C, level_l hℳ B β C ∧ limit_l hℳ β ∧ cofinal_l β ∧ mem_l hℳ X.val C ∧
      ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C := by
  obtain ⟨a, c, hc, hXc, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η X
  obtain ⟨β, hβ, haβ, hLimit, hCofinal⟩ := SecondOrderCofinalLimitDerives.exists_l hℳ a
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hc)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hLift x (hx : mem_l hℳ x c) := PowerlessRelativeLevelClosure.subset_l hℳ hBase haβ hc hC x hx
  exact ⟨β, C, hC, hLimit, hCofinal, hLift X.val hXc, fun s v => hLift _ (hParams s v)⟩

theorem satisfaction_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) (ω.eval η)) {F : type_l hℳ B}
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase)
      (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (N.eval η) F) :
    ∃ β C, ∃ R : type_l hℳ B, level_l hℳ B β C ∧ limit_l hℳ β ∧ cofinal_l β ∧
      mem_l hℳ F.val C ∧ (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C) ∧
        mem_l hℳ R.val C ∧
          PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
            (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) F R := by
  obtain ⟨β, C, hC, hLimit, hCofinal, hFC, hParams⟩ := parameters_l η F
  obtain ⟨R, hRC, hSat⟩ := PowerlessRelativeCofinalSatisfaction.exists_l (F := F)
    hC hLimit hCofinal η ω e N T A t₁ t₂ t₃ hParams hω hFC hStatic
  exact ⟨β, C, R, hC, hLimit, hCofinal, hFC, hParams, hRC, hSat⟩

#print axioms parameters_l
#print axioms satisfaction_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClosure
