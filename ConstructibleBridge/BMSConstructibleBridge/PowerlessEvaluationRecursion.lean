import BMSConstructibleBridge.PowerlessEvaluationStep
import BMSConstructibleBridge.PowerlessEvaluationHistory
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-!
# 全内部编号的实际求值图

实例化已证内部序数递归，构造每个编号对应的真值子集，并证明全部
内部编号上的局部方程。这不是源公式编译正确性或完整合法语法定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationStep

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def evaluation_l (ω e T A t₁ t₂ t₃ S F : carrier_l ℳ) : Prop :=
  ∃ B, map_l F ω B ∧ ∀ n Y, value_l F n Y → ∃ H,
    PowerlessOrdinalRecursion.history_l H F n ∧ step_l ω e T A t₁ t₂ t₃ S H n Y

theorem recursion_iff_l (ω e T A t₁ t₂ t₃ S F : carrier_l ℳ) :
    PowerlessOrdinalRecursion.recursion_l operator_m (env_l ω e T A t₁ t₂ t₃ S) F ω ↔
      evaluation_l ω e T A t₁ t₂ t₃ S F := by
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply forall_congr'
  intro n
  apply forall_congr'
  intro Y
  apply imp_congr_right
  intro _
  apply exists_congr
  intro H
  exact and_congr Iff.rfl (operator_formula_l ω e T A t₁ t₂ t₃ S H n Y)

theorem exists_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (e T A t₁ t₂ t₃ S : carrier_l ℳ) :
    ∃! F, evaluation_l ω e T A t₁ t₂ t₃ S F := by
  obtain ⟨F, hF, h₀⟩ := PowerlessOrdinalRecursion.exists_unique_l hℳ operator_m (env_l ω e T A t₁ t₂ t₃ S)
    (fun n H Y Z hY hZ => PowerlessEvaluationStep.unique_l hℳ
      ((operator_formula_l ω e T A t₁ t₂ t₃ S H n Y).mp hY)
      ((operator_formula_l ω e T A t₁ t₂ t₃ S H n Z).mp hZ))
    (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun n _ H => by
      obtain ⟨Y, hY⟩ := PowerlessEvaluationStep.exists_l hℳ ω e T A t₁ t₂ t₃ S H n
      exact ⟨Y, (operator_formula_l ω e T A t₁ t₂ t₃ S H n Y).mpr hY⟩)
  exact ⟨F, (recursion_iff_l ω e T A t₁ t₂ t₃ S F).mp hF,
    fun G hG => h₀ G ((recursion_iff_l ω e T A t₁ t₂ t₃ S G).mpr hG)⟩

theorem equation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F n : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : evaluation_l ω e T A t₁ t₂ t₃ S F) (hn : member_l ℳ n ω) (f : carrier_l ℳ) :
    PowerlessEvaluationClause.query_l F n f ↔
      member_l ℳ f S ∧ PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ F n f := by
  obtain ⟨B, hF, h₀⟩ := hF
  obtain ⟨Y, hY, _⟩ := hF.2 n hn
  obtain ⟨H, hH, h₁⟩ := h₀ n Y hY.2
  have h₂ : PowerlessEvaluationClause.query_l F n f ↔ member_l ℳ f Y := by
    constructor
    · rintro ⟨Z, hZ, hf⟩
      exact (PowerlessFunction.value_unique_l hℳ hF hZ hY.2) ▸ hf
    · intro hf
      exact ⟨Y, hY.2, hf⟩
  exact h₂.trans ((h₁ f).trans (and_congr Iff.rfl (PowerlessEvaluationHistory.clause_l hℳ hω he hT hH)))

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : PowerlessTriangular.triangular_l ω e T) (A t₁ t₂ t₃ : carrier_l ℳ) :
    ∃ S F, (∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A) ∧
      evaluation_l ω e T A t₁ t₂ t₃ S F ∧
      ∀ n, member_l ℳ n ω → ∀ f, PowerlessEvaluationClause.query_l F n f ↔
        member_l ℳ f S ∧ PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ F n f := by
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω A
  obtain ⟨F, hF, _⟩ := exists_unique_l hℳ hω e T A t₁ t₂ t₃ S
  exact ⟨S, F, hS, hF, fun _ hn f => equation_l hℳ hω he hT hF hn f⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRecursion
