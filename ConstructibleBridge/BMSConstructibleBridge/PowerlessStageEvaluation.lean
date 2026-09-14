import BMSConstructibleBridge.PowerlessStageStructure

/-!
# 实际层及其全部内部有限赋值与求值系统

把唯一层值、唯一赋值集合及唯一递归图合成纯关系。
系统存在性不要求层可数；不固定任何全局选择项。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage
open PowerlessEvaluationOperator (assignments_l assignments_m assignments_formula_l)
open PowerlessEvaluationRecursion (evaluation_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def system_l (ω e T t₁ t₂ t₃ α A S F : carrier_l ℳ) : Prop :=
  stage_l ω e T t₁ t₂ t₃ α A ∧ assignments_l ω A S ∧ evaluation_l ω e T A t₁ t₂ t₃ S F

def system_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ α A S F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (stage_m ω e T t₁ t₂ t₃ α A) (.conj (assignments_m ω A S)
    (PowerlessEvaluationPresentation.evaluation_m ω e T A t₁ t₂ t₃ S F))

theorem system_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ α A S F : Term ℒ Γ Δ .set) :
    (system_m ω e T t₁ t₂ t₃ α A S F).satisfies η ↔
      system_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (α.eval η) (A.eval η) (S.eval η) (F.eval η) := by
  simp only [system_m, system_l, Formula.satisfies, stage_formula_l hℳ,
    assignments_formula_l, PowerlessEvaluationPresentation.evaluation_formula_l hℳ]

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω α : carrier_l ℳ} (hω : omega_l ω) (hα : PowerlessOrdinal.ordinal_l α)
    (e T t₁ t₂ t₃ : carrier_l ℳ) : ∃ A S F, system_l ω e T t₁ t₂ t₃ α A S F := by
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω hα e T t₁ t₂ t₃
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω A
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T A t₁ t₂ t₃ S
  exact ⟨A, S, F, hA, hS, hF⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A B S R F G : carrier_l ℳ} (hω : omega_l ω)
    (hA : system_l ω e T t₁ t₂ t₃ α A S F) (hB : system_l ω e T t₁ t₂ t₃ α B R G) :
    A = B ∧ S = R ∧ F = G := by
  have h₁ := PowerlessHierarchyStage.unique_l hℳ hω hA.1 hB.1
  subst B
  have h₂ : S = R := (PowerlessTheory.ext_l hℳ).eq_of_same_members S R
    (fun f => (hA.2.1 f).trans (hB.2.1 f).symm)
  subst R
  obtain ⟨H, _, hH⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T A t₁ t₂ t₃ S
  exact ⟨rfl, rfl, (hH F hA.2.2).trans (hH G hB.2.2).symm⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluation
