import BMSConstructibleBridge.PowerlessEvaluationClauseAbsolute
import BMSConstructibleBridge.PowerlessEvaluationStep

/-!
# 原求值分离算子的传递子域绝对性

全称赋值候选由 Y 或 S 的成员条件取回。只用原局部求值的逐点等价；
实际极限层出口消去该条件，不把小结构假设为无幂集核心的模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem step_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω e T A t₁ t₂ t₃ S H n Y : type_l B}
    (hC : ∀ f : type_l B,
      PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ H n f ↔
        PowerlessEvaluationClause.clause_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val H.val n.val f.val) :
    PowerlessEvaluationStep.step_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ S H n Y ↔
      PowerlessEvaluationStep.step_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val H.val n.val Y.val := by
  constructor
  · intro h f
    constructor
    · intro hf
      have hfB := hBT Y.val f Y.property hf
      obtain ⟨hS, h⟩ := (h ⟨f, hfB⟩).mp hf
      exact ⟨hS, (hC ⟨f, hfB⟩).mp h⟩
    · rintro ⟨hf, hc⟩
      have hfB := hBT S.val f S.property hf
      exact (h ⟨f, hfB⟩).mpr ⟨hf, (hC ⟨f, hfB⟩).mpr hc⟩
  · intro h f
    exact (h f.val).trans (and_congr Iff.rfl (hC f).symm)

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (ω e T A t₁ t₂ t₃ S H n Y : Term ℒ Γ Δ .set)
    (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (hT : PowerlessTriangular.triangular_l (ω.eval η).val (e.eval η).val (T.eval η).val)
    (hI : ∀ x, member_l ℳ x (ω.eval η).val → ∀ F,
      PowerlessAddition.iteration_l (ω.eval η).val (e.eval η).val x F → member_l ℳ F B)
    (hG : ∀ k, member_l ℳ k (ω.eval η).val → ∀ g, map_l g k (A.eval η).val → member_l ℳ g B) :
    Formula.satisfies η (PowerlessEvaluationStep.step_m ω e T A t₁ t₂ t₃ S H n Y) ↔
      PowerlessEvaluationStep.step_l (ω.eval η).val (e.eval η).val (T.eval η).val (A.eval η).val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val (S.eval η).val (H.eval η).val (n.eval η).val (Y.eval η).val :=
  (PowerlessEvaluationStep.step_formula_l η ω e T A t₁ t₂ t₃ S H n Y).trans
    (step_l hBT (fun _ => PowerlessEvaluationClauseAbsolute.clause_l hℳ hBT hω he hT hI hG))

theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β) :
    ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ w z U s₁ s₂ s₃ : type_l B,
      w.val = ω ∧ z.val = e ∧ U.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      ∀ A S H n Y : type_l B,
        PowerlessEvaluationStep.step_l (ℳ := structure_l B hB₀) w z U A s₁ s₂ s₃ S H n Y ↔
          PowerlessEvaluationStep.step_l ω e T A.val t₁ t₂ t₃ S.val H.val n.val Y.val := by
  obtain ⟨hB₀, w, z, U, s₁, s₂, s₃, hw, hz, hU, h₁, h₂, h₃, hC⟩ :=
    PowerlessEvaluationClauseAbsolute.stage_l hℳ hω ht hT hB hωβ hβ
  refine ⟨hB₀, w, z, U, s₁, s₂, s₃, hw, hz, hU, h₁, h₂, h₃, ?_⟩
  intro A S H n Y
  have hC₀ : ∀ f : type_l B,
      PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB₀) w z U A s₁ s₂ s₃ H n f ↔
        PowerlessEvaluationClause.clause_l w.val z.val U.val A.val s₁.val s₂.val s₃.val H.val n.val f.val := by
    simpa only [hw, hz, hU, h₁, h₂, h₃] using hC A H n
  simpa only [hw, hz, hU, h₁, h₂, h₃] using
    (step_l (PowerlessStageStructure.transitive_l hℳ hω ht hT hB) (S := S) (Y := Y) hC₀)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepAbsolute
