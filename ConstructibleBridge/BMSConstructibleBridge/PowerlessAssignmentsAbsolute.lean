import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 原有限赋值全集公式的传递子域绝对性

全称量化的候选图可能在域外；必须用有限图闭包取回，不能只处理域内图。
此处 S 已是成员域中的参数，不宣称任意 A 的赋值全集 S 自动属于同一层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem assignments_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω A S : type_l B}
    (hG : ∀ n, member_l ℳ n ω.val → ∀ f, map_l f n A.val → member_l ℳ f B) :
    PowerlessEvaluationOperator.assignments_l (ℳ := structure_l B hB) ω A S ↔
      PowerlessEvaluationOperator.assignments_l ω.val A.val S.val := by
  constructor
  · intro h f
    constructor
    · intro hf
      have hfB := hBT S.val f S.property hf
      obtain ⟨n, hn, hF⟩ := (h ⟨f, hfB⟩).mp hf
      exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mp hF⟩
    · rintro ⟨n, hn, hF⟩
      have hnB := hBT ω.val n ω.property hn
      have hfB := hG n hn f hF
      exact (h ⟨f, hfB⟩).mpr ⟨⟨n, hnB⟩, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hF⟩
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, hF⟩ := (h f.val).mp hf
      have hnB := hBT ω.val n ω.property hn
      exact ⟨⟨n, hnB⟩, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hF⟩
    · rintro ⟨n, hn, hF⟩
      exact (h f.val).mpr ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mp hF⟩

theorem source_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l B hB) Γ Δ) (ω A S : Term ℒ Γ Δ .set)
    (hG : ∀ n, member_l ℳ n (ω.eval η).val → ∀ f, map_l f n (A.eval η).val → member_l ℳ f B) :
    Formula.satisfies η (PowerlessEvaluationOperator.assignments_m ω A S) ↔
      PowerlessEvaluationOperator.assignments_l (ω.eval η).val (A.eval η).val (S.eval η).val :=
  (PowerlessEvaluationOperator.assignments_formula_l η ω A S).trans (assignments_l hBT hG)

theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β) :
    ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ w : type_l B, w.val = ω ∧ ∀ A S : type_l B,
      PowerlessEvaluationOperator.assignments_l (ℳ := structure_l B hB₀) w A S ↔
        PowerlessEvaluationOperator.assignments_l ω A.val S.val := by
  have hωB := PowerlessStageParameters.omega_l hℳ hω ht hT hB hωβ
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hβ
    (fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx)
  refine ⟨⟨ω, hωB⟩, ⟨ω, hωB⟩, rfl, ?_⟩
  intro A S
  apply assignments_l hBT
  intro n hn f hf
  apply hG n hn f
  exact PowerlessFunction.range_l hℳ hf
    (fun x y hxy => hBT A.val y A.property (PowerlessFunction.value_mem_l hℳ hf hxy).2)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsAbsolute
