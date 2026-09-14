import BMSConstructibleBridge.ThirdOrderStageCore
import BMSConstructibleBridge.PowerlessOrdinalHistoryCut
import BMSConstructibleBridge.PowerlessOrdinalHistoryAbsolute
import BMSConstructibleBridge.PowerlessOrdinalRecursionAbsolute

/-!
# Cκ 中的一般前史与原序数关系见证

实际内部核心构造集合图，传递性及有序对闭包验证它与环境图相同。
前史可取任意域内集合 a，不将内部有限图闭包误用于无限序数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageRecursionClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem history_exists_l {f a : carrier_l ℳ} (hf : member_l ℳ f U) (ha : member_l ℳ a U) :
    ∃ H, member_l ℳ H U ∧ PowerlessOrdinalRecursion.history_l H f a := by
  let hU₀ : ∃ x, member_l ℳ x U := ⟨f, hf⟩
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hUT := PowerlessStageStructure.transitive_l h₀ hω ht hT hU
  obtain ⟨H, hH⟩ := PowerlessOrdinalHistoryCut.exists_l
    (ThirdOrderStageCore.models_l (hU₀ := hU₀) hℳ hω hκ ht hT hU) ⟨f, hf⟩ ⟨a, ha⟩
  exact ⟨H.val, H.property, (PowerlessOrdinalHistoryAbsolute.history_l h₀ hUT).mp hH⟩

theorem history_member_l {f a H : carrier_l ℳ} (hf : member_l ℳ f U) (ha : member_l ℳ a U)
    (hH : PowerlessOrdinalRecursion.history_l H f a) : member_l ℳ H U := by
  obtain ⟨K, hK, h⟩ := history_exists_l hℳ hω hκ ht hT hU hf ha
  exact PowerlessOrdinalHistoryCut.unique_l (ThirdOrderTheory.core_l hℳ) h hH ▸ hK

theorem relation_l {hU₀ : ∃ x, member_l ℳ x U} {A R : type_l U} :
    PowerlessOrdinalRelation.relation_l (ℳ := structure_l U hU₀) A R ↔
      PowerlessOrdinalRelation.relation_l A.val R.val := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hUT := PowerlessStageStructure.transitive_l h₀ hω ht hT hU
  apply PowerlessOrdinalRelationAbsolute.relation_l hUT
  rintro p ⟨x, y, hx, hy, _, hp⟩
  exact PowerlessStageGraphClosure.ordered_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (hUT A.val x A.property hx) (hUT A.val y A.property hy) hp

theorem relation_exists_l {A : carrier_l ℳ} (hA : member_l ℳ A U) :
    ∃ R, member_l ℳ R U ∧ PowerlessOrdinalRelation.relation_l A R := by
  let hU₀ : ∃ x, member_l ℳ x U := ⟨A, hA⟩
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l
    (ThirdOrderStageCore.models_l (hU₀ := hU₀) hℳ hω hκ ht hT hU) ⟨A, hA⟩
  exact ⟨R.val, R.property, (relation_l hℳ hω hκ ht hT hU).mp hR⟩

theorem relation_member_l {A R : carrier_l ℳ} (hA : member_l ℳ A U)
    (hR : PowerlessOrdinalRelation.relation_l A R) : member_l ℳ R U := by
  obtain ⟨S, hS, h⟩ := relation_exists_l hℳ hω hκ ht hT hU hA
  exact PowerlessOrdinalRelation.unique_l (ThirdOrderTheory.core_l hℳ) h hR ▸ hS

theorem relation_source_l {hU₀ : ∃ x, member_l ℳ x U} {Γ Δ : SortContext ℒ}
    (η : Env (structure_l U hU₀) Γ Δ) (A R : Term ℒ Γ Δ .set) :
    (PowerlessOrdinalRelation.relation_m A R).satisfies η ↔
      PowerlessOrdinalRelation.relation_l (A.eval η).val (R.eval η).val :=
  (PowerlessOrdinalRelation.relation_formula_l η A R).trans (relation_l hℳ hω hκ ht hT hU)

theorem recursion_source_l {hU₀ : ∃ x, member_l ℳ x U} {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (structure_l U hU₀)) Γ.length)
    (f A : type_l U) :
    (PowerlessOrdinalRecursion.recursion_m φ).satisfies
      (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔
      PowerlessOrdinalRecursion.recursion_l φ η f A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  apply PowerlessOrdinalRecursionAbsolute.source_l h₀
    (PowerlessStageStructure.transitive_l h₀ hω ht hT hU) φ η f A
  obtain ⟨R, hR, h⟩ := relation_exists_l hℳ hω hκ ht hT hU A.property
  exact ⟨⟨R, hR⟩, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageRecursionClosure
