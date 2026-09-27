import BMSConstructibleBridge.PowerlessRelationDiagram
import BMSConstructibleBridge.PowerlessStageStability

/-!
# 原稳定关系的内部有限图

实际使用 `PowerlessStageStability.stable_m` 的六个系统见证与原分类查询，
不改为替代关系。稳定标签及稳定关系参数可位于小层外，有限索引图仍落级。
尚不证明这个源公式具有 Hunter 反射所需的复杂度，也不假设稳定对存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableDiagram

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 以两个新自由槽作为左右标签，其余项保持原参数环境。 -/
def relation_m {Γ : SortContext ℒ} (ω e T t₁ t₂ t₃ k : Term ℒ [] Γ .set) :
    Formula ℒ [] (.set :: .set :: Γ) :=
  let w (s : Term ℒ [] Γ .set) :=
    (s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessStageStability.stable_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w k)
    (.fvar (.there .here)) (.fvar .here)

theorem relation_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (ω e T t₁ t₂ t₃ k : Term ℒ [] Γ .set)
    (a b : carrier_l ℳ) :
    (relation_m ω e T t₁ t₂ t₃ k).satisfies ((η.pushFree a).pushFree b) ↔
      PowerlessStageStability.stable_l (ω.eval η) (e.eval η) (T.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (k.eval η) a b := by
  simp only [relation_m, PowerlessStageStability.stable_formula_l hℳ, Term.eval_weakenFree]
  rfl

/-- 在真实内部有限索引乘积上筛选原稳定事实，构造位于小层的完整关系图。
乘积枚举由内部集合论实际构造，不作为额外前提，也不由外部有限列表代替。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q P : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hP : PowerlessProduct.product_l p q P)
    {Γ : SortContext ℒ}
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (w z V s₁ s₂ s₃ k : Term ℒ [] Γ .set) (f g : carrier_l ℳ) :
    ∃ D, member_l ℳ D A ∧ ∀ x, member_l ℳ x D ↔ member_l ℳ x P ∧
      ∃ i j a b, ordered_l i j x ∧ value_l f i a ∧ value_l g j b ∧
        PowerlessStageStability.stable_l
          (w.eval (PowerlessComprehension.env_l η)) (z.eval (PowerlessComprehension.env_l η))
          (V.eval (PowerlessComprehension.env_l η)) (s₁.eval (PowerlessComprehension.env_l η))
          (s₂.eval (PowerlessComprehension.env_l η)) (s₃.eval (PowerlessComprehension.env_l η))
          (k.eval (PowerlessComprehension.env_l η)) a b := by
  obtain ⟨D, hD, h⟩ := PowerlessRelationDiagram.separation_l hℳ hω ht hT hA hα hωα
    hp hq hP (relation_m w z V s₁ s₂ s₃ k) η f g
  refine ⟨D, hD, fun x => (h x).trans (and_congr Iff.rfl ?_)⟩
  simp only [PowerlessRelationDiagram.selected_l, relation_formula_l hℳ]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableDiagram
