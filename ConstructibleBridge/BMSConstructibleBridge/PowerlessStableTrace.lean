import BMSConstructibleBridge.PowerlessStageFiniteSubsets
import BMSConstructibleBridge.PowerlessStageStability

/-!
# 到指定上端点的真实稳定关系迹

直接在内部有限初段中分离哪些列标签稳定于给定端点。
与二元索引图不同，这里不需要有限乘积枚举；全部内部长度都由既有
有限子集落级定理处理。上端点、标签图和源公式参数可在小层外。
这里只构造反射输入的真假记录，不把端点参数带入低层反射环境。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableTrace

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 新自由槽是列指标，唯一存在槽是该列标签；使用原始稳定公式。 -/
def trace_m {Γ : SortContext ℒ} (ω e T t₁ t₂ t₃ k β g : Term ℒ [] Γ .set) :
    Formula ℒ [] (.set :: Γ) :=
  let w (s : Term ℒ [] Γ .set) :=
    (s.weakenFree SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.conj
    (SecondOrderObjectSyntax.value_m (w g) (.fvar .here) (.bvar .here))
    (PowerlessStageStability.stable_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w k)
      (.bvar .here) (w β)))

theorem trace_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (ω e T t₁ t₂ t₃ k β g : Term ℒ [] Γ .set)
    (j : carrier_l ℳ) :
    (trace_m ω e T t₁ t₂ t₃ k β g).satisfies (η.pushFree j) ↔
      ∃ a, value_l (g.eval η) j a ∧ PowerlessStageStability.stable_l
        (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (k.eval η)
        a (β.eval η) := by
  simp only [trace_m, Formula.satisfies, value_formula_l,
    PowerlessStageStability.stable_formula_l hℳ, Term.eval_weakenBound, Term.eval_weakenFree]
  rfl

/-- 真实稳定迹是小层中的集合；没有乘积枚举或层内分离前提。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α) (hq : member_l ℳ q ω)
    {Γ : SortContext ℒ}
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (w z V s₁ s₂ s₃ k β g : Term ℒ [] Γ .set) :
    ∃ D, member_l ℳ D A ∧ ∀ j, member_l ℳ j D ↔ member_l ℳ j q ∧
      ∃ a, value_l (g.eval (PowerlessComprehension.env_l η)) j a ∧
        PowerlessStageStability.stable_l
          (w.eval (PowerlessComprehension.env_l η)) (z.eval (PowerlessComprehension.env_l η))
          (V.eval (PowerlessComprehension.env_l η)) (s₁.eval (PowerlessComprehension.env_l η))
          (s₂.eval (PowerlessComprehension.env_l η)) (s₃.eval (PowerlessComprehension.env_l η))
          (k.eval (PowerlessComprehension.env_l η)) a (β.eval (PowerlessComprehension.env_l η)) := by
  obtain ⟨D, hD⟩ := PowerlessComprehension.separation_l hℳ (trace_m w z V s₁ s₂ s₃ k β g) η q
  refine ⟨D, PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hA hα hωα q hq D
    (fun j hj => ((hD j).mp hj).1), ?_⟩
  intro j
  exact (hD j).trans (and_congr Iff.rfl
    (trace_formula_l hℳ (PowerlessComprehension.env_l η) w z V s₁ s₂ s₃ k β g j))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStableTrace
