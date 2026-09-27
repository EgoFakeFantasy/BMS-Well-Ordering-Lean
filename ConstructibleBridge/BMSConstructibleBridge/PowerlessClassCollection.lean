import BMSConstructibleBridge.PowerlessClassBasic

/-!
# 层次类内的原公式收集

将原二绑定变量矩阵打开为实际二元请求，在包含输入集合的
更高层关闭类内见证。收集集取该实际层，并由其后继层证明
它属于层次类；不假定类预先满足收集，也不要求选择见证函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassCollection

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 即使正文仅对部分输入有类内见证，也存在同一个类内收集集。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [.set, .set] Δ)
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Δ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Δ .set) (A : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hA : PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) A) :
    let P := PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η))
    let ψ := PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ
    ∃ B, P B ∧ ∀ x, member_l ℳ x A →
      (∃ y, P y ∧ ψ.satisfies (((PowerlessComprehension.env_l η).pushBound x).pushBound y)) →
      ∃ y, member_l ℳ y B ∧ P y ∧
        ψ.satisfies (((PowerlessComprehension.env_l η).pushBound x).pushBound y) := by
  let ρ := PowerlessComprehension.env_l η
  let P := PowerlessSourceWitnessDomain.domain_l
    (ω.eval ρ) (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  let ψ := PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ
  let χ := PowerlessSourceOpening.form_m ψ
  have hφ (x y : carrier_l ℳ) :
      χ.satisfies ((ρ.pushFree x).pushFree y) ↔ ψ.satisfies ((ρ.pushBound x).pushBound y) :=
    PowerlessSourceOpening.witness_l ψ (ρ.pushBound x) y
  obtain ⟨α, V, hV, hAV⟩ := hA
  obtain ⟨δ, U, _, hαδ, hU, h⟩ := PowerlessSourceWitnessDomain.exists_l hℳ
    χ η ω e T t₁ t₂ t₃ α hω ht.1 hV.1
  have hAU := PowerlessStageStructure.subset_l hℳ hω hV hU hαδ A hAV
  have h₀ := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h₁ : P U := PowerlessClassBasic.stage_member_l hℳ hω ht hT hU
  refine ⟨U, h₁, ?_⟩
  rintro x hx ⟨y, hy, hψ⟩
  obtain ⟨z, hz, hχ⟩ := h x (h₀ A x hAU hx) ⟨y, hy, (hφ x y).mpr hψ⟩
  exact ⟨z, hz, ⟨δ, U, hU, hz⟩, (hφ x z).mp hχ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassCollection
