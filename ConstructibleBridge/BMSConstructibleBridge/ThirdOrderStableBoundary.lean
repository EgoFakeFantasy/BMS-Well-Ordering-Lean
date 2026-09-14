import BMSConstructibleBridge.ThirdOrderStablePair
import BMSConstructibleBridge.PowerlessBoundaryFamily

/-!
# 工作理论中的全内部有限层边界及统一图

先由实际稳定对构造每个内部层的最小边界，再从纯总唯一关系收集
为真实 ω→κ 函数。最后使用已证可数取界，不假定外部可数性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStableBoundary

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessStableBoundary

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) : ∃ σ, boundary_l ω e T t₁ t₂ t₃ κ n σ := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨α, β, hα, hβ, _, _, h⟩ := ThirdOrderStablePair.exists_l hℳ hω hκ ht hT
    (ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ)
  exact PowerlessStableBoundary.exists_l h₀ ⟨hα, β, hβ, h n hn⟩

theorem graph_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T) :
    ∃! F, PowerlessBoundaryFamily.family_l ω e T t₁ t₂ t₃ κ F := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (fun _ => κ)))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    boundary_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there .here))
      (.fvar .here)
  have h : ∀ n σ, φ.satisfies (((PowerlessComprehension.env_l η).pushFree n).pushFree σ) ↔
      boundary_l ω e T t₁ t₂ t₃ κ n σ := by
    intro n σ
    rw [boundary_formula_l h₀]
    rfl
  obtain ⟨F, B, hF, _, h₁⟩ := PowerlessMapping.exists_l h₀ φ η ω
    (fun n hn => (exists_l hℳ hω hκ ht hT hn).imp fun σ hσ => (h n σ).mpr hσ)
    (fun n _ σ τ hσ hτ => PowerlessStableBoundary.unique_l h₀ ((h n σ).mp hσ) ((h n τ).mp hτ))
  have h₂ : ∀ n, member_l ℳ n ω → ∀ σ, value_l F n σ ↔ boundary_l ω e T t₁ t₂ t₃ κ n σ :=
    fun n hn σ => (h₁ n hn σ).trans (h n σ)
  have h₃ := PowerlessFunction.range_l h₀ hF
    (fun n σ hσ => ((h₂ n (PowerlessFunction.value_mem_l h₀ hF hσ).1 σ).mp hσ).1.1)
  have h₄ : PowerlessBoundaryFamily.family_l ω e T t₁ t₂ t₃ κ F :=
    ⟨h₃, fun n σ hn => h₂ n hn σ⟩
  exact ⟨F, h₄, fun G hG => PowerlessBoundaryFamily.unique_l h₀ hG h₄⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T) :
    ∃ F ρ, PowerlessBoundaryFamily.family_l ω e T t₁ t₂ t₃ κ F ∧ member_l ℳ ρ κ ∧
      ∀ n σ, value_l F n σ → member_l ℳ σ ρ := by
  obtain ⟨F, hF, _⟩ := graph_l hℳ hω hκ ht hT
  obtain ⟨ρ, hρ, h⟩ := ThirdOrderCountableBounds.omega_l hℳ hω hκ hF.1
  exact ⟨F, ρ, hF, hρ, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStableBoundary
