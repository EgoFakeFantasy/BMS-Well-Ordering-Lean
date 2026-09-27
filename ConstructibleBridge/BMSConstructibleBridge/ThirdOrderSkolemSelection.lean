import BMSConstructibleBridge.PowerlessSkolemStep
import BMSConstructibleBridge.ThirdOrderSkolemBound

/-!
# 层次指标上的统一见证推进函数

对整个 κ 作一次内部纯公式选择，得到实际 H:κ→κ。每步严格增大指标，
并收进前级全部真实存在请求的见证。最后与 Cκ 的实际求值系统接合；
这里仍不把这一个函数等同于已完成的 ω 迭代及其极限闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemSelection

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage PowerlessSkolemStep

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U) :
    ∃ H, map_l H κ κ ∧ ∀ α β, value_l H α β → step_l ω e T t₁ t₂ t₃ κ U F α β := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 9 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (Fin.cases κ (Fin.cases U (fun _ => F)))))))), free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    step_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.fvar (.there .here)) (.fvar .here)
  have h : ∀ α β, φ.satisfies (((PowerlessComprehension.env_l η).pushFree α).pushFree β) ↔
      step_l ω e T t₁ t₂ t₃ κ U F α β := fun α β => step_formula_l h₀ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨H, D, hH, h₁⟩ := ThirdOrderSelection.exists_l hℳ φ η κ (fun α hα => by
    obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hα) e T t₁ t₂ t₃
    obtain ⟨β, B, hβ, hαβ, hB, _, h₂⟩ := ThirdOrderSkolemBound.exists_l hℳ (F := F) hω hκ hU hU₀ hα hA
    exact ⟨β, (h α β).mpr ⟨hαβ, hβ, A, B, hA, hB, h₂⟩⟩)
  have h₂ : ∀ α β, value_l H α β → step_l ω e T t₁ t₂ t₃ κ U F α β :=
    fun α β hβ => (h α β).mp (h₁ α β hβ)
  exact ⟨H, PowerlessFunction.range_l h₀ hH (fun α β hβ => (h₂ α β hβ).2.1), h₂⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T) :
    ∃ U S F H, stage_l ω e T t₁ t₂ t₃ κ U ∧ (∃ x, member_l ℳ x U) ∧
      PowerlessNaturalOrder.transitive_l U ∧
      (∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n U) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F ∧ map_l H κ κ ∧
      ∀ α β, value_l H α β → step_l ω e T t₁ t₂ t₃ κ U F α β := by
  obtain ⟨U, S, F, hU, hU₀, h₁, hS, hF, _⟩ := ThirdOrderHierarchyLimit.system_l hℳ hω hκ ht hT
  obtain ⟨H, hH, h₂⟩ := exists_l hℳ (F := F) hω hκ hU hU₀
  exact ⟨U, S, F, H, hU, hU₀, h₁, hS, hF, hH, h₂⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemSelection

