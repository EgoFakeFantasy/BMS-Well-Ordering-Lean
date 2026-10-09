import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-!
# 图商自然数上的纯公式归纳

背景只有原二阶语言的 `SecondOrderArithmetic.theory_m`。归纳对象是指定纯集合
公式的图码翻译；其正式推导由 `GraphTranslation.induction_m` 给出。本文件将
该实例的可靠性接回商结构，供算术递归唯一性使用，不假设商满足 Collection，
也不对模型内部自然数使用宿主归纳。这是固定高度 BMS 对象推导的辅助接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientInduction

open Logic FirstOrder SecondOrderSyntax SecondOrderInterpretation

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- 对全部内部数应用实际翻译公式的归纳，包括非标准数。 -/
theorem induction_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hM) [] Δ)
    (h₀ : φ.satisfies (η.pushFree
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val))
    (h₁ : ∀ n : SecondOrderModel.num_l M,
      φ.satisfies (η.pushFree (PowerlessBMSQuotientCoding.numberCode_l C n).val) →
      φ.satisfies (η.pushFree
        (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.succ_l n)).val)) :
    ∀ n : SecondOrderModel.num_l M,
      φ.satisfies (η.pushFree (PowerlessBMSQuotientCoding.numberCode_l C n).val) := by
  obtain ⟨ρ, τ, hη⟩ := source_surj_l hM η
  let ξ := (target_l ρ τ).pushFree C.less
  have hφ (n : SecondOrderModel.num_l M) :
      (GraphTranslation.form_m φ).satisfies (ξ.pushFree n) ↔
        φ.satisfies (η.pushFree (PowerlessBMSQuotientCoding.numberCode_l C n).val) := by
    have h := form_l hM φ ρ
      (push_l (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n) τ)
    have henv : source_l hM ρ
        (push_l (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n) τ) =
        η.pushFree (PowerlessBMSQuotientCoding.numberCode_l C n).val := by
      rw [← hη]
      apply Env.ext
      · intro s v
        nomatch v
      · intro s v
        cases v <;> rfl
    rw [henv] at h
    exact h
  exact SecondOrderModel.induct_l hM (GraphTranslation.form_m φ)
    (GraphTranslation.form_pure_m φ) ξ _ hφ h₀ h₁

#print axioms induction_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientInduction
