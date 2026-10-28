import BMSConstructibleBridge.PowerlessBMSQuotientInduction
import BMSConstructibleBridge.SecondOrderListInduction

/-! # 带环境商参数的实际纯公式强归纳

参数只在环境商中取值，不要求属于相对类。先读取同一纯公式的原图码
翻译，再在原 Z₂ 模型内取最小反例。性质 P 必须由明确的公式及环境
逐数定义，不能从本接口得到内部自然数序的宿主良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientStrongInduction

open Logic FirstOrder SecondOrderInterpretation PowerlessBMSQuotientCoding

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem strong_induct_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (P : SecondOrderModel.num_l ℳ → Prop)
    (hP : ∀ n, φ.satisfies (η.pushFree (numberCode_l K n).val) ↔ P n)
    (hStep : ∀ n, (∀ k, SecondOrderOrder.lt_l k n → P k) → P n) : ∀ n, P n := by
  obtain ⟨ρ, τ, hη⟩ := source_surj_l hℳ η
  let ξ := (target_l ρ τ).pushFree K.less
  have hφ (n : SecondOrderModel.num_l ℳ) :
      (GraphTranslation.form_m φ).satisfies (ξ.pushFree n) ↔ P n := by
    have h := form_l hℳ φ ρ
      (push_l (SecondOrderNaturalGraph.code_l hℳ K.less K.less_spec n) τ)
    have hEnv : source_l hℳ ρ
        (push_l (SecondOrderNaturalGraph.code_l hℳ K.less K.less_spec n) τ) =
        η.pushFree (numberCode_l K n).val := by
      rw [← hη]
      apply Env.ext (bound := []) (fun {_} v => nomatch v)
      · intro s v
        cases v <;> rfl
    rw [hEnv] at h
    exact h.trans (hP n)
  exact SecondOrderListInduction.strong_induct_l hℳ (GraphTranslation.form_m φ)
    (GraphTranslation.form_pure_m φ) ξ P hφ hStep

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientStrongInduction
