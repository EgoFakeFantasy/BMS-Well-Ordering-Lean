import BMSConstructibleBridge.SecondOrderFullTransfer
import BMSConstructibleBridge.PowerlessBMSQuotientReals
import BMSConstructibleBridge.PowerlessBMSQuotientTranslation
import BMSConstructibleBridge.PowerlessBMSObjectProof
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 原 Z₂ 定理的纯集合算术闭包

商内自然数与原数域同构，商内 ω 子集与原实数双向全域且单值。因而任意
合法二阶算术公式（包括集合量词及集合等式）都保持真值。结合已经验证的
关系式算术翻译，原 Z₂ 定理的纯集合闭包也有原图翻译的对象推导。
这里只传输已有推导，不提供未证 BMS 句或完整 Collection 的证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmeticTransfer

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientTranslation

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 集合对应的四个条件都是 Prop 证书，不构造集合域的选择函数。 -/
theorem coverage_l (C : source_coding_l hℳ) :
    SecondOrderFullTransfer.coverage_l (PowerlessBMSQuotientMultiplication.correspondence_l C) where
  left_total := PowerlessBMSQuotientReals.trace_exists_l C
  right_total := representative_exists_l C
  left_unique := PowerlessBMSQuotientReals.representative_unique_l C
  right_unique := PowerlessBMSQuotientReals.trace_unique_l C

theorem closed_l (C : source_coding_l hℳ) (φ : Sentence SecondOrderSyntax.signature_m)
    (hφ : SecondOrderArithmetic.language_m φ = true) :
    φ.TrueIn (arithmetic_l C) ↔ φ.TrueIn ℳ := by
  apply SecondOrderFullTransfer.formula_l
    (PowerlessBMSQuotientMultiplication.correspondence_l C) (coverage_l C) φ hφ
  constructor <;> intro s v <;> nomatch v

/-- 不要求商满足完整无幂集集合论；仅使用已经实现的算术图和原 Z₂ 推导。 -/
theorem closure_l (C : source_coding_l hℳ) (φ : Sentence SecondOrderSyntax.signature_m)
    (hφ : SecondOrderArithmetic.language_m φ = true) (h : φ.TrueIn ℳ) :
    (PowerlessBMSObjectProof.closure_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (PowerlessBMSObjectProof.closure_formula_l φ).mpr
  intro ω e hω he
  let ηω := (Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree ω
  have hω' : SecondOrderOmega.omega_l hℳ ω :=
    (SecondOrderOmegaSyntax.omega_l hℳ ηω (.fvar .here)).mp
      ((ThirdOrderSemantics.omega_formula_l ηω (.fvar .here)).mpr hω)
  have hωC := SecondOrderOmega.unique_l hℳ hω' C.omega_spec
  have heC : e = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l C x)
  subst ω
  subst e
  exact (PowerlessBMSQuotientTranslation.formula_l C Env.empty
    (((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushBound C.omega).pushBound
      (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (.bvar (.there .here)) (.bvar .here) (fun v => nomatch v) (fun v => nomatch v)
    rfl rfl (fun v => nomatch v) (fun v => nomatch v) φ).mpr ((closed_l C φ hφ).mpr h)

/-- 任意原 Z₂ 模型的商均满足已有定理的纯集合算术闭包。 -/
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (φ : Sentence SecondOrderSyntax.signature_m)
    (hφ : SecondOrderArithmetic.language_m φ = true)
    (h : Derives SecondOrderArithmetic.theory_m [] φ) :
    (PowerlessBMSObjectProof.closure_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  exact closure_l C φ hφ (h.sound hℳ Env.empty (fun _ h => nomatch h))

/-- 原签名和原推导核上的传输：结论为纯集合闭句的既有图翻译。 -/
theorem derives_m (φ : Sentence SecondOrderSyntax.signature_m)
    (hφ : SecondOrderArithmetic.language_m φ = true)
    (h : Derives SecondOrderArithmetic.theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessBMSObjectProof.closure_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  exact fun _ hℳ => models_l hℳ φ hφ h

#print axioms coverage_l
#print axioms closed_l
#print axioms closure_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmeticTransfer
