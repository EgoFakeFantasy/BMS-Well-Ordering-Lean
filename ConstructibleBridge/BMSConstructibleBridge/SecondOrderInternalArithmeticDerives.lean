import BMSConstructibleBridge.SecondOrderLanguageClosure
import BMSConstructibleBridge.PowerlessBMSQuotientArithmeticTransfer
import BMSConstructibleBridge.SecondOrderInternalFormulaSyntax

/-!
# 内部合法性与求值固定点的纯集合闭对象推导

原二阶定理先经完整语言检查，再进入既有纯集合算术闭包；所有集合量词及
参数都保留。此处只交付两项递归证书，不以它们代替精确 Def 的对象公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalArithmeticDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

theorem fixed_pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (SecondOrderRankedRecursionTheorem.fixed_m φ) = true := by
  have h₀ := SecondOrderSetOperator.pure_m φ (Γ := [.set])
    (.bvar .here) (.bvar .here) (fun v => .fvar v) hφ rfl rfl (fun _ => rfl)
  have h₁ := SecondOrderSetOperator.pure_m φ (Γ := [.set, .set])
    (.bvar .here) (.bvar .here) (fun v => .fvar v) hφ rfl rfl (fun _ => rfl)
  change (language_m (SecondOrderSetOperator.formula_m φ (Γ := [.set])
    (.bvar .here) (.bvar .here) (fun v => .fvar v)) &&
    (language_m (SecondOrderSetOperator.formula_m φ (Γ := [.set, .set])
      (.bvar .here) (.bvar .here) (fun v => .fvar v)) && true)) = true
  rw [h₀, h₁]
  rfl

def syntax_sentence_m : Sentence ℒ :=
  PowerlessBMSObjectProof.closure_m SecondOrderInternalFormulaSyntax.sentence_m

def evaluation_sentence_m : Sentence ℒ :=
  PowerlessBMSObjectProof.closure_m SecondOrderEvaluationFixedPoint.sentence_m

theorem syntax_pure_m : language_m SecondOrderInternalFormulaSyntax.sentence_m = true := by
  exact (SecondOrderLanguageClosure.forall_close_m _).trans
    (fixed_pure_m _ (SecondOrderRecursiveRelation.pure_m _ SecondOrderInternalFormulaSyntax.pure_m))

theorem evaluation_pure_m : language_m SecondOrderEvaluationFixedPoint.sentence_m = true := by
  exact (SecondOrderLanguageClosure.forall_close_m _).trans
    (fixed_pure_m _ (SecondOrderRecursiveRelation.pure_m _ SecondOrderEvaluationRule.pure_m))

theorem syntax_derives_m : Derives theory_m [] (GraphTranslation.form_m syntax_sentence_m) :=
  PowerlessBMSQuotientArithmeticTransfer.derives_m _ syntax_pure_m SecondOrderInternalFormulaSyntax.derives_m

theorem evaluation_derives_m : Derives theory_m [] (GraphTranslation.form_m evaluation_sentence_m) :=
  PowerlessBMSQuotientArithmeticTransfer.derives_m _ evaluation_pure_m SecondOrderEvaluationFixedPoint.derives_m

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem syntax_models_l (hℳ : Theory.Models ℳ theory_m) :
    syntax_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) :=
  PowerlessBMSQuotientArithmeticTransfer.models_l hℳ _ syntax_pure_m SecondOrderInternalFormulaSyntax.derives_m

theorem evaluation_models_l (hℳ : Theory.Models ℳ theory_m) :
    evaluation_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) :=
  PowerlessBMSQuotientArithmeticTransfer.models_l hℳ _ evaluation_pure_m SecondOrderEvaluationFixedPoint.derives_m

#print axioms syntax_derives_m
#print axioms evaluation_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalArithmeticDerives
