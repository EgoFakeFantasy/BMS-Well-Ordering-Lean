import BMSConstructibleBridge.PowerlessBMSQuotientBoundedImage

/-!
# 任意定义域的子集有界替换：原 Z₂ 对象推导

目标为纯集合语言闭模式经原图翻译所得的句子。实际证明还允许部分函数：
只需单值性和共同子集界，不要求定义域中每个输入有输出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientBoundedImageDerives

open Logic FirstOrder PowerlessBMSQuotientSubsetImageDerives

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 任意内部定义域与母集，全部原参数保留为自由槽。 -/
def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (.forallE .set (
    let D : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
    let A : Term ℒ [.set, .set] Δ .set := .bvar .here
    .imp (.conj (unique_m φ D) (bounded_m φ D A))
      (.existsE .set (image_m φ (D.weakenBound SetTheory.SetSort.set) (.bvar .here)))))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ D A : SecondOrderQuotient.type_l hℳ,
      (∀ x y z, SecondOrderQuotient.mem_l hℳ x D →
        φ.satisfies ((η.pushFree x).pushFree y) →
        φ.satisfies ((η.pushFree x).pushFree z) → y = z) →
      (∀ x y, SecondOrderQuotient.mem_l hℳ x D →
        φ.satisfies ((η.pushFree x).pushFree y) →
        ∀ t, SecondOrderQuotient.mem_l hℳ t y → SecondOrderQuotient.mem_l hℳ t A) →
      ∃ B, ∀ y, SecondOrderQuotient.mem_l hℳ y B ↔
        ∃ x, SecondOrderQuotient.mem_l hℳ x D ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [schema_m, unique_m, bounded_m, image_m, Formula.satisfies,
    ThirdOrderSemantics.subset_formula_l, at_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval,
    parameters_pushBound_l, parameters_empty_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l, and_imp]
  rfl

theorem models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) : (schema_m φ).satisfies η := by
  apply (schema_formula_l hℳ φ η).mpr
  intro D A hUnique hBound
  exact PowerlessBMSQuotientBoundedImage.exists_l hℳ φ η D A hUnique hBound

/-- 不增加 Collection 的实际对象模式推导，参数闭包没有遗漏。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr (models_l hℳ φ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientBoundedImageDerives
