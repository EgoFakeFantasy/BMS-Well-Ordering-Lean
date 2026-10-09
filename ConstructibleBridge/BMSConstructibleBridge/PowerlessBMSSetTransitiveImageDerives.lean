import BMSConstructibleBridge.PowerlessBMSSetTransitiveImage
import BMSConstructibleBridge.PowerlessBMSTransitiveImageDerives

/-!
# 任意集合定义域上的传递类像：对象模式

每个纯源公式实例的原图翻译均由原 Z₂ 推出。模式只要求原集合定义域上的
单值性及输出类传递；并未要求总性，也未在前提中假定值域已经是集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSSetTransitiveImageDerives

open Logic FirstOrder PowerlessBMSQuotientSubsetImageDerives

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (
    let D : Term ℒ [.set] Δ .set := .bvar .here
    .imp (.conj (unique_m φ D) (PowerlessBMSTransitiveImageDerives.transitive_m φ D))
      (.existsE .set (image_m φ (D.weakenBound SetTheory.SetSort.set) (.bvar .here))))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ D : SecondOrderQuotient.type_l hℳ,
      (∀ x y z, SecondOrderQuotient.mem_l hℳ x D →
        φ.satisfies ((η.pushFree x).pushFree y) →
        φ.satisfies ((η.pushFree x).pushFree z) → y = z) →
      (∀ y z, (∃ x, SecondOrderQuotient.mem_l hℳ x D ∧
        φ.satisfies ((η.pushFree x).pushFree y)) → SecondOrderQuotient.mem_l hℳ z y →
        ∃ x, SecondOrderQuotient.mem_l hℳ x D ∧ φ.satisfies ((η.pushFree x).pushFree z)) →
      ∃ B, ∀ y, SecondOrderQuotient.mem_l hℳ y B ↔
        ∃ x, SecondOrderQuotient.mem_l hℳ x D ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [schema_m, unique_m, PowerlessBMSTransitiveImageDerives.transitive_m,
    image_m, Formula.satisfies, at_formula_l, PowerlessBMSQuotientBoundedImage.range_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    parameters_pushBound_l, parameters_empty_l, and_imp]
  rfl

theorem models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) : (schema_m φ).satisfies η := by
  apply (schema_formula_l hℳ φ η).mpr
  intro D hUnique hTrans
  exact PowerlessBMSSetTransitiveImage.exists_l hℳ φ η D hUnique
    (fun x y hx hy z hz => hTrans y z ⟨x, hx, hy⟩ hz)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr (models_l hℳ φ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSSetTransitiveImageDerives
