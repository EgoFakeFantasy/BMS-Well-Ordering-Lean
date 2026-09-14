import BMSConstructibleBridge.PowerlessOrdinalBounded
import BMSConstructibleBridge.PowerlessBoundedCertificateSound
import BMSConstructibleBridge.PowerlessEvaluationPresentation
import BMSConstructibleBridge.PowerlessEvaluationOperator

/-!
# 不含当前域求值图参数的有界真值候选

以一个传递集合上的实际完整求值器为见证。公开公式仅含六个编码
参数、公式码和赋值图；正确性只对原有界分类给出，不宣称全真谓词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTruth

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationClause

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def certificate_l (ω e T t₁ t₂ t₃ c f A S F n : carrier_l ℳ) : Prop :=
  PowerlessNaturalOrder.transitive_l A ∧ member_l ℳ n ω ∧ map_l f n A ∧
    PowerlessEvaluationOperator.assignments_l ω A S ∧
    PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F ∧ query_l F c f

def certificate_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c f A S F n : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .conj (PowerlessOrdinalBounded.transitive_m A)
    (.conj (SecondOrderObjectSyntax.member_m n ω)
      (.conj (SecondOrderObjectSyntax.map_m f n A)
        (.conj (PowerlessEvaluationOperator.assignments_m ω A S)
          (.conj (PowerlessEvaluationPresentation.evaluation_m ω e T A t₁ t₂ t₃ S F)
            (query_m F c f)))))

theorem certificate_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c f A S F n : Term ℒ Γ Δ .set) :
    (certificate_m ω e T t₁ t₂ t₃ c f A S F n).satisfies η ↔
      certificate_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (c.eval η) (f.eval η) (A.eval η) (S.eval η) (F.eval η) (n.eval η) := by
  simp only [certificate_m, certificate_l, Formula.satisfies,
    PowerlessOrdinalBounded.transitive_formula_l, map_formula_l,
    PowerlessEvaluationOperator.assignments_formula_l, PowerlessEvaluationPresentation.evaluation_formula_l hℳ,
    query_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

def truth_l (ω e T t₁ t₂ t₃ c f : carrier_l ℳ) : Prop :=
  ∃ A S F n, certificate_l ω e T t₁ t₂ t₃ c f A S F n

def truth_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (((t.weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    certificate_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w c) (w f)
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem truth_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c f : Term ℒ Γ Δ .set) :
    (truth_m ω e T t₁ t₂ t₃ c f).satisfies η ↔
      truth_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (f.eval η) := by
  simp only [truth_m, truth_l, Formula.satisfies, certificate_formula_l hℳ, Term.eval_weakenBound]
  rfl

theorem sound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ U R H c f A S F n : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hR : PowerlessEvaluationOperator.assignments_l ω U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ R H)
    (hAU : subset_l A U) (hc : PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c)
    (h : certificate_l ω e T t₁ t₂ t₃ c f A S F n) : query_l H c f :=
  (PowerlessBoundedCertificateSound.recognizes_l hℳ hω ht hT hAU h.1 hR h.2.2.2.1
    hH h.2.2.2.2.1 hc f ⟨n, h.2.1, h.2.2.1⟩).mpr h.2.2.2.2.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTruth
