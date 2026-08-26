import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPropositionalBranchRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction

/-!
# 命题逻辑公理码的原始 token quotation

本模块把七个命题 Hilbert 公理码构造器直接对齐到其原始组件 token 串。
这里不把具名 decoder 的结果重新 quotation，因此不会引入 canonical re-quotation
假设；后续 checked mismatch 反演可以逐字复用证书 payload 中的 token。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

namespace CertifiedProof

/-! ## 外部 token 构造 -/

def fs_implication_distribution_axiom_tokens
    (antecedent middle consequent : List Nat) : List Nat :=
  Numbered.implication_tokens
    (Numbered.implication_tokens antecedent
      (Numbered.implication_tokens middle consequent))
    (Numbered.implication_tokens
      (Numbered.implication_tokens antecedent middle)
      (Numbered.implication_tokens antecedent consequent))

def fs_self_implication_axiom_tokens
    (body : List Nat) : List Nat :=
  Numbered.implication_tokens body
    (Numbered.implication_tokens body body)

def fs_weakening_axiom_tokens
    (body extra : List Nat) : List Nat :=
  Numbered.implication_tokens body
    (Numbered.implication_tokens extra body)

def fs_contradiction_axiom_tokens
    (body conclusion : List Nat) : List Nat :=
  Numbered.implication_tokens body
    (Numbered.implication_tokens
      (Numbered.negation_tokens body) conclusion)

def fs_classical_axiom_tokens
    (body : List Nat) : List Nat :=
  Numbered.implication_tokens
    (Numbered.implication_tokens
      (Numbered.negation_tokens body) body)
    body

def fs_explosion_axiom_tokens
    (body conclusion : List Nat) : List Nat :=
  Numbered.implication_tokens
    (Numbered.negation_tokens body)
    (Numbered.implication_tokens body conclusion)

def fs_case_analysis_axiom_tokens
    (body conclusion : List Nat) : List Nat :=
  Numbered.implication_tokens
    (Numbered.implication_tokens body conclusion)
    (Numbered.implication_tokens
      (Numbered.implication_tokens
        (Numbered.negation_tokens body) conclusion)
      conclusion)

/-! ## 对象层 quotation -/

/-- 自蕴含公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_self_implication_axiom_code_eq_standard
    (body : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      self_implication_axiom_code_term
          (standard_token_sequence body) ≐ₘ
        standard_token_sequence
          (fs_self_implication_axiom_tokens body)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hInner :=
    implication_formula_code_eq_standard_token_sequence
      body body
      (standard_token_sequence body)
      (standard_token_sequence body)
      hBody hBody
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      body (Numbered.implication_tokens body body)
      (standard_token_sequence body)
      (imp_codeₘ(
        standard_token_sequence body,
        standard_token_sequence body))
      hBody hInner
  simpa [self_implication_axiom_code_term,
    fs_self_implication_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 经典公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_classical_axiom_code_eq_standard
    (body : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      classical_axiom_code_term
          (standard_token_sequence body) ≐ₘ
        standard_token_sequence
          (fs_classical_axiom_tokens body)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hNeg :=
    negation_formula_code_eq_standard_token_sequence
      body (standard_token_sequence body) hBody
  have hInner :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.negation_tokens body) body
      (neg_codeₘ(standard_token_sequence body))
      (standard_token_sequence body)
      hNeg hBody
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.implication_tokens
        (Numbered.negation_tokens body) body)
      body
      (imp_codeₘ(
        neg_codeₘ(standard_token_sequence body),
        standard_token_sequence body))
      (standard_token_sequence body)
      hInner hBody
  simpa [classical_axiom_code_term,
    fs_classical_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 弱化公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_weakening_axiom_code_eq_standard
    (body extra : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      weakening_axiom_code_term
          (standard_token_sequence body)
          (standard_token_sequence extra) ≐ₘ
        standard_token_sequence
          (fs_weakening_axiom_tokens body extra)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hExtra :
      Derives godel_quotation_theory [] (
        standard_token_sequence extra ≐ₘ
          standard_token_sequence extra) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence extra)
  have hInner :=
    implication_formula_code_eq_standard_token_sequence
      extra body
      (standard_token_sequence extra)
      (standard_token_sequence body)
      hExtra hBody
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      body (Numbered.implication_tokens extra body)
      (standard_token_sequence body)
      (imp_codeₘ(
        standard_token_sequence extra,
        standard_token_sequence body))
      hBody hInner
  simpa [weakening_axiom_code_term,
    fs_weakening_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 矛盾前件公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_contradiction_axiom_code_eq_standard
    (body conclusion : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      contradiction_axiom_code_term
          (standard_token_sequence body)
          (standard_token_sequence conclusion) ≐ₘ
        standard_token_sequence
          (fs_contradiction_axiom_tokens body conclusion)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hConclusion :
      Derives godel_quotation_theory [] (
        standard_token_sequence conclusion ≐ₘ
          standard_token_sequence conclusion) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence conclusion)
  have hNeg :=
    negation_formula_code_eq_standard_token_sequence
      body (standard_token_sequence body) hBody
  have hInner :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.negation_tokens body) conclusion
      (neg_codeₘ(standard_token_sequence body))
      (standard_token_sequence conclusion)
      hNeg hConclusion
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      body
      (Numbered.implication_tokens
        (Numbered.negation_tokens body) conclusion)
      (standard_token_sequence body)
      (imp_codeₘ(
        neg_codeₘ(standard_token_sequence body),
        standard_token_sequence conclusion))
      hBody hInner
  simpa [contradiction_axiom_code_term,
    fs_contradiction_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 爆炸律公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_explosion_axiom_code_eq_standard
    (body conclusion : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      explosion_axiom_code_term
          (standard_token_sequence body)
          (standard_token_sequence conclusion) ≐ₘ
        standard_token_sequence
          (fs_explosion_axiom_tokens body conclusion)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hConclusion :
      Derives godel_quotation_theory [] (
        standard_token_sequence conclusion ≐ₘ
          standard_token_sequence conclusion) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence conclusion)
  have hNeg :=
    negation_formula_code_eq_standard_token_sequence
      body (standard_token_sequence body) hBody
  have hInner :=
    implication_formula_code_eq_standard_token_sequence
      body conclusion
      (standard_token_sequence body)
      (standard_token_sequence conclusion)
      hBody hConclusion
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.negation_tokens body)
      (Numbered.implication_tokens body conclusion)
      (neg_codeₘ(standard_token_sequence body))
      (imp_codeₘ(
        standard_token_sequence body,
        standard_token_sequence conclusion))
      hNeg hInner
  simpa [explosion_axiom_code_term,
    fs_explosion_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 分类讨论公理码保持 payload 中的原始 token。 -/
theorem fs_zfc_support_raw_case_analysis_axiom_code_eq_standard
    (body conclusion : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      case_analysis_axiom_code_term
          (standard_token_sequence body)
          (standard_token_sequence conclusion) ≐ₘ
        standard_token_sequence
          (fs_case_analysis_axiom_tokens body conclusion)) := by
  have hBody :
      Derives godel_quotation_theory [] (
        standard_token_sequence body ≐ₘ
          standard_token_sequence body) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence body)
  have hConclusion :
      Derives godel_quotation_theory [] (
        standard_token_sequence conclusion ≐ₘ
          standard_token_sequence conclusion) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence conclusion)
  have hNeg :=
    negation_formula_code_eq_standard_token_sequence
      body (standard_token_sequence body) hBody
  have hLeft :=
    implication_formula_code_eq_standard_token_sequence
      body conclusion
      (standard_token_sequence body)
      (standard_token_sequence conclusion)
      hBody hConclusion
  have hNegLeft :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.negation_tokens body) conclusion
      (neg_codeₘ(standard_token_sequence body))
      (standard_token_sequence conclusion)
      hNeg hConclusion
  have hRight :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.implication_tokens
        (Numbered.negation_tokens body) conclusion)
      conclusion
      (imp_codeₘ(
        neg_codeₘ(standard_token_sequence body),
        standard_token_sequence conclusion))
      (standard_token_sequence conclusion)
      hNegLeft hConclusion
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.implication_tokens body conclusion)
      (Numbered.implication_tokens
        (Numbered.implication_tokens
          (Numbered.negation_tokens body) conclusion)
        conclusion)
      (imp_codeₘ(
        standard_token_sequence body,
        standard_token_sequence conclusion))
      (imp_codeₘ(
        imp_codeₘ(
          neg_codeₘ(standard_token_sequence body),
          standard_token_sequence conclusion),
        standard_token_sequence conclusion))
      hLeft hRight
  simpa [case_analysis_axiom_code_term,
    fs_case_analysis_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

/-- 蕴含分配公理码保持 payload 中的三个原始 token 串。 -/
theorem
    fs_zfc_support_raw_implication_distribution_axiom_code_eq_standard
    (antecedent middle consequent : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      implication_distribution_axiom_code_term
          (standard_token_sequence antecedent)
          (standard_token_sequence middle)
          (standard_token_sequence consequent) ≐ₘ
        standard_token_sequence
          (fs_implication_distribution_axiom_tokens
            antecedent middle consequent)) := by
  have hAntecedent :
      Derives godel_quotation_theory [] (
        standard_token_sequence antecedent ≐ₘ
          standard_token_sequence antecedent) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence antecedent)
  have hMiddle :
      Derives godel_quotation_theory [] (
        standard_token_sequence middle ≐ₘ
          standard_token_sequence middle) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence middle)
  have hConsequent :
      Derives godel_quotation_theory [] (
        standard_token_sequence consequent ≐ₘ
          standard_token_sequence consequent) :=
    FirstOrder.Derives.eq_refl_m
      (standard_token_sequence consequent)
  have hMiddleConsequent :=
    implication_formula_code_eq_standard_token_sequence
      middle consequent
      (standard_token_sequence middle)
      (standard_token_sequence consequent)
      hMiddle hConsequent
  have hLeft :=
    implication_formula_code_eq_standard_token_sequence
      antecedent
      (Numbered.implication_tokens middle consequent)
      (standard_token_sequence antecedent)
      (imp_codeₘ(
        standard_token_sequence middle,
        standard_token_sequence consequent))
      hAntecedent hMiddleConsequent
  have hAntecedentMiddle :=
    implication_formula_code_eq_standard_token_sequence
      antecedent middle
      (standard_token_sequence antecedent)
      (standard_token_sequence middle)
      hAntecedent hMiddle
  have hAntecedentConsequent :=
    implication_formula_code_eq_standard_token_sequence
      antecedent consequent
      (standard_token_sequence antecedent)
      (standard_token_sequence consequent)
      hAntecedent hConsequent
  have hRight :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.implication_tokens antecedent middle)
      (Numbered.implication_tokens antecedent consequent)
      (imp_codeₘ(
        standard_token_sequence antecedent,
        standard_token_sequence middle))
      (imp_codeₘ(
        standard_token_sequence antecedent,
        standard_token_sequence consequent))
      hAntecedentMiddle hAntecedentConsequent
  have hOuter :=
    implication_formula_code_eq_standard_token_sequence
      (Numbered.implication_tokens antecedent
        (Numbered.implication_tokens middle consequent))
      (Numbered.implication_tokens
        (Numbered.implication_tokens antecedent middle)
        (Numbered.implication_tokens antecedent consequent))
      (imp_codeₘ(
        standard_token_sequence antecedent,
        imp_codeₘ(
          standard_token_sequence middle,
          standard_token_sequence consequent)))
      (imp_codeₘ(
        imp_codeₘ(
          standard_token_sequence antecedent,
          standard_token_sequence middle),
        imp_codeₘ(
          standard_token_sequence antecedent,
          standard_token_sequence consequent)))
      hLeft hRight
  simpa [implication_distribution_axiom_code_term,
    fs_implication_distribution_axiom_tokens] using
      fs_zfc_support_raw_derives_of_godel_quotation hOuter

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
