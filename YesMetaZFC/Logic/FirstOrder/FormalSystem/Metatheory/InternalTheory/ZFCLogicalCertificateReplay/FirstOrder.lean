import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder.Specialization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder.ForallDistribution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder.VacuousForall
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder.EqualitySubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder.Reflexivity

/-!
# checked 逻辑证书的一阶基础分派

本模块只汇总 tag 7–11 的精确对象层回放。各分支仍由独立模块维护；这里不重新
反演 payload，也不经过会遗失证书数据的 `HilbertBaseAxiom`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/--
tag 7–11 的 checked 基础逻辑证书在 ZFC 对象元理论中满足完整基础证书条件。
-/
theorem fs_zfc_support_raw_logical_first_order_certificate_with_base_of_check
    {formula : SetFormula} {certificate : Nat}
    (formulaCode certificateTerm : SetTerm)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ fs_zfc_formula_code_term formula))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate)))
    (hCheck :
      fs_logical_base_axiom_canonical_check formula certificate = true)
    (hTagLower :
      7 ≤ (godel_unpair_value certificate).1)
    (hTagUpper :
      (godel_unpair_value certificate).1 ≤ 11) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hCases :
      (godel_unpair_value certificate).1 = 7 ∨
      (godel_unpair_value certificate).1 = 8 ∨
      (godel_unpair_value certificate).1 = 9 ∨
      (godel_unpair_value certificate).1 = 10 ∨
      (godel_unpair_value certificate).1 = 11 := by
    omega
  rcases hCases with h7 | h8 | h9 | h10 | h11
  · exact
      fs_zfc_support_raw_logical_specialization_certificate_with_base_of_check
        formulaCode certificateTerm base hBaseLower
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode hCheck h7
  · exact
      fs_zfc_support_raw_logical_forall_distribution_certificate_with_base_of_check
        formulaCode certificateTerm base hBaseLower
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode hCheck h8
  · exact
      fs_zfc_support_raw_logical_vacuous_forall_certificate_with_base_of_check
        formulaCode certificateTerm base hBaseLower
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode hCheck h9
  · exact
      fs_zfc_support_raw_logical_equality_substitution_certificate_with_base_of_check
        formulaCode certificateTerm base hBaseLower
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode hCheck h10
  · exact
      fs_zfc_support_raw_logical_reflexivity_certificate_with_base_of_check
        formulaCode certificateTerm base
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode hCheck h11

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
