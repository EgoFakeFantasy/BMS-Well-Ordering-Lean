import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Propositional
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.FirstOrder

/-!
# checked 逻辑基础证书的总对象层回放

本模块把自然数检查器的全部 tag 0–11 精确分派到对象层基础证书。证明只读取
`fs_logical_base_axiom_check` 的计算结果；不会把 checked payload 降格为宽泛的
`HilbertBaseAxiom`。
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

/-- 基础逻辑检查通过时，其 tag 必在检查器实际实现的 `0` 到 `11` 之间。 -/
theorem fs_logical_base_axiom_check_tag_le
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_canonical_check formula certificate = true) :
    (godel_unpair_value certificate).1 ≤ 11 := by
  unfold fs_logical_base_axiom_canonical_check
    fs_logical_base_axiom_check_with at hCheck
  generalize hPair :
      godel_unpair_value certificate = pair at hCheck ⊢
  rcases pair with ⟨tag, payload⟩
  dsimp only at hCheck ⊢
  by_cases hBound : tag ≤ 11
  · exact hBound
  · have hTwelve : 12 ≤ tag := by
      omega
    obtain ⟨offset, hOffset⟩ :=
      Nat.exists_eq_add_of_le hTwelve
    have hTag : tag = offset + 12 := by
      omega
    rw [hTag] at hCheck
    simp at hCheck

/--
任意通过 `fs_logical_base_axiom_check` 的基础逻辑证书，都能在给定安全 binder
基址下回放为完整且保留 payload 的基础证书条件。
-/
theorem fs_zfc_support_raw_logical_base_certificate_with_base_of_check
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
      fs_logical_base_axiom_canonical_check formula certificate = true) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hTagUpper :=
    fs_logical_base_axiom_check_tag_le hCheck
  by_cases hPropositional :
      (godel_unpair_value certificate).1 ≤ 6
  · exact
      fs_zfc_support_raw_logical_propositional_certificate_with_base_of_check
        formulaCode certificateTerm base
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode
        hCheck hPropositional
  · exact
      fs_zfc_support_raw_logical_first_order_certificate_with_base_of_check
        formulaCode certificateTerm base hBaseLower
        hFormulaBoundary hCertificateBoundary
        hFormulaCode hCertificateCode
        hCheck (by omega) hTagUpper

/--
自动选择安全 binder 基址的基础逻辑证书回放。该封装只负责 fresh-base 计算；
所有实质分支均由显式基址内核完成。
-/
theorem fs_zfc_support_raw_logical_base_certificate_of_check
    {formula : SetFormula} {certificate : Nat}
    (formulaCode certificateTerm : SetTerm)
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
      fs_logical_base_axiom_canonical_check formula certificate = true) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition
        formulaCode certificateTerm) := by
  let base :=
    logical_certificate_fresh_base [formulaCode, certificateTerm]
  have hBaseLower : 700 ≤ base := by
    dsimp [base, logical_certificate_fresh_base]
    exact Nat.le_add_right 700 _
  unfold logical_base_certificate_condition
  simpa [base] using
    fs_zfc_support_raw_logical_base_certificate_with_base_of_check
      formulaCode certificateTerm base hBaseLower
      hFormulaBoundary hCertificateBoundary
      hFormulaCode hCertificateCode hCheck

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
