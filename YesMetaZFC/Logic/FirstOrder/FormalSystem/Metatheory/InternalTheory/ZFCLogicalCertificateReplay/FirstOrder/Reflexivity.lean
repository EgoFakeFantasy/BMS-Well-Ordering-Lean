import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFirstOrderInversion

/-!
# checked 逻辑证书的等式自反分支

本模块回放 tag 11。该分支只携带一个自然数编号、一个有限序列成员事实和
规范等式公式码；没有调用逻辑公理成员关系或旧的 Hilbert 反向实例。
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

theorem fs_zfc_support_raw_logical_reflexivity_certificate_of_decode
    (formulaCode certificateTerm : SetTerm)
    (certificate : Nat)
    (identifier : Nat)
    (identifierId : FreeVarId)
    (hCertificate :
      certificate = godel_pair_value 11 identifier)
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ numₘ(identifier)),
            var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))))
    (hFormulaCodeClosed :
      Term.freeSupport formulaCode = [])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate)))
    (hCertificateTermClosed :
      Term.freeSupport certificateTerm = []) :
    Derives fs_zfc_support_raw_theory [] (
      logical_equality_reflexivity_certificate_condition_with_id
        formulaCode certificateTerm identifierId) := by
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(11), numₘ(identifier)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hIdentifierField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(identifier) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega identifier)
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ numₘ(identifier)),
            var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))) := by
    exact hFormulaCode
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ),
      x#identifierId ∈ₘ ωₘ,
      formulaCode ≐ₘ
        eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ x#identifierId),
          var_codeₘ(numₘ(2) *ₘ x#identifierId))]
  let actualBody : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(11), numₘ(identifier)⟩ₘ),
      numₘ(identifier) ∈ₘ ωₘ,
      formulaCode ≐ₘ
        eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ numₘ(identifier)),
          var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))]
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl
    · exact hCertificateField
    · exact hIdentifierField
    · exact hFormulaField
  have hNumeralSubstitute
      (value : Nat) :
      Term.substituteFree SetSort.set identifierId
          (numₘ(identifier)) (numₘ(value)) =
        numₘ(value) :=
    fs_zfc_support_raw_closed_term_substitute
      (finite_numeral_term_freeSupport value) identifierId
      (numₘ(identifier))
  have hFormulaCodeSubstitute :
      Term.substituteFree SetSort.set identifierId
          (numₘ(identifier)) formulaCode =
        formulaCode :=
    fs_zfc_support_raw_closed_term_substitute
      hFormulaCodeClosed identifierId (numₘ(identifier))
  have hCertificateTermSubstitute :
      Term.substituteFree SetSort.set identifierId
          (numₘ(identifier)) certificateTerm =
        certificateTerm :=
    fs_zfc_support_raw_closed_term_substitute
      hCertificateTermClosed identifierId (numₘ(identifier))
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set identifierId
          (numₘ(identifier)) body) := by
    simpa [body, actualBody, logical_certificate_conjunction,
      Formula.substituteFree,
      Term.substituteFree, set_variable,
      finite_numeral_term, hFormulaCodeSubstitute,
      hCertificateTermSubstitute,
      hNumeralSubstitute] using hActualBody
  have hWitnessCheck :
      Term.CheckCertificate (numₘ(identifier)) SetSort.set :=
    Term.check_certificate_of_admissible
      (finite_numeral_term_admissible identifier)
  have hNested :=
    FirstOrder.Derives.exists_intro_substituted
      (T := fs_zfc_support_raw_theory) (Γ := [])
      identifierId hInstance hWitnessCheck
  simpa [logical_equality_reflexivity_certificate_condition_with_id,
    body, Formula.existsFreeAssignments] using hNested

theorem fs_zfc_support_raw_logical_reflexivity_certificate_with_base_of_check
    {formula : SetFormula} {certificate : Nat}
    (formulaCode certificateTerm : SetTerm)
    (base : FreeVarId)
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
    (hTag :
      (godel_unpair_value certificate).1 = 11) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_first_order_witness
      hCheck (by omega) (by omega)
  rw [hTag] at hWitness
  cases hWitness with
  | equality_reflexivity hFormula =>
      let identifier := (godel_unpair_value certificate).2
      have hCertificate :
          certificate = godel_pair_value 11 identifier := by
        have hCode := (godel_unpair_value_spec certificate).symm
        simpa [identifier, hTag] using hCode
      have hFormulaCodeRaw :
          fs_zfc_formula_code_term formula =
            eq_codeₘ(
              var_codeₘ(numₘ(2 * identifier)),
              var_codeₘ(numₘ(2 * identifier))) := by
        dsimp [identifier]
        rw [hFormula]
        exact
          fs_zfc_formula_code_term_fvar_equality_reflexivity
            (godel_unpair_value certificate).2
      have hMultiplication :
          Derives fs_zfc_support_raw_theory [] (
            numₘ(2 * identifier) ≐ₘ
              (numₘ(2) *ₘ numₘ(identifier))) :=
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_finite_numeral_multiplication
            2 identifier)
      have hLeftProduct :
          Term.Admissible
            (numₘ(2) *ₘ numₘ(identifier)) SetSort.set :=
        natural_multiplication_term_admissible
          (numₘ(2)) (numₘ(identifier))
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible identifier)
      have hLeftVariable :
          Term.Admissible
            (var_codeₘ(numₘ(2 * identifier))) SetSort.set :=
        variable_code_term_admissible
          (numₘ(2 * identifier))
          (finite_numeral_term_admissible (2 * identifier))
      have hRightVariable :
          Term.Admissible
            (var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))
            SetSort.set :=
        variable_code_term_admissible
          (numₘ(2) *ₘ numₘ(identifier))
          hLeftProduct
      have hVariableEquality :
          Derives fs_zfc_support_raw_theory [] (
            var_codeₘ(numₘ(2 * identifier)) ≐ₘ
              var_codeₘ(numₘ(2) *ₘ numₘ(identifier))) := by
        exact Metatheory.Derives.unary_term_constructor_congr_of_equality
          (fun term => var_codeₘ(term))
          (fun term hTerm =>
            variable_code_term_admissible term hTerm)
          (by intros; simp [Term.substituteFree])
          (numₘ(2 * identifier))
          (numₘ(2) *ₘ numₘ(identifier))
          (finite_numeral_term_admissible (2 * identifier))
          hLeftProduct hMultiplication
      have hEqualityCode :
          Derives fs_zfc_support_raw_theory [] (
            eq_codeₘ(
              var_codeₘ(numₘ(2 * identifier)),
              var_codeₘ(numₘ(2 * identifier))) ≐ₘ
                eq_codeₘ(
                  var_codeₘ(numₘ(2) *ₘ numₘ(identifier)),
                  var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))) :=
        fs_zfc_support_raw_equality_code_term_congr_of_equalities
          (var_codeₘ(numₘ(2 * identifier)))
          (var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))
          (var_codeₘ(numₘ(2 * identifier)))
          (var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))
          hLeftVariable hRightVariable hLeftVariable hRightVariable
          hVariableEquality hVariableEquality
      have hFormulaCodeBase :
          Derives fs_zfc_support_raw_theory [] (
            formulaCode ≐ₘ
              eq_codeₘ(
                var_codeₘ(numₘ(2 * identifier)),
                var_codeₘ(numₘ(2 * identifier)))) := by
        apply Metatheory.Derives.equality_trans hFormulaCode
        rw [← hFormulaCodeRaw]
        exact FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (fs_zfc_formula_code_term formula)
          (hTermCheck := Term.check_certificate_of_admissible
            (fs_zfc_formula_code_term_code_boundary formula).1)
      have hFormulaTarget :
          Derives fs_zfc_support_raw_theory [] (
            formulaCode ≐ₘ
              eq_codeₘ(
                var_codeₘ(numₘ(2) *ₘ numₘ(identifier)),
                var_codeₘ(numₘ(2) *ₘ numₘ(identifier)))) :=
        Metatheory.Derives.equality_trans
          hFormulaCodeBase hEqualityCode
      have hFormulaCodeClosed :
          Term.freeSupport formulaCode = [] :=
        hFormulaBoundary.2
      have hBranch :=
        fs_zfc_support_raw_logical_reflexivity_certificate_of_decode
          formulaCode certificateTerm certificate identifier (base + 62)
          hCertificate hFormulaTarget hFormulaCodeClosed
          hCertificateCode hCertificateBoundary.2
      have hCondition :
          Formula.Admissible
            (logical_base_certificate_condition_with_base
              formulaCode certificateTerm base) :=
        logical_base_certificate_condition_with_base_admissible
          formulaCode certificateTerm base
          hFormulaBoundary.1
          hCertificateBoundary.1
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      have hTail₆ := Formula.Admissible.disj_right hTail₅
      have hTail₇ := Formula.Admissible.disj_right hTail₆
      have hTail₈ := Formula.Admissible.disj_right hTail₇
      have hTail₉ := Formula.Admissible.disj_right hTail₈
      have hTail₁₀ := Formula.Admissible.disj_right hTail₉
      have hTail₁₁ := Formula.Admissible.disj_right hTail₁₀
      have hHead₀ := Formula.Admissible.disj_left hCondition
      have hHead₁ := Formula.Admissible.disj_left hTail₁
      have hHead₂ := Formula.Admissible.disj_left hTail₂
      have hHead₃ := Formula.Admissible.disj_left hTail₃
      have hHead₄ := Formula.Admissible.disj_left hTail₄
      have hHead₅ := Formula.Admissible.disj_left hTail₅
      have hHead₆ := Formula.Admissible.disj_left hTail₆
      have hHead₇ := Formula.Admissible.disj_left hTail₇
      have hHead₈ := Formula.Admissible.disj_left hTail₈
      have hHead₉ := Formula.Admissible.disj_left hTail₉
      have hHead₁₀ := Formula.Admissible.disj_left hTail₁₀
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₂)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₃)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₄)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₅)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₆)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₇)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₈)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₉)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁₀)
      simpa using hBranch

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
