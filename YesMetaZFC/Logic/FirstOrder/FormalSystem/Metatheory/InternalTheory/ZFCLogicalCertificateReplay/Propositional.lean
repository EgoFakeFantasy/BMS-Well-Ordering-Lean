import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Propositional.Ternary
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Propositional.Unary
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Propositional.Binary
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalPropositionalInversion

/-!
# checked 逻辑证书的命题基础分支

本模块汇总七个命题基础公理的精确 checked payload 回放。各元数的证书构造与
检查器反演分模块维护，避免单个编译单元膨胀。
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
tag 0–6 的 checked 基础逻辑证书在 ZFC 对象元理论中满足完整精确证书条件。

假设只限制计算结果的 tag 范围；payload 形状、字段 decoder 与最终公式结构均由
`FSLogicalPropositionalCheckWitness` 从原检查等式中恢复。
-/
theorem fs_zfc_support_raw_logical_propositional_certificate_with_base_of_check
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
    (hTagBound :
      (godel_unpair_value certificate).1 ≤ 6) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_propositional_witness
      hCheck hTagBound
  have hCertificate :
      certificate =
        godel_pair_value
          (godel_unpair_value certificate).1
          (godel_unpair_value certificate).2 :=
    (godel_unpair_value_spec certificate).symm
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
  have hHead₀ := Formula.Admissible.disj_left hCondition
  have hHead₁ := Formula.Admissible.disj_left hTail₁
  have hHead₂ := Formula.Admissible.disj_left hTail₂
  have hHead₃ := Formula.Admissible.disj_left hTail₃
  have hHead₄ := Formula.Admissible.disj_left hTail₄
  have hHead₅ := Formula.Admissible.disj_left hTail₅
  have hHead₆ := Formula.Admissible.disj_left hTail₆
  have hTraceIndex :
      base + 40 ≠ base + 41 :=
    Nat.ne_of_lt
      (Nat.add_lt_add_left (by decide : 40 < 41) base)
  generalize hTag :
      (godel_unpair_value certificate).1 = tag at hWitness
  cases hWitness with
  | implication_distribution antecedent middle consequent
      hPayload hFormula =>
      rcases fs_formula_payload_decode_three hPayload with
        ⟨antecedentCode, middleCode, consequentCode,
          hCodes, hAntecedentCode, hMiddleCode, hConsequentCode⟩
      have hAntecedent :=
        fs_formula_token_code_decode_admissible hAntecedentCode
      have hMiddle :=
        fs_formula_token_code_decode_admissible hMiddleCode
      have hConsequent :=
        fs_formula_token_code_decode_admissible hConsequentCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            implication_distribution_axiom_code_term
              (fs_zfc_formula_code_term antecedent)
              (fs_zfc_formula_code_term middle)
              (fs_zfc_formula_code_term consequent) := by
        rw [hFormula]
        exact
          fs_zfc_formula_code_term_implication_distribution
            antecedent middle consequent
            hAntecedent hMiddle hConsequent
      have hBranch :=
        fs_zfc_support_raw_logical_ternary_base_certificate_of_decode
          0 (godel_unpair_value certificate).2 certificate
          implication_distribution_axiom_code_term
          formulaCode certificateTerm
          antecedentCode middleCode consequentCode
          antecedent middle consequent
          base (base + 1) (base + 2) (base + 3) (base + 4)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement firstTerm secondTerm thirdTerm
            simp [implication_distribution_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hAntecedentCode hMiddleCode hConsequentCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₁)
      simpa using hBranch
  | self_implication body hPayload hFormula =>
      rcases fs_formula_payload_decode_one hPayload with
        ⟨bodyCode, hCodes, hBodyCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            self_implication_axiom_code_term
              (fs_zfc_formula_code_term body) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_self_implication body hBody
      have hBranch :=
        fs_zfc_support_raw_logical_unary_base_certificate_of_decode
          1 (godel_unpair_value certificate).2 certificate
          self_implication_axiom_code_term formulaCode certificateTerm
          bodyCode body
          (base + 5) (base + 6) (base + 7)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement componentTerm
            simp [self_implication_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₂)
      simpa using hBranch
  | weakening body extra hPayload hFormula =>
      rcases fs_formula_payload_decode_two hPayload with
        ⟨bodyCode, extraCode, hCodes, hBodyCode, hExtraCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hExtra :=
        fs_formula_token_code_decode_admissible hExtraCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            weakening_axiom_code_term
              (fs_zfc_formula_code_term body)
              (fs_zfc_formula_code_term extra) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_weakening
          body extra hBody hExtra
      have hBranch :=
        fs_zfc_support_raw_logical_binary_base_certificate_of_decode
          2 (godel_unpair_value certificate).2 certificate
          weakening_axiom_code_term formulaCode certificateTerm
          bodyCode extraCode body extra
          (base + 8) (base + 9) (base + 10) (base + 11)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement leftTerm rightTerm
            simp [weakening_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode hExtraCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁)
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₃)
      simpa using hBranch
  | contradiction body conclusion hPayload hFormula =>
      rcases fs_formula_payload_decode_two hPayload with
        ⟨bodyCode, conclusionCode, hCodes,
          hBodyCode, hConclusionCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hConclusion :=
        fs_formula_token_code_decode_admissible hConclusionCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            contradiction_axiom_code_term
              (fs_zfc_formula_code_term body)
              (fs_zfc_formula_code_term conclusion) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_contradiction
          body conclusion hBody hConclusion
      have hBranch :=
        fs_zfc_support_raw_logical_binary_base_certificate_of_decode
          3 (godel_unpair_value certificate).2 certificate
          contradiction_axiom_code_term formulaCode certificateTerm
          bodyCode conclusionCode body conclusion
          (base + 12) (base + 13) (base + 14) (base + 15)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement leftTerm rightTerm
            simp [contradiction_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode hConclusionCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₂)
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₄)
      simpa using hBranch
  | classical body hPayload hFormula =>
      rcases fs_formula_payload_decode_one hPayload with
        ⟨bodyCode, hCodes, hBodyCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            classical_axiom_code_term
              (fs_zfc_formula_code_term body) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_classical body hBody
      have hBranch :=
        fs_zfc_support_raw_logical_unary_base_certificate_of_decode
          4 (godel_unpair_value certificate).2 certificate
          classical_axiom_code_term formulaCode certificateTerm
          bodyCode body
          (base + 16) (base + 17) (base + 18)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement componentTerm
            simp [classical_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
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
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₅)
      simpa using hBranch
  | explosion body conclusion hPayload hFormula =>
      rcases fs_formula_payload_decode_two hPayload with
        ⟨bodyCode, conclusionCode, hCodes,
          hBodyCode, hConclusionCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hConclusion :=
        fs_formula_token_code_decode_admissible hConclusionCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            explosion_axiom_code_term
              (fs_zfc_formula_code_term body)
              (fs_zfc_formula_code_term conclusion) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_explosion
          body conclusion hBody hConclusion
      have hBranch :=
        fs_zfc_support_raw_logical_binary_base_certificate_of_decode
          5 (godel_unpair_value certificate).2 certificate
          explosion_axiom_code_term formulaCode certificateTerm
          bodyCode conclusionCode body conclusion
          (base + 19) (base + 20) (base + 21) (base + 22)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement leftTerm rightTerm
            simp [explosion_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode hConclusionCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
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
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₆)
      simpa using hBranch
  | case_analysis body conclusion hPayload hFormula =>
      rcases fs_formula_payload_decode_two hPayload with
        ⟨bodyCode, conclusionCode, hCodes,
          hBodyCode, hConclusionCode⟩
      have hBody :=
        fs_formula_token_code_decode_admissible hBodyCode
      have hConclusion :=
        fs_formula_token_code_decode_admissible hConclusionCode
      have hFormulaTerm :
          fs_zfc_formula_code_term formula =
            case_analysis_axiom_code_term
              (fs_zfc_formula_code_term body)
              (fs_zfc_formula_code_term conclusion) := by
        rw [hFormula]
        exact fs_zfc_formula_code_term_case_analysis
          body conclusion hBody hConclusion
      have hBranch :=
        fs_zfc_support_raw_logical_binary_base_certificate_of_decode
          6 (godel_unpair_value certificate).2 certificate
          case_analysis_axiom_code_term formulaCode certificateTerm
          bodyCode conclusionCode body conclusion
          (base + 23) (base + 24) (base + 25) (base + 26)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp) hTraceIndex
          (by
            intro id replacement leftTerm rightTerm
            simp [case_analysis_axiom_code_term,
              Term.substituteFree])
          (by simpa [hTag] using hCertificate)
          hCodes hBodyCode hConclusionCode
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaTerm]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
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
      apply FirstOrder.Derives.disjIntroLeft
        (hRightCheck := Formula.check_certificate_of_admissible hTail₇)
      simpa using hBranch

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
