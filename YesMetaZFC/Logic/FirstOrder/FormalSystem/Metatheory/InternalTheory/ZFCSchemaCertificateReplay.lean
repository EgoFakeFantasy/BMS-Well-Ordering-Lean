import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.ForallPrefix

/-!
# ZFC schema 证书的闭项 witness 装配

本模块只负责把已经检查过的闭项组件装入对象 verifier 的五层存在量词。
canonical 公式码、shift 与前缀的具体证书仍由上游模块提供；这里不把这些组件
重新包装成更强的“总证明谓词”。
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

set_option autoImplicit false

/-! ## 规范 schema 证书的逐层有限边界 -/

/--
规范 schema 证书的每一层 payload 都严格受上一层 Gödel 对码控制。

证明只使用地面配对计算与数值上界；对象层 verifier 因而获得有限反演边界，
无需假设或先行证明任意对象自然数上的配对函数全局单射。
-/
theorem fs_zfc_support_raw_schema_certificate_bounds_of_values
    (schemaTag parameterCount bodyTokenValue : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_schema_certificate_bounds
        (numₘ(godel_pair_value 1
          (godel_pair_value schemaTag
            (godel_pair_value parameterCount bodyTokenValue))))
        (numₘ(schemaTag))
        (numₘ(parameterCount))
        (numₘ(bodyTokenValue))) := by
  let bodyValue : Nat :=
    godel_pair_value parameterCount bodyTokenValue
  let schemaValue : Nat :=
    godel_pair_value schemaTag bodyValue
  let certificateValue : Nat :=
    godel_pair_value 1 schemaValue
  let bodyPayload : SetTerm :=
    fs_zfc_schema_body_payload_term
      (numₘ(parameterCount)) (numₘ(bodyTokenValue))
  let schemaPayload : SetTerm :=
    fs_zfc_schema_payload_term
      (numₘ(schemaTag))
      (numₘ(parameterCount)) (numₘ(bodyTokenValue))
  have hBodyPayload :
      Term.Admissible bodyPayload SetSort.set := by
    simpa [bodyPayload] using
      fs_zfc_schema_body_payload_term_admissible
        (numₘ(parameterCount)) (numₘ(bodyTokenValue))
        (finite_numeral_term_admissible parameterCount)
        (finite_numeral_term_admissible bodyTokenValue)
  have hSchemaPayload :
      Term.Admissible schemaPayload SetSort.set := by
    simpa [schemaPayload] using
      fs_zfc_schema_payload_term_admissible
        (numₘ(schemaTag))
        (numₘ(parameterCount)) (numₘ(bodyTokenValue))
        (finite_numeral_term_admissible schemaTag)
        (finite_numeral_term_admissible parameterCount)
        (finite_numeral_term_admissible bodyTokenValue)
  have hBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        bodyPayload ≐ₘ numₘ(bodyValue)) := by
    simpa [bodyPayload, bodyValue,
      fs_zfc_schema_body_payload_term] using
      fs_zfc_support_raw_godel_pair_value_eq
        parameterCount bodyTokenValue
  have hSchemaCongruence :
      Derives fs_zfc_support_raw_theory [] (
        schemaPayload ≐ₘ
          godel_pairₘ(⟨numₘ(schemaTag),
            numₘ(bodyValue)⟩ₘ)) := by
    simpa [schemaPayload, fs_zfc_schema_payload_term] using
      godel_pairing_term_congr_of_equalities
        (numₘ(schemaTag)) (numₘ(schemaTag))
        bodyPayload (numₘ(bodyValue))
        (finite_numeral_term_admissible schemaTag)
        (finite_numeral_term_admissible schemaTag)
        hBodyPayload
        (finite_numeral_term_admissible bodyValue)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(schemaTag)))
        hBodyEquality
  have hSchemaGround :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨numₘ(schemaTag),
          numₘ(bodyValue)⟩ₘ) ≐ₘ
            numₘ(schemaValue)) := by
    simpa [schemaValue] using
      fs_zfc_support_raw_godel_pair_value_eq
        schemaTag bodyValue
  have hSchemaEquality :
      Derives fs_zfc_support_raw_theory [] (
        schemaPayload ≐ₘ numₘ(schemaValue)) :=
    Metatheory.Derives.equality_trans
      hSchemaCongruence hSchemaGround
  have hCertificateReflexive :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(certificateValue) ≐ₘ
          numₘ(certificateValue)) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(certificateValue))
  have hParameterReflexive :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount) ≐ₘ numₘ(parameterCount)) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(parameterCount))
  have hBodyTokenReflexive :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(bodyTokenValue) ≐ₘ numₘ(bodyTokenValue)) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(bodyTokenValue))
  have hSchemaBound :
      Derives fs_zfc_support_raw_theory [] (
        schemaPayload ∈ₘ Sₘ(numₘ(certificateValue))) :=
    fs_zfc_support_raw_member_successor_of_numeral_equalities
      schemaPayload (numₘ(certificateValue))
      schemaValue certificateValue
      hSchemaPayload
      (finite_numeral_term_admissible certificateValue)
      hSchemaEquality hCertificateReflexive
      (right_le_godel_pair_value 1 schemaValue)
  have hBodyBound :
      Derives fs_zfc_support_raw_theory [] (
        bodyPayload ∈ₘ Sₘ(schemaPayload)) :=
    fs_zfc_support_raw_member_successor_of_numeral_equalities
      bodyPayload schemaPayload
      bodyValue schemaValue
      hBodyPayload hSchemaPayload
      hBodyEquality hSchemaEquality
      (right_le_godel_pair_value schemaTag bodyValue)
  have hParameterBound :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount) ∈ₘ Sₘ(bodyPayload)) :=
    fs_zfc_support_raw_member_successor_of_numeral_equalities
      (numₘ(parameterCount)) bodyPayload
      parameterCount bodyValue
      (finite_numeral_term_admissible parameterCount)
      hBodyPayload
      hParameterReflexive hBodyEquality
      (left_le_godel_pair_value parameterCount bodyTokenValue)
  have hBodyTokenBound :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(bodyTokenValue) ∈ₘ Sₘ(bodyPayload)) :=
    fs_zfc_support_raw_member_successor_of_numeral_equalities
      (numₘ(bodyTokenValue)) bodyPayload
      bodyTokenValue bodyValue
      (finite_numeral_term_admissible bodyTokenValue)
      hBodyPayload
      hBodyTokenReflexive hBodyEquality
      (right_le_godel_pair_value parameterCount bodyTokenValue)
  simpa [fs_zfc_schema_certificate_bounds,
    bodyPayload, schemaPayload,
    bodyValue, schemaValue, certificateValue] using
    FirstOrder.Derives.conjIntro hSchemaBound
      (FirstOrder.Derives.conjIntro hBodyBound
        (FirstOrder.Derives.conjIntro
          hParameterBound hBodyTokenBound))

/-! ## 分离条件的闭项装配 -/

/-- 将闭项组件装入分离 verifier 的五层存在量词。 -/
theorem fs_zfc_support_raw_separation_condition_with_base_of_closed_components
    (formula certificate parameter bodyTokenCode bodyCode shiftOne shiftTwo : SetTerm)
    (base : FreeVarId)
    (hFormula : GodelQuotation.Numbered.CodeBoundary formula)
    (hCertificate : GodelQuotation.Numbered.CodeBoundary certificate)
    (hParameter : GodelQuotation.Numbered.CodeBoundary parameter)
    (hBodyTokenCode :
      GodelQuotation.Numbered.CodeBoundary bodyTokenCode)
    (hBodyCode : GodelQuotation.Numbered.CodeBoundary bodyCode)
    (hShiftOne : GodelQuotation.Numbered.CodeBoundary shiftOne)
    (hShiftTwo : GodelQuotation.Numbered.CodeBoundary shiftTwo)
    (hCertificateEq :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(0)) parameter bodyTokenCode))
    (hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(0))
          parameter bodyTokenCode))
    (hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (parameter ∈ₘ ωₘ))
    (hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 5) (base + 6)))
    (hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(parameter)) bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)))
    (hShiftFirst :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter bodyCode shiftOne
          (base + 17) (base + 18) (base + 19)))
    (hShiftSecond :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter shiftOne shiftTwo
          (base + 25) (base + 26) (base + 27)))
    (hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          parameter
          (fs_zfc_separation_core_code
            parameter shiftTwo)
          formula (base + 33) (base + 34))) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_separation_condition_with_base
        formula certificate base) := by
  let parameterOne : SetTerm := Sₘ(parameter)
  let parameterTwo : SetTerm := Sₘ(parameterOne)
  let body : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(0)) parameter bodyTokenCode) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(0))
          parameter bodyTokenCode) ∧ₘ
        ((parameter ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              bodyCode bodyTokenCode
              (base + 5) (base + 6)) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                parameterOne bodyCode
                (base + 7) (base + 8)
                (base + 9) (base + 10)
                (base + 11) (base + 12)
                (base + 13) (base + 14)
                (base + 15) (base + 16)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter bodyCode shiftOne
                  (base + 17) (base + 18) (base + 19)) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    parameter shiftOne shiftTwo
                    (base + 25) (base + 26) (base + 27)) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    parameter
                     (fs_zfc_separation_core_code
                       parameter shiftTwo)
                     formula (base + 33) (base + 34)))))))
  have hBody : Derives fs_zfc_support_raw_theory [] body := by
    dsimp [body, parameterOne, parameterTwo]
    exact FirstOrder.Derives.conjIntro
      hCertificateEq
      (FirstOrder.Derives.conjIntro
        hCertificateBounds
        (FirstOrder.Derives.conjIntro
          hParameterNatural
          (FirstOrder.Derives.conjIntro
            hSequence
            (FirstOrder.Derives.conjIntro
              hClassifier
              (FirstOrder.Derives.conjIntro
                hShiftFirst
                (FirstOrder.Derives.conjIntro
                  hShiftSecond hPrefix))))))
  have hFixed (term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term)
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement term = term :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTerm id replacement
  have hParameterFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport parameter := by
    rw [hParameter.2]
    exact List.not_mem_nil
  have hBodyTokenFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport bodyTokenCode := by
    rw [hBodyTokenCode.2]
    exact List.not_mem_nil
  have hBodyCodeFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport bodyCode := by
    rw [hBodyCode.2]
    exact List.not_mem_nil
  have hShiftOneFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport shiftOne := by
    rw [hShiftOne.2]
    exact List.not_mem_nil
  have hShiftTwoFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport shiftTwo := by
    rw [hShiftTwo.2]
    exact List.not_mem_nil
  have hNumeralClose (value : Nat) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      ⟨finite_numeral_term_admissible value,
        finite_numeral_term_freeSupport value⟩
      id depth
  have hNumeralSubstitute (value : Nat) (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      ⟨finite_numeral_term_admissible value,
        finite_numeral_term_freeSupport value⟩
      id replacement
  have hParameterCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base ≠ closed) :
      Term.substituteFree SetSort.set base parameter
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set base parameter term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set base closed depth parameter term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hParameter closed depth]
  have hBodyTokenCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 1 ≠ closed) :
      Term.substituteFree SetSort.set (base + 1) bodyTokenCode
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 1) bodyTokenCode term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 1) closed depth bodyTokenCode term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hBodyTokenCode closed depth]
  have hBodyCodeCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 2 ≠ closed) :
      Term.substituteFree SetSort.set (base + 2) bodyCode
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 2) bodyCode term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 2) closed depth bodyCode term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hBodyCode closed depth]
  have hShiftOneCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 3 ≠ closed) :
      Term.substituteFree SetSort.set (base + 3) shiftOne
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 3) shiftOne term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 3) closed depth shiftOne term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hShiftOne closed depth]
  have hShiftTwoCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 4 ≠ closed) :
      Term.substituteFree SetSort.set (base + 4) shiftTwo
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 4) shiftTwo term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 4) closed depth shiftTwo term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hShiftTwo closed depth]
  have hShiftSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (indexId sourceDepthId targetDepthId : FreeVarId)
      (hSourceNeIndex : sourceId ≠ indexId)
      (hSourceNeSourceDepth : sourceId ≠ sourceDepthId)
      (hSourceNeTargetDepth : sourceId ≠ targetDepthId) :
      ∀ cutoff sourceCode targetCode,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_project_shift_code_condition_with_ids
              cutoff sourceCode targetCode
              indexId sourceDepthId targetDepthId) =
          canonical_project_shift_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement cutoff)
            (Term.substituteFree SetSort.set sourceId replacement sourceCode)
            (Term.substituteFree SetSort.set sourceId replacement targetCode)
            indexId sourceDepthId targetDepthId := by
    intro cutoff sourceCode targetCode
    exact canonical_project_shift_code_condition_with_ids_substitute_closed
      cutoff sourceCode targetCode replacement
      (Term.substituteFree SetSort.set sourceId replacement cutoff)
      (Term.substituteFree SetSort.set sourceId replacement sourceCode)
      (Term.substituteFree SetSort.set sourceId replacement targetCode)
      sourceId indexId sourceDepthId targetDepthId
      hSourceNeIndex hSourceNeSourceDepth hSourceNeTargetDepth
      hReplacement rfl rfl rfl
  have hClassifierSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (hCodes : sourceId ≠ base + 7)
      (hDepths : sourceId ≠ base + 8)
      (hLastIndex : sourceId ≠ base + 9)
      (hIndex : sourceId ≠ base + 10)
      (hFirstPremise : sourceId ≠ base + 11)
      (hSecondPremise : sourceId ≠ base + 12)
      (hLeftCode : sourceId ≠ base + 13)
      (hRightCode : sourceId ≠ base + 14)
      (hLeftDepth : sourceId ≠ base + 15)
      (hRightDepth : sourceId ≠ base + 16) :
      ∀ entryDepth code,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_project_formula_code_condition_with_ids
              entryDepth code
              (base + 7) (base + 8) (base + 9) (base + 10)
              (base + 11) (base + 12) (base + 13) (base + 14)
              (base + 15) (base + 16)) =
          canonical_project_formula_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement entryDepth)
            (Term.substituteFree SetSort.set sourceId replacement code)
            (base + 7) (base + 8) (base + 9) (base + 10)
            (base + 11) (base + 12) (base + 13) (base + 14)
            (base + 15) (base + 16) := by
    intro entryDepth code
    exact canonical_project_formula_code_condition_with_ids_substitute_closed
      entryDepth code replacement
      (Term.substituteFree SetSort.set sourceId replacement entryDepth)
      (Term.substituteFree SetSort.set sourceId replacement code)
      sourceId
      (base + 7) (base + 8) (base + 9) (base + 10)
      (base + 11) (base + 12) (base + 13) (base + 14)
      (base + 15) (base + 16)
      hCodes hDepths hLastIndex hIndex hFirstPremise
      hSecondPremise hLeftCode hRightCode hLeftDepth hRightDepth
      hReplacement rfl rfl
  have hPrefixSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (hTrace : sourceId ≠ base + 33)
      (hIndex : sourceId ≠ base + 34) :
      ∀ binderCount core code,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_forall_prefix_code_condition_with_ids
              binderCount core code (base + 33) (base + 34)) =
          canonical_forall_prefix_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement binderCount)
            (Term.substituteFree SetSort.set sourceId replacement core)
            (Term.substituteFree SetSort.set sourceId replacement code)
            (base + 33) (base + 34) := by
    intro binderCount core code
    exact canonical_forall_prefix_code_condition_with_ids_substitute_closed
      binderCount core code replacement
      (Term.substituteFree SetSort.set sourceId replacement binderCount)
      (Term.substituteFree SetSort.set sourceId replacement core)
      (Term.substituteFree SetSort.set sourceId replacement code)
      sourceId (base + 33) (base + 34)
      hTrace hIndex hReplacement rfl rfl rfl
  have hParameterShiftFirst :=
    hShiftSubstitute base parameter hParameter
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hParameterShiftSecond :=
    hShiftSubstitute base parameter hParameter
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hBodyTokenShiftFirst :=
    hShiftSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hBodyTokenShiftSecond :=
    hShiftSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hBodyCodeShiftFirst :=
    hShiftSubstitute (base + 2) bodyCode hBodyCode
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hBodyCodeShiftSecond :=
    hShiftSubstitute (base + 2) bodyCode hBodyCode
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hShiftOneShiftFirst :=
    hShiftSubstitute (base + 3) shiftOne hShiftOne
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hShiftOneShiftSecond :=
    hShiftSubstitute (base + 3) shiftOne hShiftOne
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hShiftTwoShiftFirst :=
    hShiftSubstitute (base + 4) shiftTwo hShiftTwo
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hShiftTwoShiftSecond :=
    hShiftSubstitute (base + 4) shiftTwo hShiftTwo
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hParameterClassifier :=
    hClassifierSubstitute base parameter hParameter
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hBodyTokenClassifier :=
    hClassifierSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hBodyCodeClassifier :=
    hClassifierSubstitute (base + 2) bodyCode hBodyCode
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hShiftOneClassifier :=
    hClassifierSubstitute (base + 3) shiftOne hShiftOne
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hShiftTwoClassifier :=
    hClassifierSubstitute (base + 4) shiftTwo hShiftTwo
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hParameterPrefix :=
    hPrefixSubstitute base parameter hParameter (by simp) (by simp)
  have hBodyTokenPrefix :=
    hPrefixSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (by simp) (by simp)
  have hBodyCodePrefix :=
    hPrefixSubstitute (base + 2) bodyCode hBodyCode
      (by simp) (by simp)
  have hShiftOnePrefix :=
    hPrefixSubstitute (base + 3) shiftOne hShiftOne
      (by simp) (by simp)
  have hShiftTwoPrefix :=
    hPrefixSubstitute (base + 4) shiftTwo hShiftTwo
      (by simp) (by simp)
  unfold fs_zfc_separation_condition_with_base
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := parameter) base
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 1) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 1))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := bodyTokenCode) (base + 1)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 2) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 2))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 2) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 2))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := bodyCode) (base + 2)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 3) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 3))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 3) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 3))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 3) 0 bodyCode _ (by simp)
    hBodyCode.1.2 (hBodyCodeFresh (base + 3))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := shiftOne) (base + 3)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 4) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 4) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 4) 0 bodyCode _ (by simp)
    hBodyCode.1.2 (hBodyCodeFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 3) (base + 4) 0 shiftOne _ (by simp)
    hShiftOne.1.2 (hShiftOneFresh (base + 4))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := shiftTwo) (base + 4)
  simp only [Formula.substituteFree]
  simpa [Formula.substituteFree_self, Term.substituteFree_self,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    fs_zfc_separation_condition_with_base, body,
    fs_zfc_schema_certificate_term,
    fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt,
    Formula.freeSupport, Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    Term.not_mem_freeSupport_closeFreeAt_of_not_mem,
    parameterOne, parameterTwo,
    hFixed formula hFormula,
    hFixed certificate hCertificate,
    hFixed parameter hParameter,
    hFixed bodyTokenCode hBodyTokenCode,
    hFixed bodyCode hBodyCode,
    hFixed shiftOne hShiftOne,
    hFixed shiftTwo hShiftTwo,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hFormula,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hCertificate,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hParameter,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hBodyTokenCode,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hBodyCode,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hShiftOne,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hShiftTwo,
    hNumeralClose,
    hNumeralSubstitute,
    fs_zfc_separation_core_code,
    fs_zfc_hilbert_iff_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    membership_atomic_formula_code_term,
    binary_atomic_formula_code_term,
    canonical_binder_variable_code_term,
    canonical_binder_name_term,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence,
    GodelQuotation.standard_sequence_from,
    hParameterCloseSubstituteComm,
    hBodyTokenCloseSubstituteComm,
    hBodyCodeCloseSubstituteComm,
    hShiftOneCloseSubstituteComm,
    hShiftTwoCloseSubstituteComm,
    hParameterShiftFirst, hParameterShiftSecond,
    hBodyTokenShiftFirst, hBodyTokenShiftSecond,
    hBodyCodeShiftFirst, hBodyCodeShiftSecond,
    hShiftOneShiftFirst, hShiftOneShiftSecond,
    hShiftTwoShiftFirst, hShiftTwoShiftSecond,
    hParameterClassifier, hBodyTokenClassifier,
    hBodyCodeClassifier, hShiftOneClassifier, hShiftTwoClassifier,
    hParameterPrefix, hBodyTokenPrefix, hBodyCodePrefix,
    hShiftOnePrefix, hShiftTwoPrefix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.succ_eq_add_one] using hBody

/-! ## 收集条件的闭项装配 -/

/-- 将闭项组件装入收集 verifier 的五层存在量词。 -/
theorem fs_zfc_support_raw_collection_condition_with_base_of_closed_components
    (formula certificate parameter bodyTokenCode bodyCode shiftOne shiftTwo : SetTerm)
    (base : FreeVarId)
    (hFormula : GodelQuotation.Numbered.CodeBoundary formula)
    (hCertificate : GodelQuotation.Numbered.CodeBoundary certificate)
    (hParameter : GodelQuotation.Numbered.CodeBoundary parameter)
    (hBodyTokenCode :
      GodelQuotation.Numbered.CodeBoundary bodyTokenCode)
    (hBodyCode : GodelQuotation.Numbered.CodeBoundary bodyCode)
    (hShiftOne : GodelQuotation.Numbered.CodeBoundary shiftOne)
    (hShiftTwo : GodelQuotation.Numbered.CodeBoundary shiftTwo)
    (hCertificateEq :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(1)) parameter bodyTokenCode))
    (hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(1))
          parameter bodyTokenCode))
    (hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (parameter ∈ₘ ωₘ))
    (hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 5) (base + 6)))
    (hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(Sₘ(parameter))) bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)))
    (hShiftFirst :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter bodyCode shiftOne
          (base + 17) (base + 18) (base + 19)))
    (hShiftSecond :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter shiftOne shiftTwo
          (base + 25) (base + 26) (base + 27)))
    (hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          parameter
          (fs_zfc_collection_core_code
            parameter shiftOne shiftTwo)
          formula (base + 33) (base + 34))) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_collection_condition_with_base
        formula certificate base) := by
  let parameterOne : SetTerm := Sₘ(parameter)
  let parameterTwo : SetTerm := Sₘ(parameterOne)
  let parameterThree : SetTerm := Sₘ(parameterTwo)
  let body : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(1)) parameter bodyTokenCode) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(1))
          parameter bodyTokenCode) ∧ₘ
        ((parameter ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              bodyCode bodyTokenCode
              (base + 5) (base + 6)) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                parameterTwo bodyCode
                (base + 7) (base + 8)
                (base + 9) (base + 10)
                (base + 11) (base + 12)
                (base + 13) (base + 14)
                (base + 15) (base + 16)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter bodyCode shiftOne
                  (base + 17) (base + 18) (base + 19)) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    parameter shiftOne shiftTwo
                    (base + 25) (base + 26) (base + 27)) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    parameter
                    (fs_zfc_collection_core_code
                      parameter shiftOne shiftTwo)
                    formula (base + 33) (base + 34)))))))
  have hBody : Derives fs_zfc_support_raw_theory [] body := by
    dsimp [body, parameterOne, parameterTwo, parameterThree]
    exact FirstOrder.Derives.conjIntro
      hCertificateEq
      (FirstOrder.Derives.conjIntro
        hCertificateBounds
        (FirstOrder.Derives.conjIntro
          hParameterNatural
          (FirstOrder.Derives.conjIntro
            hSequence
            (FirstOrder.Derives.conjIntro
              hClassifier
              (FirstOrder.Derives.conjIntro
                hShiftFirst
                (FirstOrder.Derives.conjIntro
                  hShiftSecond hPrefix))))))
  have hFixed (term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term)
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement term = term :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTerm id replacement
  have hParameterFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport parameter := by
    rw [hParameter.2]
    exact List.not_mem_nil
  have hBodyTokenFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport bodyTokenCode := by
    rw [hBodyTokenCode.2]
    exact List.not_mem_nil
  have hBodyCodeFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport bodyCode := by
    rw [hBodyCode.2]
    exact List.not_mem_nil
  have hShiftOneFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport shiftOne := by
    rw [hShiftOne.2]
    exact List.not_mem_nil
  have hShiftTwoFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport shiftTwo := by
    rw [hShiftTwo.2]
    exact List.not_mem_nil
  have hNumeralClose (value : Nat) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      ⟨finite_numeral_term_admissible value,
        finite_numeral_term_freeSupport value⟩
      id depth
  have hNumeralSubstitute (value : Nat) (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      ⟨finite_numeral_term_admissible value,
        finite_numeral_term_freeSupport value⟩
      id replacement
  have hParameterCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base ≠ closed) :
      Term.substituteFree SetSort.set base parameter
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set base parameter term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set base closed depth parameter term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hParameter closed depth]
  have hBodyTokenCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 1 ≠ closed) :
      Term.substituteFree SetSort.set (base + 1) bodyTokenCode
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 1) bodyTokenCode term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 1) closed depth bodyTokenCode term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hBodyTokenCode closed depth]
  have hBodyCodeCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 2 ≠ closed) :
      Term.substituteFree SetSort.set (base + 2) bodyCode
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 2) bodyCode term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 2) closed depth bodyCode term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hBodyCode closed depth]
  have hShiftOneCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 3 ≠ closed) :
      Term.substituteFree SetSort.set (base + 3) shiftOne
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 3) shiftOne term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 3) closed depth shiftOne term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hShiftOne closed depth]
  have hShiftTwoCloseSubstituteComm
      (closed : FreeVarId) (depth : Nat) (term : SetTerm)
      (hDistinct : base + 4 ≠ closed) :
      Term.substituteFree SetSort.set (base + 4) shiftTwo
          (Term.closeFreeAt SetSort.set closed depth term) =
        Term.closeFreeAt SetSort.set closed depth
          (Term.substituteFree SetSort.set (base + 4) shiftTwo term) := by
    symm
    rw [Term.closeFreeAt_substituteFree_comm
      SetSort.set (base + 4) closed depth shiftTwo term hDistinct]
    rw [GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
      hShiftTwo closed depth]
  have hShiftSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (indexId sourceDepthId targetDepthId : FreeVarId)
      (hSourceNeIndex : sourceId ≠ indexId)
      (hSourceNeSourceDepth : sourceId ≠ sourceDepthId)
      (hSourceNeTargetDepth : sourceId ≠ targetDepthId) :
      ∀ cutoff sourceCode targetCode,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_project_shift_code_condition_with_ids
              cutoff sourceCode targetCode
              indexId sourceDepthId targetDepthId) =
          canonical_project_shift_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement cutoff)
            (Term.substituteFree SetSort.set sourceId replacement sourceCode)
            (Term.substituteFree SetSort.set sourceId replacement targetCode)
            indexId sourceDepthId targetDepthId := by
    intro cutoff sourceCode targetCode
    exact canonical_project_shift_code_condition_with_ids_substitute_closed
      cutoff sourceCode targetCode replacement
      (Term.substituteFree SetSort.set sourceId replacement cutoff)
      (Term.substituteFree SetSort.set sourceId replacement sourceCode)
      (Term.substituteFree SetSort.set sourceId replacement targetCode)
      sourceId indexId sourceDepthId targetDepthId
      hSourceNeIndex hSourceNeSourceDepth hSourceNeTargetDepth
      hReplacement rfl rfl rfl
  have hClassifierSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (hCodes : sourceId ≠ base + 7)
      (hDepths : sourceId ≠ base + 8)
      (hLastIndex : sourceId ≠ base + 9)
      (hIndex : sourceId ≠ base + 10)
      (hFirstPremise : sourceId ≠ base + 11)
      (hSecondPremise : sourceId ≠ base + 12)
      (hLeftCode : sourceId ≠ base + 13)
      (hRightCode : sourceId ≠ base + 14)
      (hLeftDepth : sourceId ≠ base + 15)
      (hRightDepth : sourceId ≠ base + 16) :
      ∀ entryDepth code,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_project_formula_code_condition_with_ids
              entryDepth code
              (base + 7) (base + 8) (base + 9) (base + 10)
              (base + 11) (base + 12) (base + 13) (base + 14)
              (base + 15) (base + 16)) =
          canonical_project_formula_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement entryDepth)
            (Term.substituteFree SetSort.set sourceId replacement code)
            (base + 7) (base + 8) (base + 9) (base + 10)
            (base + 11) (base + 12) (base + 13) (base + 14)
            (base + 15) (base + 16) := by
    intro entryDepth code
    exact canonical_project_formula_code_condition_with_ids_substitute_closed
      entryDepth code replacement
      (Term.substituteFree SetSort.set sourceId replacement entryDepth)
      (Term.substituteFree SetSort.set sourceId replacement code)
      sourceId
      (base + 7) (base + 8) (base + 9) (base + 10)
      (base + 11) (base + 12) (base + 13) (base + 14)
      (base + 15) (base + 16)
      hCodes hDepths hLastIndex hIndex hFirstPremise
      hSecondPremise hLeftCode hRightCode hLeftDepth hRightDepth
      hReplacement rfl rfl
  have hPrefixSubstitute
      (sourceId : FreeVarId) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (hTrace : sourceId ≠ base + 33)
      (hIndex : sourceId ≠ base + 34) :
      ∀ binderCount core code,
        Formula.substituteFree SetSort.set sourceId replacement
            (canonical_forall_prefix_code_condition_with_ids
              binderCount core code (base + 33) (base + 34)) =
          canonical_forall_prefix_code_condition_with_ids
            (Term.substituteFree SetSort.set sourceId replacement binderCount)
            (Term.substituteFree SetSort.set sourceId replacement core)
            (Term.substituteFree SetSort.set sourceId replacement code)
            (base + 33) (base + 34) := by
    intro binderCount core code
    exact canonical_forall_prefix_code_condition_with_ids_substitute_closed
      binderCount core code replacement
      (Term.substituteFree SetSort.set sourceId replacement binderCount)
      (Term.substituteFree SetSort.set sourceId replacement core)
      (Term.substituteFree SetSort.set sourceId replacement code)
      sourceId (base + 33) (base + 34)
      hTrace hIndex hReplacement rfl rfl rfl
  have hParameterShiftFirst :=
    hShiftSubstitute base parameter hParameter
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hParameterShiftSecond :=
    hShiftSubstitute base parameter hParameter
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hBodyTokenShiftFirst :=
    hShiftSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hBodyTokenShiftSecond :=
    hShiftSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hBodyCodeShiftFirst :=
    hShiftSubstitute (base + 2) bodyCode hBodyCode
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hBodyCodeShiftSecond :=
    hShiftSubstitute (base + 2) bodyCode hBodyCode
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hShiftOneShiftFirst :=
    hShiftSubstitute (base + 3) shiftOne hShiftOne
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hShiftOneShiftSecond :=
    hShiftSubstitute (base + 3) shiftOne hShiftOne
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hShiftTwoShiftFirst :=
    hShiftSubstitute (base + 4) shiftTwo hShiftTwo
      (base + 17) (base + 18) (base + 19)
      (by simp) (by simp) (by simp)
  have hShiftTwoShiftSecond :=
    hShiftSubstitute (base + 4) shiftTwo hShiftTwo
      (base + 25) (base + 26) (base + 27)
      (by simp) (by simp) (by simp)
  have hParameterClassifier :=
    hClassifierSubstitute base parameter hParameter
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hBodyTokenClassifier :=
    hClassifierSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hBodyCodeClassifier :=
    hClassifierSubstitute (base + 2) bodyCode hBodyCode
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hShiftOneClassifier :=
    hClassifierSubstitute (base + 3) shiftOne hShiftOne
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hShiftTwoClassifier :=
    hClassifierSubstitute (base + 4) shiftTwo hShiftTwo
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have hParameterPrefix :=
    hPrefixSubstitute base parameter hParameter (by simp) (by simp)
  have hBodyTokenPrefix :=
    hPrefixSubstitute (base + 1) bodyTokenCode hBodyTokenCode
      (by simp) (by simp)
  have hBodyCodePrefix :=
    hPrefixSubstitute (base + 2) bodyCode hBodyCode
      (by simp) (by simp)
  have hShiftOnePrefix :=
    hPrefixSubstitute (base + 3) shiftOne hShiftOne
      (by simp) (by simp)
  have hShiftTwoPrefix :=
    hPrefixSubstitute (base + 4) shiftTwo hShiftTwo
      (by simp) (by simp)
  unfold fs_zfc_collection_condition_with_base
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := parameter) base
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 1) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 1))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := bodyTokenCode) (base + 1)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 2) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 2))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 2) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 2))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := bodyCode) (base + 2)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 3) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 3))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 3) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 3))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 3) 0 bodyCode _ (by simp)
    hBodyCode.1.2 (hBodyCodeFresh (base + 3))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := shiftOne) (base + 3)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 4) 0 parameter _ (by simp)
    hParameter.1.2 (hParameterFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 4) 0 bodyTokenCode _ (by simp)
    hBodyTokenCode.1.2 (hBodyTokenFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 4) 0 bodyCode _ (by simp)
    hBodyCode.1.2 (hBodyCodeFresh (base + 4))]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 3) (base + 4) 0 shiftOne _ (by simp)
    hShiftOne.1.2 (hShiftOneFresh (base + 4))]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := shiftTwo) (base + 4)
  simp only [Formula.substituteFree]
  simpa [Formula.substituteFree_self, Term.substituteFree_self,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    fs_zfc_collection_condition_with_base, body,
    fs_zfc_schema_certificate_term,
    fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt,
    Formula.freeSupport, Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    Term.not_mem_freeSupport_closeFreeAt_of_not_mem,
    parameterOne, parameterTwo, parameterThree,
    hFixed formula hFormula,
    hFixed certificate hCertificate,
    hFixed parameter hParameter,
    hFixed bodyTokenCode hBodyTokenCode,
    hFixed bodyCode hBodyCode,
    hFixed shiftOne hShiftOne,
    hFixed shiftTwo hShiftTwo,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hFormula,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hCertificate,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hParameter,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hBodyTokenCode,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hBodyCode,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hShiftOne,
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hShiftTwo,
    hNumeralClose,
    hNumeralSubstitute,
    fs_zfc_collection_core_code,
    fs_zfc_hilbert_iff_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    membership_atomic_formula_code_term,
    binary_atomic_formula_code_term,
    canonical_binder_variable_code_term,
    canonical_binder_name_term,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence,
    GodelQuotation.standard_sequence_from,
    hParameterCloseSubstituteComm,
    hBodyTokenCloseSubstituteComm,
    hBodyCodeCloseSubstituteComm,
    hShiftOneCloseSubstituteComm,
    hShiftTwoCloseSubstituteComm,
    hParameterShiftFirst, hParameterShiftSecond,
    hBodyTokenShiftFirst, hBodyTokenShiftSecond,
    hBodyCodeShiftFirst, hBodyCodeShiftSecond,
    hShiftOneShiftFirst, hShiftOneShiftSecond,
    hShiftTwoShiftFirst, hShiftTwoShiftSecond,
    hParameterClassifier, hBodyTokenClassifier,
    hBodyCodeClassifier, hShiftOneClassifier, hShiftTwoClassifier,
    hParameterPrefix, hBodyTokenPrefix, hBodyCodePrefix,
    hShiftOnePrefix, hShiftTwoPrefix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.succ_eq_add_one] using hBody

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
