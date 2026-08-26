import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPayloadFailureInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalSpecializationCaptureFailureAdapter

/-!
# 等式替换逻辑公理的失败适配

本模块只把 tag 10 的宿主检查失败转换为对象层证书条件的否定。成功解码、
替换与捕获反演全部由既有接口提供；公开结论不携带 replay trace。
-/

namespace YesMetaZFC.Logic.FirstOrder

open Nonlogical.BasicSetTheory
open FormalSystem
open FormalSystem.Rosser
open FormalSystem.GodelQuotation
open FormalSystem.ProofCode
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

namespace FormalSystem.CertifiedProof

/-- 标准单变量 token 串满足对象项码谓词。 -/
private theorem gq_standard_named_variable_is_term_code
    (name : Nat) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(
        standard_token_sequence
          [Numbered.variable_token name]) := by
  let named := Numbered.named_variable_code name
  let standard :=
    standard_token_sequence [Numbered.variable_token name]
  have hNamed :
      ⊢ₘ[godel_quotation_theory] term_codeₘ(named) := by
    simpa [named] using
      named_variable_code_is_term_code name
  have hNamedMember :
      ⊢ₘ[godel_quotation_theory] named ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (gq_term_code_definition_instance named <| by
        simpa [named] using
          variable_code_term_admissible
            (numₘ(name))
            (finite_numeral_term_admissible name))
      hNamed
  have hEquality :
      ⊢ₘ[godel_quotation_theory] named ≐ₘ standard := by
    simpa [named, standard] using
      named_variable_code_eq_standard_token_sequence name
  have hStandardMember :
      ⊢ₘ[godel_quotation_theory] standard ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        named standard TermCodeₘ
        (by
          simpa [named] using
            variable_code_term_admissible
              (numₘ(name))
              (finite_numeral_term_admissible name))
        (by
          exact standard_token_sequence_admissible _)
        term_code_set_term_admissible hEquality)
      hNamedMember
  exact FirstOrder.Derives.iffElimLeft
    (gq_term_code_definition_instance standard <| by
      exact standard_token_sequence_admissible _)
    hStandardMember

/-- 两个对象变量码的等式公式码与对应标准 token 串一致。 -/
private theorem fs_zfc_support_raw_equality_code_eq_standard_variables
    {Γ : Context signature}
    (leftId rightId : Nat)
    (left right : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ≐ₘ standard_token_sequence
          [Numbered.variable_token (free_name leftId)])
    (hRightEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ≐ₘ standard_token_sequence
          [Numbered.variable_token (free_name rightId)]) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      eq_codeₘ(left, right) ≐ₘ
        standard_token_sequence
          (Numbered.equality_tokens
            [Numbered.variable_token (free_name leftId)]
            [Numbered.variable_token (free_name rightId)]) := by
  let leftTokens : List Nat :=
    [Numbered.variable_token (free_name leftId)]
  let rightTokens : List Nat :=
    [Numbered.variable_token (free_name rightId)]
  let leftStandard := standard_token_sequence leftTokens
  let rightStandard := standard_token_sequence rightTokens
  have hCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        eq_codeₘ(left, right) ≐ₘ
          eq_codeₘ(leftStandard, rightStandard) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => eq_codeₘ(left, right))
      (fun left right hLeft hRight =>
        equality_formula_code_term_admissible
          left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      left
      leftStandard
      right
      rightStandard
      hLeft.admissible
      (by
        exact standard_token_sequence_admissible _)
      hRight.admissible
      (by
        exact standard_token_sequence_admissible _)
      (by simpa [leftStandard, leftTokens] using hLeftEquality)
      (by simpa [rightStandard, rightTokens] using hRightEquality)
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        eq_codeₘ(leftStandard, rightStandard) ≐ₘ
          standard_token_sequence
            (Numbered.equality_tokens leftTokens rightTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          equality_formula_code_eq_standard_token_sequence
            leftTokens rightTokens leftStandard rightStandard
            (gq_standard_named_variable_is_term_code
              (free_name leftId))
            (gq_standard_named_variable_is_term_code
              (free_name rightId))
            (by
              simpa [leftStandard, leftTokens] using
                (FirstOrder.Derives.eq_refl_m leftStandard))
            (by
              simpa [rightStandard, rightTokens] using
                (FirstOrder.Derives.eq_refl_m rightStandard))
  simpa [leftStandard, rightStandard, leftTokens, rightTokens] using
    Metatheory.Derives.equality_trans hCongruence hStandard

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/--
tag 10 的 payload 长度、正文解码、替换安全性或最终公式匹配任一失败，均在
对象层否定等式替换证书条件。
-/
theorem fs_zfc_support_raw_logical_equality_substitution_neg_of_check_false
    (raw freeBase : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hTag : (godel_unpair_value raw).1 = 10)
    (hDecode : fs_formula_row_decode freeBase row = some decoded)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_equality_substitution_certificate_condition_with_ids
        (standard_token_sequence row) (numₘ(raw))
        (base + 58) (base + 59) (base + 60) (base + 61)
        (base + 40) (base + 41)) := by
  simp [fs_logical_base_axiom_check,
    fs_logical_base_axiom_check_with, hTag] at hCheck
  let payloadId := base + 58
  let sequenceId := base + 59
  let bodyId := base + 60
  let resultId := base + 61
  let traceId := base + 40
  let indexId := base + 41
  let leftVariable :=
    var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0)))
  let rightVariable :=
    var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1)))
  let fields : List SetFormula := [
    numₘ(raw) ≐ₘ
      godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ),
    nat_sequence_code_condition_with_ids
      (x#sequenceId) (x#payloadId) traceId indexId,
    domₘ(x#sequenceId) ≐ₘ numₘ(3),
    logical_formula_payload_component_condition_with_ids
      (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
      traceId indexId,
    ¬ₘ quantifier_occurs_condition leftVariable (x#bodyId),
    substitutableₘ(leftVariable, rightVariable, x#bodyId),
    code_substitution_spec
      (x#bodyId) leftVariable rightVariable (x#resultId),
    standard_token_sequence row ≐ₘ
      imp_codeₘ(
        eq_codeₘ(leftVariable, rightVariable),
        imp_codeₘ(x#bodyId, x#resultId))]
  let body := logical_certificate_conjunction fields
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId), (sequenceId, x#sequenceId),
    (bodyId, x#bodyId), (resultId, x#resultId)]
  have hCondition :=
    logical_equality_substitution_certificate_condition_with_ids_admissible
      (standard_token_sequence row) (numₘ(raw))
      payloadId sequenceId bodyId resultId traceId indexId
      (standard_token_sequence_admissible row)
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments
      assignments body <| by
        simpa [assignments, body, fields, payloadId, sequenceId,
          bodyId, resultId, traceId, indexId,
          leftVariable, rightVariable,
          logical_equality_substitution_certificate_condition_with_ids,
          Formula.existsFreeAssignments] using hCondition
  have hTraceIndex : traceId ≠ indexId := by
    simp [traceId, indexId]
  have hTraceFreshBody :
      (SetSort.set, traceId) ∉ Formula.freeSupport body := by
    intro hMember
    have hConditionMember :
        (SetSort.set, traceId) ∈
          Formula.freeSupport
            (Formula.existsFreeAssignments
              SetSort.set assignments body) :=
      fs_zfc_fo_failure_mem_exists_assignments
        assignments body (SetSort.set, traceId)
        (by
          intro assignment hAssignment
          simp only [assignments, List.mem_cons,
            List.not_mem_nil, or_false] at hAssignment
          rcases hAssignment with rfl | rfl | rfl | rfl
          all_goals
            simp [traceId, payloadId, sequenceId, bodyId, resultId])
        hMember
    rcases
        logical_equality_substitution_certificate_condition_with_ids_freeSupport_subset
          (standard_token_sequence row) (numₘ(raw))
          payloadId sequenceId bodyId resultId traceId indexId
          (SetSort.set, traceId)
          (by
            simpa [assignments, body, fields, payloadId, sequenceId,
              bodyId, resultId, traceId, indexId,
              leftVariable, rightVariable,
              logical_equality_substitution_certificate_condition_with_ids,
              Formula.existsFreeAssignments] using hConditionMember) with
      hFormula | hCertificate
    · simp at hFormula
    · simp [finite_numeral_term_freeSupport] at hCertificate
  apply fs_zfc_support_raw_exists_assignments_neg assignments body
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hAt : Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hBody)
  have hField :
      ∀ field, field ∈ fields →
        Γ ⊢ₘ[fs_zfc_support_raw_theory] field := by
    intro field hMember
    exact fs_zfc_fo_failure_conjunction_elim
      fields field hMember (by simpa [Γ, body] using hAt)
  have hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ) :=
    hField _ (by simp [fields])
  have hSequence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          (x#sequenceId) (x#payloadId) traceId indexId :=
    hField _ (by simp [fields])
  have hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(x#sequenceId) ≐ₘ numₘ(3) :=
    hField _ (by simp [fields])
  have hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
          traceId indexId :=
    hField _ (by simp [fields])
  have hNoQuantifier :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ quantifier_occurs_condition leftVariable (x#bodyId) :=
    hField _ (by simp [fields])
  have hSubstitutable :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        substitutableₘ(leftVariable, rightVariable, x#bodyId) :=
    hField _ (by simp [fields])
  have hSubstitution :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#bodyId) leftVariable rightVariable (x#resultId) :=
    hField _ (by simp [fields])
  have hFormulaField :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          imp_codeₘ(
            eq_codeₘ(leftVariable, rightVariable),
            imp_codeₘ(x#bodyId, x#resultId)) :=
    hField _ (by simp [fields])
  have hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    exact hTraceFreshBody
  have hLengthFalsum
      (hLength :
        (nat_sequence_decode
          (godel_unpair_value raw).2).length ≠ 3) :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
    fs_zfc_support_raw_logical_payload_length_falsum
      raw 10 3 (x#payloadId) (x#sequenceId)
      traceId indexId
      (set_variable_admissible payloadId)
      (set_variable_admissible sequenceId)
      hTraceIndex
      (fs_zfc_fo_failure_set_variable_fresh
        traceId sequenceId <| by
          simp [traceId, sequenceId])
      (fs_zfc_fo_failure_set_variable_fresh
        indexId sequenceId <| by
          simp [indexId, sequenceId])
      (fs_zfc_fo_failure_set_variable_fresh
        indexId payloadId <| by
          simp [indexId, payloadId])
      hTraceFreshContext hPair hSequence hDomain hLength
  generalize hPayload :
      nat_sequence_decode (godel_unpair_value raw).2 = payload
    at hCheck
  cases payload with
  | nil =>
      exact hLengthFalsum (by simp [hPayload])
  | cons leftId rest =>
      cases rest with
      | nil =>
          exact hLengthFalsum (by simp [hPayload])
      | cons rightId rest =>
          cases rest with
          | nil =>
              exact hLengthFalsum (by simp [hPayload])
          | cons bodyCode rest =>
              cases rest with
              | cons extra more =>
                  exact hLengthFalsum (by simp [hPayload])
              | nil =>
                  have hFreshVariable
                      (id offset : Nat) (hUpper : id ≤ 470) :
                      (SetSort.set, id) ∉
                        Term.freeSupport (x#(base + offset)) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      id (base + offset) <| by
                        apply Nat.ne_of_lt
                        exact Nat.lt_of_le_of_lt hUpper <|
                          Nat.lt_of_lt_of_le
                            (by decide : 470 < 700) <|
                              Nat.le_trans hBaseLower
                                (Nat.le_add_right base offset)
                  have hTraceFreshSequence :
                      (SetSort.set, traceId) ∉
                        Term.freeSupport (x#sequenceId) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      traceId sequenceId <| by
                        simp [traceId, sequenceId]
                  have hIndexFreshSequence :
                      (SetSort.set, indexId) ∉
                        Term.freeSupport (x#sequenceId) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      indexId sequenceId <| by
                        simp [indexId, sequenceId]
                  have hIndexFreshPayload :
                      (SetSort.set, indexId) ∉
                        Term.freeSupport (x#payloadId) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      indexId payloadId <| by
                        simp [indexId, payloadId]
                  have hTraceFreshBodyCode :
                      (SetSort.set, traceId) ∉
                        Term.freeSupport (x#bodyId) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      traceId bodyId <| by
                        simp [traceId, bodyId]
                  have hIndexFreshBodyCode :
                      (SetSort.set, indexId) ∉
                        Term.freeSupport (x#bodyId) :=
                    fs_zfc_fo_failure_set_variable_fresh
                      indexId bodyId <| by
                        simp [indexId, bodyId]
                  have hIndexFreshBodyNumeric :
                      (SetSort.set, indexId) ∉
                        Term.freeSupport
                          (x#sequenceId ·ₘ numₘ(2)) :=
                    fs_zfc_fo_failure_application_numeral_fresh
                      indexId sequenceId 2 <| by
                        simp [indexId, sequenceId]
                  generalize hBodyDecode :
                      fs_named_formula_token_code_decode
                          freeBase bodyCode =
                        bodyOption at hCheck
                  cases bodyOption with
                  | none =>
                      exact
                        fs_zfc_support_raw_logical_payload_component_falsum
                          raw 10 freeBase 2
                          (x#payloadId) (x#sequenceId)
                          (x#bodyId)
                          (x#sequenceId ·ₘ numₘ(2))
                          traceId indexId
                          (set_variable_admissible payloadId)
                          (set_variable_admissible sequenceId)
                          (set_variable_admissible bodyId)
                          (by prove_term_admissible)
                          hTraceIndex hTraceFreshSequence
                          hIndexFreshSequence hIndexFreshPayload
                          hTraceFreshBodyCode hIndexFreshBodyCode
                          hIndexFreshBodyNumeric hTraceFreshContext
                          hPair hSequence
                          (FirstOrder.Derives.eq_refl_m
                            (x#sequenceId ·ₘ numₘ(2)))
                          hComponent
                          (by simp [hPayload])
                          (by
                            simpa [hPayload] using hBodyDecode)
                  | some sourceFormula =>
                      let bodyTokens := nat_sequence_decode bodyCode
                      let leftTokens : List Nat :=
                        [Numbered.variable_token
                          (free_name leftId)]
                      let rightTokens : List Nat :=
                        [Numbered.variable_token
                          (free_name rightId)]
                      have hBodyStandard :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            x#bodyId ≐ₘ
                              standard_token_sequence bodyTokens := by
                        simpa [bodyTokens, hPayload] using
                          fs_zfc_support_raw_logical_payload_component_code_eq_standard
                            raw 10 2
                            (x#payloadId) (x#sequenceId)
                            (x#bodyId)
                            (x#sequenceId ·ₘ numₘ(2))
                            traceId indexId
                            (set_variable_admissible payloadId)
                            (set_variable_admissible sequenceId)
                            (set_variable_admissible bodyId)
                            (by prove_term_admissible)
                            hTraceIndex hTraceFreshSequence
                            hIndexFreshSequence hIndexFreshPayload
                            hTraceFreshBodyCode hIndexFreshBodyCode
                            hIndexFreshBodyNumeric hTraceFreshContext
                            hPair hSequence
                            (FirstOrder.Derives.eq_refl_m
                              (x#sequenceId ·ₘ numₘ(2)))
                            hComponent
                            (by simp [hPayload])
                      have hLeftNumeric :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            (x#sequenceId ·ₘ numₘ(0)) ≐ₘ
                              numₘ(leftId) := by
                        simpa [hPayload] using
                          fs_zfc_support_raw_logical_payload_component_numeric_eq
                            raw 10 0
                            (x#payloadId) (x#sequenceId)
                            (x#sequenceId ·ₘ numₘ(0))
                            traceId indexId
                            (set_variable_admissible payloadId)
                            (set_variable_admissible sequenceId)
                            hTraceIndex hTraceFreshSequence
                            hIndexFreshSequence hIndexFreshPayload
                            hTraceFreshContext hPair hSequence
                            (FirstOrder.Derives.eq_refl_m
                              (x#sequenceId ·ₘ numₘ(0)))
                            (by simp [hPayload])
                      have hRightNumeric :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            (x#sequenceId ·ₘ numₘ(1)) ≐ₘ
                              numₘ(rightId) := by
                        simpa [hPayload] using
                          fs_zfc_support_raw_logical_payload_component_numeric_eq
                            raw 10 1
                            (x#payloadId) (x#sequenceId)
                            (x#sequenceId ·ₘ numₘ(1))
                            traceId indexId
                            (set_variable_admissible payloadId)
                            (set_variable_admissible sequenceId)
                            hTraceIndex hTraceFreshSequence
                            hIndexFreshSequence hIndexFreshPayload
                            hTraceFreshContext hPair hSequence
                            (FirstOrder.Derives.eq_refl_m
                              (x#sequenceId ·ₘ numₘ(1)))
                            (by simp [hPayload])
                      have hVariableStandardOfNumeric
                          (index identifier : Nat)
                          (hNumeric :
                            Γ ⊢ₘ[fs_zfc_support_raw_theory]
                              (x#sequenceId ·ₘ numₘ(index)) ≐ₘ
                                numₘ(identifier)) :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            var_codeₘ(numₘ(2) *ₘ
                                (x#sequenceId ·ₘ numₘ(index))) ≐ₘ
                              standard_token_sequence
                                [Numbered.variable_token
                                  (free_name identifier)] := by
                        have hCongruence :
                            Γ ⊢ₘ[fs_zfc_support_raw_theory]
                              var_codeₘ(numₘ(2) *ₘ
                                  (x#sequenceId ·ₘ numₘ(index))) ≐ₘ
                                var_codeₘ(numₘ(2) *ₘ
                                  numₘ(identifier)) :=
                          Metatheory.Derives.unary_term_constructor_congr_of_equality
                            (fun term =>
                              var_codeₘ(numₘ(2) *ₘ term))
                            (fun term hTerm =>
                              variable_code_term_admissible _ <|
                                natural_multiplication_term_admissible
                                  (numₘ(2)) term
                                  (finite_numeral_term_admissible 2)
                                  hTerm)
                            (by
                              intros
                              simp [Term.substituteFree,
                                Term.substituteFree_eq_self_of_not_mem,
                                finite_numeral_term_freeSupport])
                            (x#sequenceId ·ₘ numₘ(index))
                            (numₘ(identifier))
                            (function_application_term_admissible
                              (x#sequenceId) (numₘ(index))
                              (set_variable_admissible sequenceId)
                              (finite_numeral_term_admissible index))
                            (finite_numeral_term_admissible identifier)
                            hNumeric
                        have hArithmetic :
                            Γ ⊢ₘ[fs_zfc_support_raw_theory]
                              var_codeₘ(numₘ(2) *ₘ
                                  numₘ(identifier)) ≐ₘ
                                var_codeₘ(numₘ(2 * identifier)) :=
                          FirstOrder.Derives.context_weaken
                            (Γ := []) (Δ := Γ) (by simp) <|
                              Metatheory.Derives.equality_symm
                                (fs_zfc_support_raw_variable_code_term_numeral_mul
                                  identifier)
                        have hNamed :
                            Γ ⊢ₘ[fs_zfc_support_raw_theory]
                              var_codeₘ(numₘ(2 * identifier)) ≐ₘ
                                standard_token_sequence
                                  [Numbered.variable_token
                                    (free_name identifier)] :=
                          FirstOrder.Derives.context_weaken
                            (Γ := []) (Δ := Γ) (by simp) <|
                              fs_zfc_support_raw_derives_of_godel_quotation <| by
                                simpa [
                                  Numbered.named_variable_code,
                                  free_name] using
                                  named_variable_code_eq_standard_token_sequence
                                    (free_name identifier)
                        exact Metatheory.Derives.equality_trans
                          hCongruence <|
                            Metatheory.Derives.equality_trans
                              hArithmetic hNamed
                      have hLeftStandard :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            leftVariable ≐ₘ
                              standard_token_sequence leftTokens := by
                        simpa [leftVariable, leftTokens] using
                          hVariableStandardOfNumeric
                            0 leftId hLeftNumeric
                      have hRightStandard :
                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                            rightVariable ≐ₘ
                              standard_token_sequence rightTokens := by
                        simpa [rightVariable, rightTokens] using
                          hVariableStandardOfNumeric
                            1 rightId hRightNumeric
                      have hPayloadValue :
                          nat_sequence_code_value
                              [leftId, rightId, bodyCode] =
                            (godel_unpair_value raw).2 := by
                        rw [← hPayload]
                        exact nat_sequence_code_value_decode _
                      have hLeftBound : leftId < freeBase := by
                        have hMember :
                            leftId <
                              nat_sequence_code_value
                                [leftId, rightId, bodyCode] :=
                          mem_lt_nat_sequence_code_value (by simp)
                        rw [hPayloadValue] at hMember
                        exact Nat.lt_of_le_of_lt
                          (Nat.le_trans
                            (Nat.le_of_lt hMember)
                            (godel_unpair_value_right_le raw))
                          hRawBound
                      have hBodyNamed :
                          fs_named_hilbert_tokens_decode_with_env
                              freeBase [] bodyTokens =
                            some sourceFormula := by
                        simpa [fs_named_formula_token_code_decode,
                          bodyTokens] using hBodyDecode
                      rcases
                          (fs_named_hilbert_tokens_decode_with_env_iff
                            freeBase [] bodyTokens sourceFormula).mp
                            hBodyNamed with
                        ⟨sourceTree, hSourceParse,
                          hSourceTreeDecode⟩
                      have hRightTermDecode :
                          fs_named_term_tokens_decode_with_env
                              freeBase [] rightTokens =
                            some
                              (Term.var
                                (.fvar SetSort.set rightId)) := by
                        simpa [rightTokens,
                          fs_named_variable_of_name, free_name] using
                          fs_named_term_tokens_decode_with_env_variable
                            freeBase [] (free_name rightId)
                      rcases
                          (fs_named_term_tokens_decode_with_env_iff
                            freeBase [] rightTokens
                            (Term.var
                              (.fvar SetSort.set rightId))).mp
                            hRightTermDecode with
                        ⟨replacementTree, hReplacementParse,
                          hReplacementTreeDecode⟩
                      by_cases hNotBound :
                          fs_named_hilbert_tree_target_not_bound
                            (Numbered.variable_token
                              (free_name leftId))
                            sourceTree
                      · by_cases hSafe :
                            fs_named_hilbert_tree_substitution_safe
                              (Numbered.variable_token
                                (free_name leftId))
                              replacementTree sourceTree
                        · let resultTokens :=
                            substitute_tokens bodyTokens
                              (Numbered.variable_token
                                (free_name leftId))
                              rightTokens
                          have hResultDecode :
                              fs_named_hilbert_tokens_decode_with_env
                                  freeBase [] resultTokens =
                                some
                                  (Formula.substituteFree
                                    SetSort.set leftId
                                    (Term.var
                                      (.fvar SetSort.set rightId))
                                    sourceFormula) := by
                            simpa [resultTokens] using
                              fs_named_hilbert_tokens_decode_with_env_substitute_free_of_trees
                                freeBase leftId
                                bodyTokens rightTokens
                                sourceTree replacementTree
                                sourceFormula
                                (Term.var
                                  (.fvar SetSort.set rightId))
                                hLeftBound hSourceParse
                                hReplacementParse hBodyNamed
                                hRightTermDecode
                                (TermWellSorted.fvar
                                  (σ := signature)
                                  SetSort.set rightId)
                                hNotBound hSafe
                          have hLeftTermDecode :
                              fs_named_term_tokens_decode_with_env
                                  freeBase [] leftTokens =
                                some
                                  (Term.var
                                    (.fvar SetSort.set leftId)) := by
                            simpa [leftTokens,
                              fs_named_variable_of_name, free_name] using
                              fs_named_term_tokens_decode_with_env_variable
                                freeBase [] (free_name leftId)
                          let equalityTokens :=
                            Numbered.equality_tokens
                              leftTokens rightTokens
                          let innerTokens :=
                            Numbered.implication_tokens
                              bodyTokens resultTokens
                          let expectedTokens :=
                            Numbered.implication_tokens
                              equalityTokens innerTokens
                          let candidate : SetFormula :=
                            Formula.imp
                              (Formula.equal
                                (Term.var
                                  (.fvar SetSort.set leftId))
                                (Term.var
                                  (.fvar SetSort.set rightId)))
                              (Formula.imp sourceFormula
                                (Formula.substituteFree
                                  SetSort.set leftId
                                  (Term.var
                                    (.fvar SetSort.set rightId))
                                  sourceFormula))
                          have hEqualityDecode :
                              fs_named_hilbert_tokens_decode_with_env
                                  freeBase [] equalityTokens =
                                some
                                  (Formula.equal
                                    (Term.var
                                      (.fvar SetSort.set leftId))
                                    (Term.var
                                      (.fvar SetSort.set rightId))) := by
                            simpa [equalityTokens] using
                              fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
                                freeBase []
                                hLeftTermDecode hRightTermDecode
                          have hExpectedDecode :
                              fs_named_hilbert_tokens_decode_with_env
                                  freeBase [] expectedTokens =
                                some candidate := by
                            exact
                              fs_named_hilbert_tokens_decode_with_env_implication
                                freeBase [] hEqualityDecode <|
                                  fs_named_hilbert_tokens_decode_with_env_implication
                                    freeBase [] hBodyNamed hResultDecode
                          have hFormulaCheck :
                              fs_formula_code_eq
                                  decoded.formula candidate =
                                false := by
                            simpa [candidate, hBodyDecode] using hCheck
                          have hCandidateDifferent :
                              candidate ≠ decoded.formula :=
                            Ne.symm <|
                              fs_formula_code_eq_ne_of_false
                                hFormulaCheck
                          have hRowNe :
                              row ≠ expectedTokens := by
                            intro hEqual
                            have hNamed :=
                              fs_formula_row_decode_named_of_some
                                hDecode
                            rw [hEqual] at hNamed
                            exact hCandidateDifferent <|
                              Option.some.inj
                                (hExpectedDecode.symm.trans hNamed)
                          have hBodyFormula :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                formula_codeₘ(x#bodyId) :=
                            FirstOrder.Derives.conjElimLeft <|
                              FirstOrder.Derives.conjElimLeft
                                hComponent
                          have hBodyMember :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                x#bodyId ∈ₘ FormulaCodeₘ :=
                            FirstOrder.Derives.iffElimRight
                              (FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Γ) (by simp) <|
                                  fs_zfc_support_raw_derives_of_godel_quotation <| by
                                    simpa [
                                      is_formula_code_definition_instance] using
                                      gq_formula_code_definition_instance
                                        (x#bodyId)
                                        (set_variable_admissible bodyId))
                              hBodyFormula
                          have hSourceUnion :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                x#bodyId ∈ₘ
                                  (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
                            FirstOrder.Derives.impElim
                              (FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Γ) (by simp) <|
                                  fs_zfc_support_raw_derives_of_godel_quotation <|
                                    gq_weaken_relation_plane <|
                                      mem_binary_union_right
                                        TermCodeₘ FormulaCodeₘ
                                        (x#bodyId)
                                        term_code_set_term_admissible
                                        formula_code_set_term_admissible
                                        (set_variable_admissible bodyId))
                              hBodyMember
                          have hSourceUnionStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                standard_token_sequence bodyTokens ∈ₘ
                                  (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
                            FirstOrder.Derives.iffElimRight
                              (membership_left_iff_of_equality
                                (x#bodyId)
                                (standard_token_sequence bodyTokens)
                                (TermCodeₘ ∪ₘ FormulaCodeₘ)
                                (set_variable_admissible bodyId)
                                (standard_token_sequence_admissible
                                  bodyTokens)
                                (binary_union_term_admissible
                                  TermCodeₘ FormulaCodeₘ
                                  term_code_set_term_admissible
                                  formula_code_set_term_admissible)
                                hBodyStandard)
                              hSourceUnion
                          have hStandardVariableMember
                              (identifier : Nat) :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                standard_token_sequence
                                    [Numbered.variable_token
                                      (free_name identifier)] ∈ₘ
                                  VarSymₘ := by
                            apply FirstOrder.Derives.context_weaken
                              (Γ := []) (Δ := Γ) (by simp)
                            apply
                              fs_zfc_support_raw_derives_of_godel_quotation
                            exact FirstOrder.Derives.iffElimRight
                              (membership_left_iff_of_equality
                                (Numbered.named_variable_code
                                  (free_name identifier))
                                (standard_token_sequence
                                  [Numbered.variable_token
                                    (free_name identifier)])
                                VarSymₘ
                                (variable_code_term_admissible
                                  (numₘ(free_name identifier))
                                  (finite_numeral_term_admissible
                                    (free_name identifier)))
                                (standard_token_sequence_admissible
                                  [Numbered.variable_token
                                    (free_name identifier)])
                                variable_symbol_set_term_admissible
                                (named_variable_code_eq_standard_token_sequence
                                  (free_name identifier)))
                              (named_variable_code_mem_variable_symbols
                                (free_name identifier))
                          have hLeftMember :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                leftVariable ∈ₘ VarSymₘ :=
                            FirstOrder.Derives.iffElimLeft
                              (membership_left_iff_of_equality
                                leftVariable
                                (standard_token_sequence leftTokens)
                                VarSymₘ
                                (by
                                  dsimp [leftVariable]
                                  prove_term_admissible)
                                (standard_token_sequence_admissible
                                  leftTokens)
                                variable_symbol_set_term_admissible
                                hLeftStandard)
                              (by
                                simpa [leftTokens] using
                                  hStandardVariableMember leftId)
                          have hRightTermCodeStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                term_codeₘ(
                                  standard_token_sequence rightTokens) :=
                            FirstOrder.Derives.context_weaken
                              (Γ := []) (Δ := Γ) (by simp) <|
                                fs_zfc_support_raw_derives_of_godel_quotation <| by
                                  simpa [rightTokens] using
                                    gq_standard_named_variable_is_term_code
                                      (free_name rightId)
                          have hRightTermMemberStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                standard_token_sequence rightTokens ∈ₘ
                                  TermCodeₘ :=
                            FirstOrder.Derives.iffElimRight
                              (FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Γ) (by simp) <|
                                  fs_zfc_support_raw_derives_of_godel_quotation <| by
                                    simpa [
                                      is_term_code_definition_instance] using
                                      gq_term_code_definition_instance
                                        (standard_token_sequence rightTokens)
                                        (standard_token_sequence_admissible
                                          rightTokens))
                              hRightTermCodeStandard
                          have hRightTermMember :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                rightVariable ∈ₘ TermCodeₘ :=
                            FirstOrder.Derives.iffElimLeft
                              (membership_left_iff_of_equality
                                rightVariable
                                (standard_token_sequence rightTokens)
                                TermCodeₘ
                                (by
                                  dsimp [rightVariable]
                                  prove_term_admissible)
                                (standard_token_sequence_admissible
                                  rightTokens)
                                term_code_set_term_admissible
                                hRightStandard)
                              hRightTermMemberStandard
                          have hRightTermCode :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                term_codeₘ(rightVariable) :=
                            FirstOrder.Derives.iffElimLeft
                              (FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Γ) (by simp) <|
                                  fs_zfc_support_raw_derives_of_godel_quotation <| by
                                    simpa [
                                      is_term_code_definition_instance] using
                                      gq_term_code_definition_instance
                                        rightVariable
                                        (by
                                          dsimp [rightVariable]
                                          prove_term_admissible))
                              hRightTermMember
                          have hPrecondition :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                code_substitution_precondition
                                  (x#bodyId)
                                  leftVariable rightVariable := by
                            simpa [code_substitution_precondition] using
                              FirstOrder.Derives.conjIntro
                                (FirstOrder.Derives.conjIntro
                                  hSourceUnion hLeftMember)
                                hRightTermCode
                          have hStandardPrecondition :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                code_substitution_precondition
                                  (standard_token_sequence bodyTokens)
                                  (standard_token_sequence leftTokens)
                                  (standard_token_sequence rightTokens) := by
                            simpa [code_substitution_precondition,
                              leftTokens] using
                              FirstOrder.Derives.conjIntro
                                (FirstOrder.Derives.conjIntro
                                  hSourceUnionStandard
                                  (hStandardVariableMember leftId))
                                hRightTermCodeStandard
                          have hReservedUpper
                              (id : FreeVarId)
                              (hId : id ∈ [310, 311]) :
                              id ≤ 470 := by
                            simp only [List.mem_cons,
                              List.not_mem_nil, or_false] at hId
                            rcases hId with rfl | rfl <;> decide
                          have hObjectFresh :
                              ReservedIdsFresh [310, 311]
                                [x#bodyId, leftVariable,
                                  rightVariable, x#resultId] := by
                            intro value hValue id hId
                            simp only [List.mem_cons,
                              List.not_mem_nil, or_false] at hValue
                            rcases hValue with rfl | rfl | rfl | rfl
                            · exact hFreshVariable
                                id 60 (hReservedUpper id hId)
                            · simpa [leftVariable,
                                Term.freeSupport, Term.freeSupportList,
                                finite_numeral_term_freeSupport] using
                                hFreshVariable
                                  id 59 (hReservedUpper id hId)
                            · simpa [rightVariable,
                                Term.freeSupport, Term.freeSupportList,
                                finite_numeral_term_freeSupport] using
                                hFreshVariable
                                  id 59 (hReservedUpper id hId)
                            · exact hFreshVariable
                                id 61 (hReservedUpper id hId)
                          have hResultStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                x#resultId ≐ₘ
                                  standard_token_sequence
                                    resultTokens := by
                            simpa [resultTokens, leftTokens] using
                              fs_zfc_support_raw_logical_substitution_result_eq_standard
                                (x#bodyId)
                                leftVariable rightVariable
                                (x#resultId)
                                bodyTokens rightTokens
                                (Numbered.variable_token
                                  (free_name leftId))
                                (set_variable_admissible bodyId)
                                (by
                                  dsimp [leftVariable]
                                  prove_term_admissible)
                                (by
                                  dsimp [rightVariable]
                                  prove_term_admissible)
                                (set_variable_admissible resultId)
                                hObjectFresh hPrecondition
                                hStandardPrecondition hSubstitution
                                hBodyStandard hLeftStandard
                                hRightStandard
                          have hEqualityStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                eq_codeₘ(
                                    leftVariable,
                                    rightVariable) ≐ₘ
                                  standard_token_sequence
                                    equalityTokens := by
                            simpa [equalityTokens,
                              leftTokens, rightTokens] using
                              fs_zfc_support_raw_equality_code_eq_standard_variables
                                leftId rightId
                                leftVariable rightVariable
                                (by
                                  dsimp [leftVariable]
                                  prove_term_check)
                                (by
                                  dsimp [rightVariable]
                                  prove_term_check)
                                hLeftStandard hRightStandard
                          have hInnerStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                imp_codeₘ(x#bodyId, x#resultId) ≐ₘ
                                  standard_token_sequence
                                    innerTokens := by
                            simpa [innerTokens] using
                              fs_zfc_support_raw_implication_code_eq_standard
                                bodyTokens resultTokens
                                (x#bodyId) (x#resultId)
                                (by prove_term_check)
                                (by prove_term_check)
                                hBodyStandard hResultStandard
                          have hWholeStandard :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                imp_codeₘ(
                                    eq_codeₘ(
                                      leftVariable,
                                      rightVariable),
                                    imp_codeₘ(
                                      x#bodyId, x#resultId)) ≐ₘ
                                  standard_token_sequence
                                    expectedTokens := by
                            simpa [expectedTokens] using
                              fs_zfc_support_raw_implication_code_eq_standard
                                equalityTokens innerTokens
                                (eq_codeₘ(
                                  leftVariable, rightVariable))
                                (imp_codeₘ(
                                  x#bodyId, x#resultId))
                                (by prove_term_check)
                                (by prove_term_check)
                                hEqualityStandard hInnerStandard
                          have hRowEquality :
                              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                standard_token_sequence row ≐ₘ
                                  standard_token_sequence
                                    expectedTokens :=
                            Metatheory.Derives.equality_trans
                              hFormulaField hWholeStandard
                          exact FirstOrder.Derives.negElim
                            hRowEquality <|
                              FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Γ) (by simp) <|
                                  fs_zfc_support_raw_derives_of_standard_sequence <|
                                    standard_token_sequence_ne hRowNe
                        · exact
                            fs_zfc_support_raw_logical_substitution_capture_unsafe_elim
                              (Γ := Γ) (Δ := Γ)
                              freeBase leftId bodyTokens rightTokens
                              sourceTree replacementTree sourceFormula
                              (Term.var
                                (.fvar SetSort.set rightId))
                              leftVariable rightVariable (x#bodyId)
                              (by
                                dsimp [leftVariable]
                                prove_term_admissible)
                              (by
                                dsimp [rightVariable]
                                prove_term_admissible)
                              (set_variable_admissible bodyId)
                              (fun id hUpper => by
                                simpa [leftVariable,
                                  Term.freeSupport, Term.freeSupportList,
                                  finite_numeral_term_freeSupport] using
                                  hFreshVariable id 59 hUpper)
                              (fun id hUpper => by
                                simpa [rightVariable,
                                  Term.freeSupport, Term.freeSupportList,
                                  finite_numeral_term_freeSupport] using
                                  hFreshVariable id 59 hUpper)
                              (fun id hUpper =>
                                hFreshVariable id 60 hUpper)
                              (fun _ h => h)
                              hSafe hSourceParse hSourceTreeDecode
                              hReplacementParse hReplacementTreeDecode
                              hLeftStandard hBodyStandard hRightStandard
                              hNoQuantifier hSubstitutable
                      · exact
                          fs_zfc_support_raw_logical_substitution_target_bound_elim
                            (Γ := Γ) (Δ := Γ)
                            freeBase leftId bodyTokens sourceTree
                            sourceFormula leftVariable (x#bodyId)
                            (by
                              dsimp [leftVariable]
                              prove_term_admissible)
                            (set_variable_admissible bodyId)
                            (fun id hUpper => by
                              simpa [leftVariable,
                                Term.freeSupport, Term.freeSupportList,
                                finite_numeral_term_freeSupport] using
                                hFreshVariable id 59 hUpper)
                            (fun id hUpper =>
                              hFreshVariable id 60 hUpper)
                            (fun _ h => h)
                            hNotBound hSourceParse hSourceTreeDecode
                            hLeftStandard hBodyStandard hNoQuantifier

end FormalSystem.CertifiedProof

end YesMetaZFC.Logic.FirstOrder
