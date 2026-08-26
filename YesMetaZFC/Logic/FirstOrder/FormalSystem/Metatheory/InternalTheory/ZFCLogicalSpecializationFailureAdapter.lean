import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaAtomicShiftInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalSpecializationCaptureFailureAdapter

namespace YesMetaZFC.Logic.FirstOrder

open Nonlogical.BasicSetTheory
open FormalSystem
open FormalSystem.Rosser
open FormalSystem.GodelQuotation
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

/--
若同一载荷在宿主侧解码为反身等式，且两侧项由同一 token 序列解码，
则载荷的项提取器恢复该项。
-/
theorem fs_term_carrier_decode_of_reflexive_equality_tokens
    (freeBase : Nat)
    (termTokens tokens : List Nat)
    (carrier : SetFormula)
    (term : SetTerm)
    (hTokens : tokens = Numbered.equality_tokens termTokens termTokens)
    (hCarrier :
      fs_named_hilbert_tokens_decode_with_env freeBase [] tokens = some carrier)
    (hTerm :
      fs_named_term_tokens_decode_with_env freeBase [] termTokens = some term) :
    fs_term_carrier_decode carrier = some term := by
  have hEquality :
      fs_named_hilbert_tokens_decode_with_env freeBase [] tokens =
        some (.equal term term) := by
    rw [hTokens]
    exact
      fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
        freeBase [] hTerm hTerm
  have hCarrierShape : carrier = .equal term term :=
    Option.some.inj (hCarrier.symm.trans hEquality)
  subst carrier
  simp [fs_term_carrier_decode, fs_term_code_eq]

/-!
该包装只把三段码的 GQ 构造定理接到 raw theory。
它消费已经得到的三个对象等式，不引入新的序列反演接口。
-/
private theorem fs_zfc_support_raw_bracketed_three_part_eq_standard_token_sequence
    {Γ : Context signature}
    (firstTokens middleTokens lastTokens : List Nat)
    (first middle last : SetTerm)
    (hFirst :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        first ≐ₘ standard_token_sequence firstTokens)
    (hMiddle :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        middle ≐ₘ standard_token_sequence middleTokens)
    (hLast :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        last ≐ₘ standard_token_sequence lastTokens)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      binary_atomic_formula_code_term middle first last ≐ₘ
        standard_token_sequence
          ([Numbered.logical_token .leftParenthesis] ++
            firstTokens ++ middleTokens ++ lastTokens ++
              [Numbered.logical_token .rightParenthesis]) := by
  let premises : Context signature := [
    first ≐ₘ standard_token_sequence firstTokens,
    middle ≐ₘ standard_token_sequence middleTokens,
    last ≐ₘ standard_token_sequence lastTokens]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        binary_atomic_formula_code_term middle first last ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token .leftParenthesis] ++
              firstTokens ++ middleTokens ++ lastTokens ++
                [Numbered.logical_token .rightParenthesis]) :=
    gq_bracketed_three_part_eq_standard_token_sequence_of_context
      firstTokens middleTokens lastTokens
      first middle last
      (FirstOrder.Derives.assumption (by simp [premises]))
      (FirstOrder.Derives.assumption (by simp [premises]))
      (FirstOrder.Derives.assumption (by simp [premises]))
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  apply FirstOrder.Derives.multi_cut
    (T := fs_zfc_support_raw_theory)
    (premises := premises)
  · intro formula hFormula
    simp [premises] at hFormula
    rcases hFormula with rfl | rfl | rfl
    · exact hFirst
    · exact hMiddle
    · exact hLast
  · exact
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        hGQ).context_weaken_append

namespace FormalSystem.CertifiedProof

/--
同一源码、变量与替换项下，对象代换规格唯一决定标准 token 结果。

该接口只组合既有 substitution 函数性与标准序列规格，避免各逻辑分支重复展开
`subst_codeₘ` 的函数项运输。
-/
theorem fs_zfc_support_raw_code_substitution_standard_unique_imp
    (sourceTokens replacementTokens : List Nat)
    (eigen : Nat)
    (sourceCode variableCode replacementCode resultCode : SetTerm)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hVariable : Term.CheckCertificate variableCode SetSort.set)
    (hReplacement : Term.CheckCertificate replacementCode SetSort.set)
    (hResult : Term.CheckCertificate resultCode SetSort.set)
    (hFresh :
      ReservedIdsFresh [310, 311]
        [sourceCode, variableCode, replacementCode, resultCode]) :
    Derives fs_zfc_support_raw_theory [] (
      formula_codeₘ(sourceCode) ⟶ₘ
        term_codeₘ(replacementCode) ⟶ₘ
          sourceCode ≐ₘ standard_token_sequence sourceTokens ⟶ₘ
            variableCode ≐ₘ standard_token_sequence
                [Numbered.variable_token (free_name eigen)] ⟶ₘ
              replacementCode ≐ₘ
                  standard_token_sequence replacementTokens ⟶ₘ
                code_substitution_spec
                    sourceCode variableCode replacementCode resultCode ⟶ₘ
                  resultCode ≐ₘ standard_token_sequence
                    (substitute_tokens sourceTokens
                      (Numbered.variable_token (free_name eigen))
                      replacementTokens)) := by
  repeat'
    apply FirstOrder.Derives.impIntro
      (hAntecedentCheck := by prove_nd_formula_check)
  let resultTokens :=
    substitute_tokens sourceTokens
      (Numbered.variable_token (free_name eigen))
      replacementTokens
  let standardSource := standard_token_sequence sourceTokens
  let standardVariable :=
    standard_token_sequence
      [Numbered.variable_token (free_name eigen)]
  let standardReplacement :=
    standard_token_sequence replacementTokens
  let standardResult := standard_token_sequence resultTokens
  let sourceFormula : SetFormula := formula_codeₘ(sourceCode)
  let replacementFormula : SetFormula := term_codeₘ(replacementCode)
  let sourceEquality : SetFormula := sourceCode ≐ₘ standardSource
  let variableEquality : SetFormula := variableCode ≐ₘ standardVariable
  let replacementEquality : SetFormula :=
    replacementCode ≐ₘ standardReplacement
  let specification : SetFormula :=
    code_substitution_spec
      sourceCode variableCode replacementCode resultCode
  let Γ : Context signature := [
    specification, replacementEquality, variableEquality,
    sourceEquality, replacementFormula, sourceFormula]
  have hSourceFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] sourceFormula :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hReplacementFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] replacementFormula :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] sourceEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hVariableEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] variableEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hReplacementEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] replacementEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] specification :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSourceMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] sourceCode ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_formula_code_definition_instance
              sourceCode hSource.admissible)
      (by simpa [sourceFormula] using hSourceFormula)
  have hSourceUnion :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_relation_plane <|
              mem_binary_union_right
                TermCodeₘ FormulaCodeₘ sourceCode
                term_code_set_term_admissible
                formula_code_set_term_admissible
                hSource.admissible)
      hSourceMember
  have hStandardVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardVariable ∈ₘ VarSymₘ := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply fs_zfc_support_raw_derives_of_godel_quotation
    exact FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        (Numbered.named_variable_code (free_name eigen))
        standardVariable VarSymₘ
        (variable_code_term_admissible _
          (finite_numeral_term_admissible _))
        (standard_token_sequence_admissible _)
        variable_symbol_set_term_admissible
        (by
          simpa [standardVariable] using
            named_variable_code_eq_standard_token_sequence
              (free_name eigen)))
      (named_variable_code_mem_variable_symbols
        (free_name eigen))
  have hVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] variableCode ∈ₘ VarSymₘ :=
    FirstOrder.Derives.iffElimLeft
      (membership_left_iff_of_equality
        variableCode standardVariable VarSymₘ
        hVariable.admissible
        (standard_token_sequence_admissible _)
        variable_symbol_set_term_admissible
        (by simpa [variableEquality] using hVariableEquality))
      hStandardVariableMember
  have hPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
          sourceCode variableCode replacementCode :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro hSourceUnion hVariableMember)
      (by simpa [replacementFormula] using hReplacementFormula)
  have hStandardSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          standardSource standardVariable standardReplacement
          standardResult := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply fs_zfc_support_raw_derives_of_godel_quotation
    simpa [standardSource, standardVariable, standardReplacement,
      standardResult, resultTokens] using
        gq_weaken_standard_sequence <|
          standard_token_sequence_code_substitution_spec
            sourceTokens
            (Numbered.variable_token (free_name eigen))
            replacementTokens
  have hStandardSourceUnion :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardSource ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        sourceCode standardSource (TermCodeₘ ∪ₘ FormulaCodeₘ)
        hSource.admissible (standard_token_sequence_admissible _)
        (binary_union_term_admissible
          TermCodeₘ FormulaCodeₘ
          term_code_set_term_admissible
          formula_code_set_term_admissible)
        (by simpa [sourceEquality] using hSourceEquality))
      hSourceUnion
  have hReplacementMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] replacementCode ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_term_code_definition_instance
              replacementCode hReplacement.admissible)
      (by simpa [replacementFormula] using hReplacementFormula)
  have hStandardReplacementMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] standardReplacement ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        replacementCode standardReplacement TermCodeₘ
        hReplacement.admissible (standard_token_sequence_admissible _)
        term_code_set_term_admissible
        (by simpa [replacementEquality] using hReplacementEquality))
      hReplacementMember
  have hStandardReplacementFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(standardReplacement) :=
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_term_code_definition_instance
              standardReplacement
              (standard_token_sequence_admissible _))
      hStandardReplacementMember
  have hStandardPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
          standardSource standardVariable standardReplacement :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hStandardSourceUnion hStandardVariableMember)
      hStandardReplacementFormula
  have hStandardFresh :
      ReservedIdsFresh [310, 311]
        [standardSource, standardVariable,
          standardReplacement, standardResult] := by
    repeat' apply reserved_ids_fresh_cons_closed
    · exact standard_token_sequence_freeSupport_nil _
    · exact standard_token_sequence_freeSupport_nil _
    · exact standard_token_sequence_freeSupport_nil _
    · exact standard_token_sequence_freeSupport_nil _
    · exact reserved_ids_fresh_nil _
  have hObjectResult :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        resultCode ≐ₘ
          subst_codeₘ(sourceCode, variableCode, replacementCode) := by
    have hFunctional :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_substitution_variable <|
              code_substitution_spec_implies_eq_term
                sourceCode variableCode replacementCode resultCode
                hSource hVariable hReplacement hResult hFresh
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim hFunctional hPrecondition)
      (by simpa [specification] using hSpecification)
  have hStandardResult :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardResult ≐ₘ
          subst_codeₘ(standardSource, standardVariable,
            standardReplacement) := by
    have hFunctional :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_substitution_variable <|
              code_substitution_spec_implies_eq_term
                standardSource standardVariable standardReplacement
                standardResult
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible _)
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible _)
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible _)
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible _)
                hStandardFresh
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim hFunctional hStandardPrecondition)
      hStandardSpecification
  have hInputCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        subst_codeₘ(sourceCode, variableCode, replacementCode) ≐ₘ
          subst_codeₘ(standardSource, standardVariable,
            standardReplacement) :=
    Metatheory.Derives.ternary_term_constructor_congr_of_equalities
      code_substitution_term code_substitution_term_admissible
      (by
        intros
        simp [code_substitution_term, Term.substituteFree])
      sourceCode standardSource variableCode standardVariable
      replacementCode standardReplacement
      hSource.admissible (standard_token_sequence_admissible _)
      hVariable.admissible (standard_token_sequence_admissible _)
      hReplacement.admissible (standard_token_sequence_admissible _)
      (by simpa [sourceEquality] using hSourceEquality)
      (by simpa [variableEquality] using hVariableEquality)
      (by simpa [replacementEquality] using hReplacementEquality)
  simpa [standardResult, resultTokens] using
    Metatheory.Derives.equality_trans hObjectResult <|
      Metatheory.Derives.equality_trans hInputCongruence <|
        Metatheory.Derives.equality_symm hStandardResult

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/--
逻辑公理 tag 7 的宿主检查失败，内部化为对象层特化证书条件的否定。
该定理只消费二元检查器的失败视图，不向 Rosser 终局泄露 replay 细节。
-/
theorem fs_zfc_support_raw_logical_specialization_neg_of_check_false
    (raw freeBase : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hTag : (ProofCode.godel_unpair_value raw).fst = 7)
    (hDecode : fs_formula_row_decode freeBase row = some decoded)
    (hCheck : fs_logical_base_axiom_check freeBase decoded.formula raw = false) :
    ⊢ₘ[fs_zfc_support_raw_theory]
      ¬ₘ logical_specialization_certificate_condition_with_ids
        (standard_token_sequence row)
        (finite_numeral_term raw)
        (base + 27) (base + 28) (base + 29) (base + 30)
        (base + 31) (base + 32) (base + 33) (base + 34)
        (base + 35) (base + 36) (base + 40) (base + 41) := by
  simp [fs_logical_base_axiom_check, fs_logical_base_axiom_check_with, hTag] at hCheck
  unfold logical_specialization_certificate_condition_with_ids
  apply fs_zfc_support_raw_exists_assignments_neg
    (assignments := [
      (base + 27, set_variable (base + 27)),
      (base + 28, set_variable (base + 28)),
      (base + 29, set_variable (base + 29)),
      (base + 30, set_variable (base + 30)),
      (base + 31, set_variable (base + 31)),
      (base + 32, set_variable (base + 32)),
      (base + 33, set_variable (base + 33)),
      (base + 34, set_variable (base + 34)),
      (base + 35, set_variable (base + 35)),
      (base + 36, set_variable (base + 36))])
  let assignments : List (FreeVarId × SetTerm) := [
    (base + 27, set_variable (base + 27)),
    (base + 28, set_variable (base + 28)),
    (base + 29, set_variable (base + 29)),
    (base + 30, set_variable (base + 30)),
    (base + 31, set_variable (base + 31)),
    (base + 32, set_variable (base + 32)),
    (base + 33, set_variable (base + 33)),
    (base + 34, set_variable (base + 34)),
    (base + 35, set_variable (base + 35)),
    (base + 36, set_variable (base + 36))]
  let allFields : List SetFormula := [
    numₘ(raw) ≐ₘ
      godel_pairing_term (ordered_pair_term numₘ(7) (set_variable (base + 27))),
    set_variable (base + 27) ≐ₘ
      godel_pairing_term
        (ordered_pair_term (set_variable (base + 28))
          (godel_pairing_term
            (ordered_pair_term (set_variable (base + 29)) (set_variable (base + 30))))),
    membership_formula (set_variable (base + 28)) omega_term,
    logical_formula_payload_component_condition_with_ids
      (set_variable (base + 31)) (set_variable (base + 29)) (base + 40) (base + 41),
    logical_formula_payload_component_condition_with_ids
      (set_variable (base + 32)) (set_variable (base + 30)) (base + 40) (base + 41),
    is_term_code_formula (set_variable (base + 33)),
    set_variable (base + 32) ≐ₘ
      equality_formula_code_term (set_variable (base + 33)) (set_variable (base + 33)),
    set_variable (base + 34) ≐ₘ
      variable_code_term (natural_multiplication_term numₘ(2) (set_variable (base + 28))),
    ¬ₘ quantifier_occurs_condition (set_variable (base + 34)) (set_variable (base + 31)),
    substitutableₘ(
      set_variable (base + 34), set_variable (base + 33), set_variable (base + 31)),
    canonical_forall_closure_code_condition
      (set_variable (base + 31)) (set_variable (base + 34)) (set_variable (base + 35)),
    code_substitution_spec
      (set_variable (base + 31)) (set_variable (base + 34))
      (set_variable (base + 33)) (set_variable (base + 36)),
    standard_token_sequence row ≐ₘ
      specialization_axiom_code_term (set_variable (base + 35)) (set_variable (base + 36))]
  let A : SetFormula := logical_certificate_conjunction allFields
  let Γ : Context _ := [A]
  have hFormulaCheck :
      Term.CheckCertificate (standard_token_sequence row) SetSort.set := by
    prove_term_check
  have hCertificateCheck :
      Term.CheckCertificate (finite_numeral_term raw) SetSort.set := by
    prove_term_check
  have hConditionAdmissible :=
    logical_specialization_certificate_condition_with_ids_admissible
      (standard_token_sequence row) (finite_numeral_term raw)
      (base + 27) (base + 28) (base + 29) (base + 30)
      (base + 31) (base + 32) (base + 33) (base + 34)
      (base + 35) (base + 36) (base + 40) (base + 41)
      hFormulaCheck.admissible hCertificateCheck.admissible
  have hA : A.CheckCertificate := by
    apply Formula.CheckCertificate.iff_admissible.mpr
    apply fs_zfc_admissible_body_of_exists_assignments assignments A
    unfold logical_specialization_certificate_condition_with_ids at hConditionAdmissible
    simpa [assignments, A, allFields] using hConditionAdmissible
  apply Derives.deduction (hAntecedentCheck := hA)
  have hWhole : Γ ⊢ₘ[fs_zfc_support_raw_theory] A :=
    Derives.assumption List.mem_cons_self hA
  have hFields : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_certificate_conjunction allFields := by
    simpa [A] using hWhole
  have hCertificatePair : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numₘ(raw) ≐ₘ
        godel_pairing_term (ordered_pair_term numₘ(7) (set_variable (base + 27))) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hPayloadPair : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      set_variable (base + 27) ≐ₘ
        godel_pairing_term
          (ordered_pair_term (set_variable (base + 28))
            (godel_pairing_term
              (ordered_pair_term (set_variable (base + 29)) (set_variable (base + 30))))) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hEigenNatural : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      membership_formula (set_variable (base + 28)) omega_term := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hBodyComponent : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_formula_payload_component_condition_with_ids
        (set_variable (base + 31)) (set_variable (base + 29)) (base + 40) (base + 41) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hCarrierComponent : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_formula_payload_component_condition_with_ids
        (set_variable (base + 32)) (set_variable (base + 30)) (base + 40) (base + 41) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hTermCode : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      is_term_code_formula (set_variable (base + 33)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hCarrierEquality : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      set_variable (base + 32) ≐ₘ
        equality_formula_code_term (set_variable (base + 33)) (set_variable (base + 33)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hVariableEquality : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      set_variable (base + 34) ≐ₘ
        variable_code_term
          (natural_multiplication_term numₘ(2) (set_variable (base + 28))) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hNoQuantifier : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ¬ₘ quantifier_occurs_condition (set_variable (base + 34)) (set_variable (base + 31)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hSubstitutable : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      substitutableₘ(
        set_variable (base + 34), set_variable (base + 33), set_variable (base + 31)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hUniversal : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_forall_closure_code_condition
        (set_variable (base + 31)) (set_variable (base + 34)) (set_variable (base + 35)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hSubstitution : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      code_substitution_spec
        (set_variable (base + 31)) (set_variable (base + 34))
        (set_variable (base + 33)) (set_variable (base + 36)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hFormulaEquality : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      standard_token_sequence row ≐ₘ
        specialization_axiom_code_term (set_variable (base + 35)) (set_variable (base + 36)) := by
    exact fs_zfc_fo_failure_conjunction_elim allFields _ (by simp [allFields]) hFields
  have hBodySequence : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      nat_sequence_code_condition_with_ids
        (set_variable (base + 31)) (set_variable (base + 29))
        (base + 40) (base + 41) := by
    unfold logical_formula_payload_component_condition_with_ids at hBodyComponent
    exact Derives.conj_elim_right hBodyComponent
  have hCarrierSequence : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      nat_sequence_code_condition_with_ids
        (set_variable (base + 32)) (set_variable (base + 30))
        (base + 40) (base + 41) := by
    unfold logical_formula_payload_component_condition_with_ids at hCarrierComponent
    exact Derives.conj_elim_right hCarrierComponent
  have hBodyNumericNatural : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      membership_formula (set_variable (base + 29)) omega_term := by
    unfold nat_sequence_code_condition_with_ids at hBodySequence
    exact Derives.conj_elim_right
      (Derives.conj_elim_left
        (Derives.conj_elim_left
          (Derives.conj_elim_left hBodySequence)))
  have hCarrierNumericNatural : Γ ⊢ₘ[fs_zfc_support_raw_theory]
      membership_formula (set_variable (base + 30)) omega_term := by
    unfold nat_sequence_code_condition_with_ids at hCarrierSequence
    exact Derives.conj_elim_right
      (Derives.conj_elim_left
        (Derives.conj_elim_left
          (Derives.conj_elim_left hCarrierSequence)))
  have hCoordinates :=
    fs_zfc_support_raw_nested_pair_coordinates
      raw 7
      (set_variable (base + 27))
      (set_variable (base + 28))
      (set_variable (base + 29))
      (set_variable (base + 30))
      (by prove_term_admissible)
      (by prove_term_admissible)
      (by prove_term_admissible)
      (by prove_term_admissible)
      hEigenNatural hBodyNumericNatural hCarrierNumericNatural
      hCertificatePair hPayloadPair
  rcases hCoordinates with ⟨hEigenEquality, hBodyNumericEquality, hCarrierNumericEquality⟩
  let bodyCode : Nat :=
    (ProofCode.godel_unpair_value
      (ProofCode.godel_unpair_value (ProofCode.godel_unpair_value raw).snd).snd).fst
  let carrierCode : Nat :=
    (ProofCode.godel_unpair_value
      (ProofCode.godel_unpair_value (ProofCode.godel_unpair_value raw).snd).snd).snd
  have hOffsetNe {m n : Nat} (h : m ≠ n) :
      base + m ≠ base + n := by
    intro hmn
    exact h (Nat.add_left_cancel hmn)
  have h40_27 : base + 40 ≠ base + 27 := hOffsetNe (by decide)
  have h40_28 : base + 40 ≠ base + 28 := hOffsetNe (by decide)
  have h40_29 : base + 40 ≠ base + 29 := hOffsetNe (by decide)
  have h40_30 : base + 40 ≠ base + 30 := hOffsetNe (by decide)
  have h40_31 : base + 40 ≠ base + 31 := hOffsetNe (by decide)
  have h40_32 : base + 40 ≠ base + 32 := hOffsetNe (by decide)
  have h40_33 : base + 40 ≠ base + 33 := hOffsetNe (by decide)
  have h40_34 : base + 40 ≠ base + 34 := hOffsetNe (by decide)
  have h40_35 : base + 40 ≠ base + 35 := hOffsetNe (by decide)
  have h40_36 : base + 40 ≠ base + 36 := hOffsetNe (by decide)
  have hExistsClose {id : FreeVarId} {φ : SetFormula}
      (hNe : base + 40 ≠ id)
      (hMem : (SetSort.set, base + 40) ∈ φ.freeSupport) :
      (SetSort.set, base + 40) ∈
        (∃ₘ[SetSort.set], Formula.closeFreeAt SetSort.set id 0 φ).freeSupport := by
    have hPairNe :
        (SetSort.set, base + 40) ≠ (SetSort.set, id) := by
      intro h
      exact hNe (congrArg Prod.snd h)
    simpa [Formula.freeSupport] using
      Formula.mem_freeSupport_closeFreeAt_of_mem_of_ne
        (SetSort.set, base + 40) SetSort.set id 0 φ hMem hPairNe
  have hTraceFreshContext :
      ∀ φ ∈ Γ, ¬(SetSort.set, base + 40) ∈ φ.freeSupport := by
    intro φ hφ hFree
    simp only [Γ, List.mem_singleton] at hφ
    subst φ
    have hConditionFree :
        (SetSort.set, base + 40) ∈
          (logical_specialization_certificate_condition_with_ids
            (standard_token_sequence row)
            (finite_numeral_term raw)
            (base + 27) (base + 28) (base + 29) (base + 30)
            (base + 31) (base + 32) (base + 33) (base + 34)
            (base + 35) (base + 36) (base + 40) (base + 41)).freeSupport := by
      unfold logical_specialization_certificate_condition_with_ids
      exact
        hExistsClose h40_27
          (hExistsClose h40_28
            (hExistsClose h40_29
              (hExistsClose h40_30
                (hExistsClose h40_31
                  (hExistsClose h40_32
                    (hExistsClose h40_33
                      (hExistsClose h40_34
                        (hExistsClose h40_35
                          (hExistsClose h40_36 (by simpa [A, allFields] using hFree))))))))))
    rcases
        logical_specialization_certificate_condition_with_ids_freeSupport_subset
          (standard_token_sequence row)
          (finite_numeral_term raw)
          (base + 27) (base + 28) (base + 29) (base + 30)
          (base + 31) (base + 32) (base + 33) (base + 34)
          (base + 35) (base + 36) (base + 40) (base + 41)
          (SetSort.set, base + 40) hConditionFree with hFormula | hCertificate
    · rw [standard_token_sequence_freeSupport_nil] at hFormula
      simp at hFormula
    · rw [finite_numeral_term_freeSupport] at hCertificate
      simp at hCertificate
  generalize hBodyDecode :
      fs_named_formula_token_code_decode freeBase bodyCode = bodyOption at hCheck
  cases bodyOption with
  | none =>
      apply
        fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
          (Γ := Γ)
          (componentCode := set_variable (base + 31))
          (numericCode := set_variable (base + 29))
          (freeBase := freeBase)
          (code := bodyCode)
          (traceId := base + 40)
          (indexId := base + 41)
          (hIds := hOffsetNe (by decide))
          (hComponentCode := by prove_term_admissible)
          (hNumericCode := by prove_term_admissible)
          (hTraceFreshSequence := by
            simp only [Term.freeSupport]
            intro h
            exact hOffsetNe (m := 40) (n := 31) (by decide)
              (congrArg Prod.snd (List.mem_singleton.mp h)))
          (hIndexFreshSequence := by
            simp only [Term.freeSupport]
            intro h
            exact hOffsetNe (m := 41) (n := 31) (by decide)
              (congrArg Prod.snd (List.mem_singleton.mp h)))
          (hIndexFreshCode := by
            simp only [Term.freeSupport]
            intro h
            exact hOffsetNe (m := 41) (n := 29) (by decide)
              (congrArg Prod.snd (List.mem_singleton.mp h)))
          (hTraceFreshContext := hTraceFreshContext)
          (hComponent := hBodyComponent)
          (hNumericEquality := by
            simpa [bodyCode] using hBodyNumericEquality)
          (hDecode := by
            simpa [fs_named_formula_token_code_decode, bodyCode] using hBodyDecode)
  | some body =>
      generalize hCarrierDecode :
          fs_named_formula_token_code_decode freeBase carrierCode = carrierOption at hCheck
      cases carrierOption with
      | none =>
          apply
            fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
              (Γ := Γ)
              (componentCode := set_variable (base + 32))
              (numericCode := set_variable (base + 30))
              (freeBase := freeBase)
              (code := carrierCode)
              (traceId := base + 40)
              (indexId := base + 41)
              (hIds := hOffsetNe (by decide))
              (hComponentCode := by prove_term_admissible)
              (hNumericCode := by prove_term_admissible)
              (hTraceFreshSequence := by
                simp only [Term.freeSupport]
                intro h
                exact hOffsetNe (m := 40) (n := 32) (by decide)
                  (congrArg Prod.snd (List.mem_singleton.mp h)))
              (hIndexFreshSequence := by
                simp only [Term.freeSupport]
                intro h
                exact hOffsetNe (m := 41) (n := 32) (by decide)
                  (congrArg Prod.snd (List.mem_singleton.mp h)))
              (hIndexFreshCode := by
                simp only [Term.freeSupport]
                intro h
                exact hOffsetNe (m := 41) (n := 30) (by decide)
                  (congrArg Prod.snd (List.mem_singleton.mp h)))
              (hTraceFreshContext := hTraceFreshContext)
              (hComponent := hCarrierComponent)
              (hNumericEquality := by
                simpa [carrierCode] using hCarrierNumericEquality)
              (hDecode := by
                simpa [fs_named_formula_token_code_decode, carrierCode] using hCarrierDecode)
      | some carrier =>
              generalize hTermDecode :
                  fs_term_carrier_decode carrier = termOption at hCheck
              let tokens : List Nat :=
                    ProofCode.nat_sequence_decode carrierCode
              exact show Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum from by
                  have hCarrierStandard :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        set_variable (base + 32) ≐ₘ
                          standard_token_sequence tokens :=
                    by
                      simpa [tokens] using
                        fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
                          (set_variable (base + 32))
                          (set_variable (base + 30))
                          carrierCode (base + 40) (base + 41)
                          (hOffsetNe (by decide))
                          (by prove_term_admissible)
                          (by prove_term_admissible)
                          (by
                            simp only [Term.freeSupport]
                            intro h
                            exact hOffsetNe (m := 40) (n := 32) (by decide)
                              (congrArg Prod.snd (List.mem_singleton.mp h)))
                          (by
                            simp only [Term.freeSupport]
                            intro h
                            exact hOffsetNe (m := 41) (n := 32) (by decide)
                              (congrArg Prod.snd (List.mem_singleton.mp h)))
                          (by
                            simp only [Term.freeSupport]
                            intro h
                            exact hOffsetNe (m := 41) (n := 30) (by decide)
                              (congrArg Prod.snd (List.mem_singleton.mp h)))
                          hTraceFreshContext hCarrierComponent
                          (by
                            simpa [carrierCode] using
                              hCarrierNumericEquality)
                  have hRawEquality :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        equality_formula_code_term
                            (set_variable (base + 33))
                            (set_variable (base + 33)) ≐ₘ
                          equality_atomic_formula_code_term
                            (set_variable (base + 33))
                            (set_variable (base + 33)) :=
                    fs_zfc_support_raw_equality_code_eq_raw_of_term_codes
                      (set_variable (base + 33))
                      (set_variable (base + 33))
                      (by prove_term_admissible)
                      (by prove_term_admissible)
                      hTermCode hTermCode
                  have hStandardEquality :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        standard_token_sequence tokens ≐ₘ
                          equality_atomic_formula_code_term
                            (set_variable (base + 33))
                            (set_variable (base + 33)) :=
                    Metatheory.Derives.equality_trans
                      (Metatheory.Derives.equality_symm
                        hCarrierStandard)
                      (Metatheory.Derives.equality_trans
                        hCarrierEquality hRawEquality)
                  have hFormulaFields :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        formula_codeₘ(set_variable (base + 32)) ∧ₘ
                          fs_formula_replay_condition
                            (set_variable (base + 32)) :=
                    FirstOrder.Derives.conjElimLeft hCarrierComponent
                  have hCarrierReplay :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        fs_formula_replay_condition
                          (set_variable (base + 32)) :=
                    FirstOrder.Derives.conjElimRight hFormulaFields
                  have hReplayTransport :=
                    fs_formula_replay_condition_iff_of_equality
                      (set_variable (base + 32))
                      (standard_token_sequence tokens)
                      (by prove_term_admissible)
                      (standard_token_sequence_admissible tokens)
                      hCarrierStandard
                  have hStandardReplay :
                      Γ ⊢ₘ[fs_zfc_support_raw_theory]
                        fs_formula_replay_condition
                          (standard_token_sequence tokens) :=
                    FirstOrder.Derives.iffElimRight
                      hReplayTransport hCarrierReplay
                  rcases fs_formula_tokens_or_bad_index tokens with
                    hTokens | ⟨tokenIndex, hTokenIndex, hToken⟩
                  · have hTermFinite :
                        Γ ⊢ₘ[fs_zfc_support_raw_theory]
                          finite_sequence_condition
                            (set_variable (base + 33)) :=
                      fs_zfc_support_raw_term_code_implies_finite_sequence
                        (set_variable (base + 33))
                        (by prove_term_admissible)
                        hTermCode
                    have hMiddle :
                        Γ ⊢ₘ[fs_zfc_support_raw_theory]
                          equality_symbol_code_term ≐ₘ
                            standard_token_sequence
                              [Numbered.logical_token .equality] :=
                      FirstOrder.Derives.context_weaken
                        (Γ := []) (Δ := Γ) (by simp) <|
                          fs_zfc_support_raw_derives_of_godel_quotation <|
                            logical_symbol_code_eq_standard_token_sequence
                              .equality
                    have hDomainMember :
                        Γ ⊢ₘ[fs_zfc_support_raw_theory]
                          domₘ(set_variable (base + 33)) ∈ₘ
                            domₘ(equality_atomic_formula_code_term
                              (set_variable (base + 33))
                              (set_variable (base + 33))) := by
                      simpa [equality_atomic_formula_code_term] using
                        fs_zfc_support_raw_bracketed_first_domain_mem
                          (set_variable (base + 33))
                          equality_symbol_code_term
                          (set_variable (base + 33))
                          (Term.check_certificate_of_admissible
                            (set_variable_admissible (base + 33)))
                          (Term.check_certificate_of_admissible
                            (logical_symbol_code_term_admissible .equality))
                          (Term.check_certificate_of_admissible
                            (set_variable_admissible (base + 33)))
                          hTermFinite
                          (FirstOrder.Derives.context_weaken
                            (Γ := []) (Δ := Γ) (by simp) <|
                              fs_zfc_support_raw_derives_of_godel_quotation <|
                                gq_finite_sequence_of_eq_standard_token_sequence
                                  equality_symbol_code_term
                                  [Numbered.logical_token .equality]
                                  (logical_symbol_code_eq_standard_token_sequence
                                    .equality)
                                  (hCode := by prove_term_check))
                          hTermFinite
                    refine fs_zfc_support_raw_domain_length_elim
                      (Γ := Γ)
                      (child := set_variable (base + 33))
                      (parent := equality_atomic_formula_code_term
                        (set_variable (base + 33))
                        (set_variable (base + 33)))
                      (tokens := tokens)
                      (conclusion := Formula.falsum)
                      (hChild := set_variable_admissible (base + 33))
                      (hParent := by prove_term_check)
                      (hConclusion := Formula.Admissible.falsum)
                      hDomainMember hStandardEquality ?_
                    intro n hn
                    let Δ : Context signature :=
                      (domₘ(set_variable (base + 33)) ≐ₘ numₘ(n)) :: Γ
                    have hWeaken :
                        ∀ φ, φ ∈ Γ → φ ∈ Δ := by
                      intro φ hφ
                      exact List.mem_cons_of_mem _ hφ
                    have hDomain :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          domₘ(set_variable (base + 33)) ≐ₘ numₘ(n) :=
                      FirstOrder.Derives.assumption (by simp [Δ])
                    have hFinite :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          finite_sequence_condition
                            (set_variable (base + 33)) :=
                      FirstOrder.Derives.context_weaken
                        (Γ := Γ) (Δ := Δ) hWeaken hTermFinite
                    have hMiddle' :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          equality_symbol_code_term ≐ₘ
                            standard_token_sequence
                              [Numbered.logical_token .equality] :=
                      FirstOrder.Derives.context_weaken
                        (Γ := Γ) (Δ := Δ) hWeaken hMiddle
                    have hEquality' :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          standard_token_sequence tokens ≐ₘ
                            equality_atomic_formula_code_term
                              (set_variable (base + 33))
                              (set_variable (base + 33)) :=
                      FirstOrder.Derives.context_weaken
                        (Γ := Γ) (Δ := Δ) hWeaken hStandardEquality
                    let leftTokens : List Nat :=
                      (tokens.drop 1).take n
                    let rightTokens : List Nat :=
                      (tokens.drop (n + 2)).take n
                    let expected : List Nat :=
                      Numbered.equality_tokens leftTokens rightTokens
                    have hParts :=
                      gq_bracketed_three_part_parts_eq_standard_slices_of_theory
                        (T := fs_zfc_support_raw_theory)
                        (fun formula hFormula =>
                          fs_zfc_support_raw_contains_godel_quotation
                            hFormula)
                        (set_variable (base + 33))
                        equality_symbol_code_term
                        (set_variable (base + 33))
                        tokens
                        (Numbered.logical_token .equality)
                        n n hFinite hMiddle' hFinite hDomain hDomain
                        (by
                          simpa [equality_atomic_formula_code_term] using
                            hEquality')
                        (hFirstCheck := by prove_term_check)
                        (hMiddleCheck := by prove_term_check)
                        (hLastCheck := by prove_term_check)
                    have hLeft :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          set_variable (base + 33) ≐ₘ
                            standard_token_sequence leftTokens := by
                      simpa [leftTokens] using
                        FirstOrder.Derives.conjElimLeft hParts
                    have hRight :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          set_variable (base + 33) ≐ₘ
                            standard_token_sequence rightTokens := by
                      simpa [rightTokens] using
                        FirstOrder.Derives.conjElimRight hParts
                    have hExpectedStandard :
                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                          equality_atomic_formula_code_term
                              (set_variable (base + 33))
                              (set_variable (base + 33)) ≐ₘ
                            standard_token_sequence expected := by
                      simpa [equality_atomic_formula_code_term,
                        expected, Numbered.equality_tokens] using
                        fs_zfc_support_raw_bracketed_three_part_eq_standard_token_sequence
                          leftTokens [Numbered.logical_token .equality]
                          rightTokens
                          (set_variable (base + 33))
                          equality_symbol_code_term
                          (set_variable (base + 33))
                          hLeft hMiddle' hRight
                          (hFirstCheck := by prove_term_check)
                          (hMiddleCheck := by prove_term_check)
                          (hLastCheck := by prove_term_check)
                    by_cases hShape : tokens = expected
                    · have hLeftTokens : FSFormulaTokens leftTokens := by
                        rw [hShape] at hTokens
                        intro token hToken
                        apply hTokens token
                        simp [expected, Numbered.equality_tokens, hToken]
                      have hCarrierAt :
                          fs_named_hilbert_tokens_decode_with_env
                              freeBase [] tokens =
                            some carrier := by
                        simpa [fs_named_formula_token_code_decode,
                          tokens] using hCarrierDecode
                      by_cases hTokenEquality :
                          leftTokens = rightTokens
                      · have hReflexiveShape :
                            tokens =
                              Numbered.equality_tokens
                                leftTokens leftTokens := by
                          simpa [expected, hTokenEquality] using hShape
                        cases hTerm :
                            fs_named_term_tokens_decode_with_env
                              freeBase [] leftTokens with
                        | none =>
                            have hReject :
                                ⊢ₘ[fs_zfc_support_raw_theory]
                                  ¬ₘ (standard_token_sequence leftTokens ∈ₘ
                                    TermCodeₘ) :=
                              fs_zfc_support_raw_derives_of_godel_quotation <|
                                gq_standard_term_code_not_of_decode_none
                                  freeBase [] leftTokens hLeftTokens hTerm
                            have hMember :
                                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                  standard_token_sequence leftTokens ∈ₘ
                                    TermCodeₘ :=
                              FirstOrder.Derives.iffElimRight
                                (membership_left_iff_of_equality
                                  (set_variable (base + 33))
                                  (standard_token_sequence leftTokens)
                                  TermCodeₘ
                                  (set_variable_admissible (base + 33))
                                  (standard_token_sequence_admissible leftTokens)
                                  term_code_set_term_admissible hLeft)
                                (FirstOrder.Derives.iffElimRight
                                  (FirstOrder.Derives.context_weaken
                                    (Γ := []) (Δ := Δ) (by simp) <|
                                      fs_zfc_support_raw_derives_of_godel_quotation <|
                                        gq_term_code_definition_instance
                                          (set_variable (base + 33))
                                          (set_variable_admissible (base + 33)))
                                  (FirstOrder.Derives.context_weaken
                                    (Γ := Γ) (Δ := Δ) hWeaken hTermCode))
                            exact FirstOrder.Derives.negElim hMember <|
                              FirstOrder.Derives.context_weaken
                                (Γ := []) (Δ := Δ) (by simp) hReject
                        | some decodedTerm =>
                            have hRecovered :=
                              fs_term_carrier_decode_of_reflexive_equality_tokens
                                freeBase leftTokens tokens carrier decodedTerm
                                hReflexiveShape
                                hCarrierAt hTerm
                            cases termOption with
                            | none =>
                                simp [hTermDecode] at hRecovered
                            | some term =>
                                rw [hTermDecode] at hRecovered
                                have hTermEquality :
                                    term = decodedTerm :=
                                  Option.some.inj hRecovered
                                subst decodedTerm
                                have hCarrierShape :
                                    carrier = term ≐ₘ term :=
                                  fs_term_carrier_decode_sound hTermDecode
                                subst carrier
                                simp only [hTermDecode] at hCheck
                                rcases
                                    (fs_named_term_tokens_decode_with_env_iff
                                      freeBase [] leftTokens term).mp hTerm with
                                  ⟨replacementTree, hReplacementParse,
                                    hReplacementTreeDecode⟩
                                have hReplacementListDecode :
                                    [replacementTree].mapM
                                        (fs_named_term_token_tree_decode
                                          freeBase []) =
                                      some [term] := by
                                  simp [hReplacementTreeDecode]
                                have hTermWellSorted :
                                    TermWellSorted term SetSort.set := by
                                  have hArguments :=
                                    fs_named_term_token_trees_decode_wellSorted
                                      freeBase [] hReplacementListDecode
                                  cases hArguments with
                                  | cons hWellSorted _ =>
                                      exact hWellSorted
                                have hTermScoped :
                                    TermScoped Scope.empty term := by
                                  simpa [Numbered.scope_of_names] using
                                    fs_named_term_token_trees_decode_scoped
                                      freeBase [] hReplacementListDecode
                                      term (by simp)
                                let eigen : Nat :=
                                  (ProofCode.godel_unpair_value
                                    (ProofCode.godel_unpair_value raw).snd).fst
                                have hEigenBound : eigen < freeBase := by
                                  have hRight :=
                                    ProofCode.godel_unpair_value_right_le raw
                                  have hLeft :=
                                    ProofCode.godel_unpair_value_left_le
                                      (ProofCode.godel_unpair_value raw).snd
                                  dsimp [eigen]
                                  omega
                                let bodyTokens : List Nat :=
                                  ProofCode.nat_sequence_decode bodyCode
                                have hBodyNamed :
                                    fs_named_hilbert_tokens_decode_with_env
                                        freeBase [] bodyTokens =
                                      some body := by
                                  simpa [fs_named_formula_token_code_decode,
                                    bodyTokens] using hBodyDecode
                                rcases
                                    (fs_named_hilbert_tokens_decode_with_env_iff
                                      freeBase [] bodyTokens body).mp hBodyNamed with
                                  ⟨sourceTree, hSourceParse,
                                    hSourceTreeDecode⟩
                                rcases
                                    fs_named_hilbert_tokens_decode_with_env_binder_close
                                      freeBase eigen [] bodyTokens body
                                      hEigenBound hBodyNamed with
                                  ⟨shiftedTokens, hShift,
                                    hClosedBodyDecode⟩
                                let closedTokens : List Nat :=
                                  Numbered.universal_tokens 1
                                    (substitute_tokens shiftedTokens
                                      (Numbered.variable_token
                                        (free_name eigen))
                                      [Numbered.variable_token
                                        (bound_name 0)])
                                have hClosedDecode :
                                    fs_named_hilbert_tokens_decode_with_env
                                        freeBase [] closedTokens =
                                      some
                                        (Formula.forallE SetSort.set
                                          (Formula.closeFreeAt SetSort.set
                                            eigen 0 body)) := by
                                  apply
                                    fs_named_hilbert_tokens_decode_with_env_universal
                                  simpa [closedTokens, bound_name] using
                                    hClosedBodyDecode
                                have hBodyStandardΓ :
                                    Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                      x#(base + 31) ≐ₘ
                                        standard_token_sequence
                                          bodyTokens := by
                                  simpa [bodyTokens] using
                                    fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
                                      (x#(base + 31))
                                      (x#(base + 29))
                                      bodyCode (base + 40) (base + 41)
                                      (hOffsetNe (by decide))
                                      (by prove_term_admissible)
                                      (by prove_term_admissible)
                                      (by
                                        simp only [Term.freeSupport]
                                        intro h
                                        exact hOffsetNe
                                          (m := 40) (n := 31)
                                          (by decide)
                                          (congrArg Prod.snd
                                            (List.mem_singleton.mp h)))
                                      (by
                                        simp only [Term.freeSupport]
                                        intro h
                                        exact hOffsetNe
                                          (m := 41) (n := 31)
                                          (by decide)
                                          (congrArg Prod.snd
                                            (List.mem_singleton.mp h)))
                                      (by
                                        simp only [Term.freeSupport]
                                        intro h
                                        exact hOffsetNe
                                          (m := 41) (n := 29)
                                          (by decide)
                                          (congrArg Prod.snd
                                            (List.mem_singleton.mp h)))
                                      hTraceFreshContext hBodyComponent
                                      (by
                                        simpa [bodyCode] using
                                          hBodyNumericEquality)
                                have hBodyStandard :
                                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                      x#(base + 31) ≐ₘ
                                        standard_token_sequence
                                          bodyTokens :=
                                  FirstOrder.Derives.context_weaken
                                    (Γ := Γ) (Δ := Δ) hWeaken
                                    hBodyStandardΓ
                                have hVariableCongruence :
                                    Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                      var_codeₘ(numₘ(2) *ₘ
                                          x#(base + 28)) ≐ₘ
                                        var_codeₘ(numₘ(2) *ₘ
                                          numₘ(eigen)) :=
                                  Metatheory.Derives.unary_term_constructor_congr_of_equality
                                    (fun value =>
                                      var_codeₘ(numₘ(2) *ₘ value))
                                    (fun value hValue =>
                                      variable_code_term_admissible _ <|
                                        natural_multiplication_term_admissible
                                          (numₘ(2)) value
                                          (finite_numeral_term_admissible 2)
                                          hValue)
                                    (by
                                      intros
                                      simp [Term.substituteFree,
                                        Term.substituteFree_eq_self_of_not_mem,
                                        finite_numeral_term_freeSupport])
                                    (x#(base + 28)) (numₘ(eigen))
                                    (set_variable_admissible (base + 28))
                                    (finite_numeral_term_admissible eigen)
                                    (by
                                      simpa [eigen] using hEigenEquality)
                                have hVariableArithmetic :
                                    Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                      var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) ≐ₘ
                                        var_codeₘ(numₘ(2 * eigen)) :=
                                  FirstOrder.Derives.context_weaken
                                    (Γ := []) (Δ := Γ) (by simp) <|
                                      Metatheory.Derives.equality_symm
                                        (fs_zfc_support_raw_variable_code_term_numeral_mul
                                          eigen)
                                have hVariableStandardΓ :
                                    Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                      x#(base + 34) ≐ₘ
                                        standard_token_sequence
                                          [Numbered.variable_token
                                            (free_name eigen)] := by
                                  exact
                                    Metatheory.Derives.equality_trans
                                      hVariableEquality <|
                                        Metatheory.Derives.equality_trans
                                          hVariableCongruence <|
                                            Metatheory.Derives.equality_trans
                                              hVariableArithmetic <|
                                                FirstOrder.Derives.context_weaken
                                                  (Γ := []) (Δ := Γ)
                                                  (by simp) <| by
                                                    apply
                                                      FirstOrder.Derives.theory_weaken
                                                        (fun _ hFormula =>
                                                          fs_zfc_support_raw_contains_godel_quotation
                                                            hFormula)
                                                    simpa [
                                                      Numbered.named_variable_code,
                                                      free_name] using
                                                      named_variable_code_eq_standard_token_sequence
                                                        (free_name eigen)
                                have hVariableStandard :
                                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                      x#(base + 34) ≐ₘ
                                        standard_token_sequence
                                          [Numbered.variable_token
                                            (free_name eigen)] :=
                                  FirstOrder.Derives.context_weaken
                                    (Γ := Γ) (Δ := Δ) hWeaken
                                    hVariableStandardΓ
                                have hFreshVariable
                                    (id offset : Nat)
                                    (hUpper : id ≤ 470) :
                                    (SetSort.set, id) ∉
                                      Term.freeSupport
                                        (x#(base + offset)) :=
                                  fs_zfc_fo_failure_set_variable_fresh
                                    id (base + offset) <| by
                                      apply Nat.ne_of_lt
                                      exact Nat.lt_of_le_of_lt hUpper <|
                                        Nat.lt_of_lt_of_le
                                          (by decide : 470 < 700) <|
                                            Nat.le_trans hBaseLower
                                              (Nat.le_add_right base offset)
                                by_cases hNotBound :
                                    fs_named_hilbert_tree_target_not_bound
                                      (Numbered.variable_token
                                        (free_name eigen))
                                      sourceTree
                                · by_cases hSafe :
                                      fs_named_hilbert_tree_substitution_safe
                                        (Numbered.variable_token
                                          (free_name eigen))
                                        replacementTree sourceTree
                                  · let resultTokens : List Nat :=
                                      substitute_tokens bodyTokens
                                        (Numbered.variable_token
                                          (free_name eigen))
                                        leftTokens
                                    have hResultDecode :
                                        fs_named_hilbert_tokens_decode_with_env
                                            freeBase [] resultTokens =
                                          some
                                            ((Formula.closeFreeAt SetSort.set
                                                eigen 0 body)⟦SetSort.set,
                                              0 ↦ term⟧ₘ) := by
                                      have hSubstitute :=
                                        fs_named_hilbert_tokens_decode_with_env_substitute_free_of_trees
                                          freeBase eigen
                                          bodyTokens leftTokens
                                          sourceTree replacementTree
                                          body term hEigenBound
                                          hSourceParse hReplacementParse
                                          hBodyNamed hTerm
                                          hTermWellSorted hNotBound hSafe
                                      simpa [resultTokens,
                                        Formula.openAt_closeFreeAt_eq_substituteFree]
                                        using hSubstitute
                                    let candidate : SetFormula :=
                                      Formula.imp
                                        (Formula.forallE SetSort.set
                                          (Formula.closeFreeAt SetSort.set
                                            eigen 0 body))
                                        ((Formula.closeFreeAt SetSort.set
                                            eigen 0 body)⟦SetSort.set,
                                          0 ↦ term⟧ₘ)
                                    let expectedTokens : List Nat :=
                                      Numbered.implication_tokens
                                        closedTokens resultTokens
                                    have hExpectedDecode :
                                        fs_named_hilbert_tokens_decode_with_env
                                            freeBase [] expectedTokens =
                                          some candidate := by
                                      exact
                                        fs_named_hilbert_tokens_decode_with_env_implication
                                          freeBase [] hClosedDecode hResultDecode
                                    have hFormulaCheck :
                                        fs_formula_code_eq
                                            decoded.formula candidate =
                                          false := by
                                      simpa [candidate, eigen,
                                        Term.check_wellSorted_complete
                                          hTermWellSorted,
                                        Term.check_scoped_complete
                                          hTermScoped] using hCheck
                                    have hCandidateDifferent :
                                        candidate ≠ decoded.formula :=
                                      Ne.symm
                                        (fs_formula_code_eq_ne_of_false
                                          hFormulaCheck)
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
                                    have hUniversalFunctional :=
                                      FirstOrder.Derives.context_weaken
                                        (Γ := []) (Δ := Δ) (by simp) <|
                                          fs_zfc_support_raw_canonical_forall_closure_unique_imp
                                            bodyTokens shiftedTokens eigen hShift
                                            (x#(base + 31))
                                            (x#(base + 34))
                                            (x#(base + 35))
                                            (Term.check_certificate_of_admissible <|
                                              set_variable_admissible (base + 31))
                                            (Term.check_certificate_of_admissible <|
                                              set_variable_admissible (base + 34))
                                            (Term.check_certificate_of_admissible <|
                                              set_variable_admissible (base + 35))
                                            (by
                                              intro id _ hUpper
                                              exact hFreshVariable id 31
                                                (Nat.le_trans hUpper (by decide)))
                                            (by
                                              intro id _ hUpper
                                              exact hFreshVariable id 34
                                                (Nat.le_trans hUpper (by decide)))
                                            (by
                                              intro id hId
                                              exact hFreshVariable id 31 <| by
                                                rcases hId with rfl | rfl <;>
                                                  decide)
                                            (by
                                              intro id hId
                                              exact hFreshVariable id 34 <| by
                                                rcases hId with rfl | rfl <;>
                                                  decide)
                                            (by
                                              intro id hId
                                              exact hFreshVariable id 35 <| by
                                                rcases hId with rfl | rfl <;>
                                                  decide)
                                            (by
                                              intro id hId
                                              exact hFreshVariable id 34 <| by
                                                rcases hId with rfl | rfl <;>
                                                  decide)
                                    have hUniversalEquality :
                                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                          x#(base + 35) ≐ₘ
                                            standard_token_sequence
                                              closedTokens := by
                                      simpa [closedTokens] using
                                        FirstOrder.Derives.impElim
                                          (FirstOrder.Derives.impElim
                                            (FirstOrder.Derives.impElim
                                              hUniversalFunctional
                                              hBodyStandard)
                                            hVariableStandard)
                                          (FirstOrder.Derives.context_weaken
                                            (Γ := Γ) (Δ := Δ) hWeaken
                                            hUniversal)
                                    have hBodyFormulaFields :
                                        Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                          formula_codeₘ(x#(base + 31)) ∧ₘ
                                            fs_formula_replay_condition
                                              (x#(base + 31)) :=
                                      FirstOrder.Derives.conjElimLeft
                                        hBodyComponent
                                    have hBodyFormula :
                                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                          formula_codeₘ(x#(base + 31)) := by
                                      have hBodyFormulaΓ :
                                          Γ ⊢ₘ[fs_zfc_support_raw_theory]
                                            formula_codeₘ(x#(base + 31)) :=
                                        FirstOrder.Derives.conjElimLeft
                                          hBodyFormulaFields
                                      exact
                                      FirstOrder.Derives.context_weaken
                                        (Γ := Γ) (Δ := Δ) hWeaken
                                        hBodyFormulaΓ
                                    have hVariableFresh :
                                        ReservedIdsFresh [310, 311]
                                          [x#(base + 31), x#(base + 34),
                                            x#(base + 33), x#(base + 36)] := by
                                      intro value hValue id hId
                                      simp only [List.mem_cons,
                                        List.not_mem_nil, or_false] at hValue hId
                                      rcases hValue with
                                        rfl | rfl | rfl | rfl
                                      · rcases hId with rfl | rfl <;>
                                          exact hFreshVariable _ 31 (by decide)
                                      · rcases hId with rfl | rfl <;>
                                          exact hFreshVariable _ 34 (by decide)
                                      · rcases hId with rfl | rfl <;>
                                          exact hFreshVariable _ 33 (by decide)
                                      · rcases hId with rfl | rfl <;>
                                          exact hFreshVariable _ 36 (by decide)
                                    have hResultEquality :
                                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                          x#(base + 36) ≐ₘ
                                            standard_token_sequence
                                              resultTokens := by
                                      have hTermCodeΔ :=
                                        FirstOrder.Derives.context_weaken
                                          (Γ := Γ) (Δ := Δ) hWeaken hTermCode
                                      have hSubstitutionΔ :=
                                        FirstOrder.Derives.context_weaken
                                          (Γ := Γ) (Δ := Δ) hWeaken
                                          hSubstitution
                                      have hUnique :=
                                        FirstOrder.Derives.context_weaken
                                          (Γ := []) (Δ := Δ) (by simp) <|
                                            fs_zfc_support_raw_code_substitution_standard_unique_imp
                                              bodyTokens leftTokens eigen
                                              (x#(base + 31))
                                              (x#(base + 34))
                                              (x#(base + 33))
                                              (x#(base + 36))
                                              (by prove_term_check)
                                              (by prove_term_check)
                                              (by prove_term_check)
                                              (by prove_term_check)
                                              hVariableFresh
                                      simpa [resultTokens] using
                                        FirstOrder.Derives.impElim
                                          (FirstOrder.Derives.impElim
                                            (FirstOrder.Derives.impElim
                                              (FirstOrder.Derives.impElim
                                                (FirstOrder.Derives.impElim
                                                  (FirstOrder.Derives.impElim
                                                    hUnique hBodyFormula)
                                                  hTermCodeΔ)
                                                hBodyStandard)
                                              hVariableStandard)
                                            hLeft)
                                          hSubstitutionΔ
                                    have hWholeEquality :=
                                      fs_zfc_support_raw_implication_code_eq_standard
                                        closedTokens resultTokens
                                        (x#(base + 35)) (x#(base + 36))
                                        (by prove_term_check)
                                        (by prove_term_check)
                                        hUniversalEquality hResultEquality
                                    have hFormulaEquality' :
                                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                          standard_token_sequence row ≐ₘ
                                            specialization_axiom_code_term
                                              (x#(base + 35))
                                              (x#(base + 36)) :=
                                      FirstOrder.Derives.context_weaken
                                        (Γ := Γ) (Δ := Δ) hWeaken
                                        hFormulaEquality
                                    have hRowEquality :
                                        Δ ⊢ₘ[fs_zfc_support_raw_theory]
                                          standard_token_sequence row ≐ₘ
                                            standard_token_sequence
                                              expectedTokens := by
                                      simpa [specialization_axiom_code_term,
                                        expectedTokens] using
                                          Metatheory.Derives.equality_trans
                                            hFormulaEquality' hWholeEquality
                                    exact FirstOrder.Derives.negElim
                                      hRowEquality <|
                                        FirstOrder.Derives.context_weaken
                                          (Γ := []) (Δ := Δ) (by simp) <|
                                            fs_zfc_support_raw_derives_of_standard_sequence <|
                                              standard_token_sequence_ne hRowNe
                                  · exact
                                      fs_zfc_support_raw_logical_substitution_capture_unsafe_elim
                                        (Γ := Γ) (Δ := Δ)
                                        freeBase eigen bodyTokens leftTokens
                                        sourceTree replacementTree body term
                                        (x#(base + 34)) (x#(base + 33))
                                        (x#(base + 31))
                                        (set_variable_admissible (base + 34))
                                        (set_variable_admissible (base + 33))
                                        (set_variable_admissible (base + 31))
                                        (fun id hUpper =>
                                          hFreshVariable id 34 hUpper)
                                        (fun id hUpper =>
                                          hFreshVariable id 33 hUpper)
                                        (fun id hUpper =>
                                          hFreshVariable id 31 hUpper)
                                        hWeaken hSafe hSourceParse
                                        hSourceTreeDecode hReplacementParse
                                        hReplacementTreeDecode hVariableStandard
                                        hBodyStandard hLeft hNoQuantifier
                                        hSubstitutable
                                · exact
                                    fs_zfc_support_raw_logical_substitution_target_bound_elim
                                      (Γ := Γ) (Δ := Δ)
                                      freeBase eigen bodyTokens sourceTree body
                                      (x#(base + 34)) (x#(base + 31))
                                      (set_variable_admissible (base + 34))
                                      (set_variable_admissible (base + 31))
                                      (fun id hUpper =>
                                        hFreshVariable id 34 hUpper)
                                      (fun id hUpper =>
                                        hFreshVariable id 31 hUpper)
                                      hWeaken hNotBound hSourceParse
                                      hSourceTreeDecode hVariableStandard
                                      hBodyStandard hNoQuantifier
                      · have hStandard :
                            Δ ⊢ₘ[fs_zfc_support_raw_theory]
                              standard_token_sequence leftTokens ≐ₘ
                                standard_token_sequence rightTokens :=
                          Metatheory.Derives.equality_trans
                            (Metatheory.Derives.equality_symm hLeft)
                            hRight
                        exact FirstOrder.Derives.negElim hStandard <|
                          FirstOrder.Derives.context_weaken
                            (Γ := []) (Δ := Δ) (by simp) <|
                              fs_zfc_support_raw_derives_of_standard_sequence <|
                                standard_token_sequence_ne hTokenEquality
                    · have hStandard :
                          Δ ⊢ₘ[fs_zfc_support_raw_theory]
                            standard_token_sequence tokens ≐ₘ
                              standard_token_sequence expected :=
                        Metatheory.Derives.equality_trans
                          hEquality' hExpectedStandard
                      exact FirstOrder.Derives.negElim hStandard <|
                        FirstOrder.Derives.context_weaken
                          (Γ := []) (Δ := Δ) (by simp) <|
                            fs_zfc_support_raw_derives_of_standard_sequence <|
                              standard_token_sequence_ne hShape
                  · have hStandardSignature :
                        Γ ⊢ₘ[fs_zfc_support_raw_theory]
                          fs_formula_signature_condition
                            (standard_token_sequence tokens) := by
                      simpa [fs_formula_replay_condition] using
                        FirstOrder.Derives.conjElimLeft hStandardReplay
                    have hSignatureNot :
                        ⊢ₘ[fs_zfc_support_raw_theory]
                          ¬ₘ fs_formula_signature_condition
                            (standard_token_sequence tokens) := by
                      exact
                        fs_zfc_support_raw_standard_token_sequence_signature_neg_of_token
                          tokens tokenIndex hTokenIndex hToken
                    exact FirstOrder.Derives.negElim
                      hStandardSignature <|
                        FirstOrder.Derives.context_weaken
                          (Γ := []) (Δ := Γ) (by simp) hSignatureNot
end FormalSystem.CertifiedProof

end YesMetaZFC.Logic.FirstOrder
