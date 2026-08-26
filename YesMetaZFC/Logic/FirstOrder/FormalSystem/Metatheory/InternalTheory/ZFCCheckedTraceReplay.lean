import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCBoundedCheckedReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaBinderReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateTranscriptReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedTraceSupport

/-!
# ZFC checked trace 的对象层回放

本模块把外部 `FSCheckedHilbertTrace` 的逐行分类自动翻译为对象层
`CertifiedProof.line_condition_with_ids`，并据此装配完整的证明序列条件。

有限 trace 的列表归纳留在 `ZFCBoundedCheckedReplay`；这里仅承担三类行证书的
对象层构造，避免把分类结构与 Hilbert 编码细节耦合在同一模块。
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

/-! ## 公式码等式运输 -/

/-- `formula_codeₘ` 沿对象项等式从右向左运输。 -/
theorem ProofT.formula_code_of_eq
    {T : SetTheory}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Derives T [] (left ≐ₘ right))
    (hRightFormulaCode :
      Derives T [] formula_codeₘ(right)) :
    Derives T [] formula_codeₘ(left) := by
  let body : SetFormula := formula_codeₘ(x#442)
  have hRightInstance :
      Derives T [] (
        Formula.substituteFree SetSort.set 442 right body) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable] using hRightFormulaCode
  have hSymmetric :
      Derives T [] (right ≐ₘ left) :=
    Metatheory.Derives.equality_symm
      hEquality
  have hTransport :
      Derives T [] (
        Formula.substituteFree SetSort.set 442 left body) :=
    FirstOrder.Derives.eq_subst_m
      (T := T) (Γ := [])
      (sort := SetSort.set) (eigen := 442)
      (left := right) (right := left) (body := body)
      hSymmetric hRightInstance
  simpa [body, Formula.substituteFree,
    Term.substituteFree, set_variable] using hTransport

/-- 标准公式序列的指定位置等于该行的总化 quotation 项。 -/
theorem ProofT.ZFC.formula_sequence_apply_eq_code
    {T : SetTheory}
    (hStandardSequence :
      ∀ {candidate : SetFormula},
        standard_sequence_semantics_theory candidate → T candidate)
    (hQuotation :
      ∀ {candidate : SetFormula},
        godel_quotation_theory candidate → T candidate)
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    {index : Nat}
    {formula : SetFormula}
    (hGet : proof[index]? = some formula) :
    Derives T [] (
      (standard_sequence
          (proof.map (fun row =>
            standard_token_sequence
              (certified_row_tokens row))) ·ₘ
        numₘ(index)) ≐ₘ
      fs_zfc_formula_code_term formula) := by
  have hFormula :
      Formula.Admissible formula :=
    hRows formula (List.mem_of_getElem? hGet)
  have hApply :=
    ProofT.ZFC.formula_sequence_apply
      hStandardSequence
      hGet
  have hCode :=
    ProofT.ZFC.formula_code_eq_tokens
      hQuotation
      hFormula
  have hCodeSymmetric :=
    Metatheory.Derives.equality_symm
      hCode
  exact Metatheory.Derives.equality_trans
    hApply hCodeSymmetric

/-! ## 逐行公式条件回放 -/

/--
标准公式序列的任意有效位置满足对象 verifier 的完整 replay 词法条件。
-/
theorem ProofT.formula_condition_at
    {T : SetTheory}
    (hStandardSequence :
      ∀ {candidate : SetFormula},
        standard_sequence_semantics_theory candidate → T candidate)
    (hFormulaReplay :
      ∀ tokens,
        FSFormulaTokens tokens →
        FSFormulaBinderTokens tokens →
        Derives T [] (
          fs_formula_replay_condition
            (standard_token_sequence tokens)))
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    (indexId : FreeVarId)
    (index : Nat) (hIndex : index < proof.length) :
    Derives T [] (
      ((x#indexId ≐ₘ numₘ(index)) ⟶ₘ
        verifier.formula_condition
          (standard_sequence
              (proof.map (fun formula =>
                standard_token_sequence
                  (certified_row_tokens formula))) ·ₘ
            x#indexId))) := by
  let sequence : SetTerm :=
    standard_sequence
      (proof.map (fun formula =>
        standard_token_sequence
          (certified_row_tokens formula)))
  let point : SetTerm := x#indexId
  let currentCode : SetTerm :=
    sequence ·ₘ point
  let equality : SetFormula :=
    point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  let formula := proof[index]
  have hGet :
      proof[index]? = some formula :=
    List.getElem?_eq_some_iff.mpr
      ⟨hIndex, rfl⟩
  have hFormula :
      Formula.Admissible formula :=
    hRows formula (by
      simp [formula])
  rcases Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hQuote⟩
  have hTokens :
      FSFormulaTokens
        (certified_row_tokens formula) := by
    simpa [certified_row_tokens, hQuote] using
      fs_quote_tokens_formula_tokens
        hFormula hQuote
  have hBinder :
      FSFormulaBinderTokens
        (certified_row_tokens formula) := by
    simpa [certified_row_tokens, hQuote] using
      fs_quote_tokens_formula_binder_tokens
        hQuote
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, _, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens row)
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible indexId
  have hCurrentCode :
      Term.Admissible currentCode SetSort.set := by
    simpa [currentCode] using
      function_application_term_admissible
        sequence point hSequence hPoint
  have hRowCode :
      Term.Admissible
        (standard_token_sequence
          (certified_row_tokens formula))
        SetSort.set :=
    standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hRowCondition :
      Derives T [] (
        fs_formula_replay_condition
          (standard_token_sequence
            (certified_row_tokens formula))) :=
    hFormulaReplay
      (certified_row_tokens formula)
      hTokens hBinder
  have hConclusion :
      Formula.Admissible
        (verifier.formula_condition
          currentCode) := by
    exact verifier.formula_condition_admissible
      currentCode hCurrentCode
  nd_apply FirstOrder.Derives.impIntro
  have hIndexEquality :
      Γ ⊢ₘ[T]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Γ) (φ := equality)
        (by simp [Γ]))
  have hCurrentToNumeral :
      Γ ⊢ₘ[T]
        currentCode ≐ₘ
          (sequence ·ₘ numₘ(index)) := by
    simpa [currentCode] using
      function_application_term_congr_argument_of_equality
        sequence point (numₘ(index))
        hSequence hPoint
        (finite_numeral_term_admissible index)
        hIndexEquality
  have hNumeralToRow :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence
            (certified_row_tokens formula) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      (by
        simpa [sequence, formula] using
          ProofT.ZFC.formula_sequence_apply
            hStandardSequence
            hGet)
  have hCurrentToRow :
      Γ ⊢ₘ[T]
        currentCode ≐ₘ
          standard_token_sequence
            (certified_row_tokens formula) :=
    Metatheory.Derives.equality_trans
      hCurrentToNumeral hNumeralToRow
  have hConditionIff :=
    fs_formula_replay_condition_iff_of_equality
      currentCode
      (standard_token_sequence
        (certified_row_tokens formula))
      hCurrentCode hRowCode
      hCurrentToRow
  have hRowConditionInContext :
      Γ ⊢ₘ[T]
        fs_formula_replay_condition
          (standard_token_sequence
            (certified_row_tokens formula)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      hRowCondition
  have hCurrentCondition :
      Γ ⊢ₘ[T]
        fs_formula_replay_condition currentCode :=
    FirstOrder.Derives.iffElimLeft
      hConditionIff hRowConditionInContext
  rw [hContract.formula_condition]
  simpa [Γ, equality, currentCode] using hCurrentCondition

/-! ## checked trace 的逐行自动回放 -/

/--
checked trace 的任意有效位置都自动给出对象层行条件。

保留编号统一取自 `ProofT.CheckedSyntax`：除当前行、证书 payload 与
MP 两个早先行外，还显式携带逻辑证书 transcript 的六个内部编号。
-/
theorem ProofT.ZFC.line_condition_at
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {formula : SetFormula},
        enumeration.certificate_verifier
            certificate formula = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term formula)
              (numₘ(certificate))))
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace
        enumeration
        fs_logical_axiom_canonical_check
        proof certificates)
    (index : Nat)
    (hIndex : index < proof.length) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#ProofT.line_index_id ≐ₘ numₘ(index)) ⟶ₘ
        CertifiedProof.line_condition_with_ids
          verifier
          (standard_sequence
            (proof.map (fun formula =>
              standard_token_sequence
                (certified_row_tokens formula))))
          (standard_token_sequence
            (certificates.map
              HilbertLineCertificateCode.value))
          (x#ProofT.line_index_id)
          ProofT.certificate_code_id
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id
          ProofT.mp_implication_id
          ProofT.mp_premise_id)) := by
  let sequence : SetTerm :=
    standard_sequence
      (proof.map (fun formula =>
        standard_token_sequence
          (certified_row_tokens formula)))
  let certificateSequence : SetTerm :=
    standard_token_sequence
      (certificates.map HilbertLineCertificateCode.value)
  have hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula := by
    intro formula hFormula
    exact fs_checked_trace_admissible_of_mem
      hTrace hFormula
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    dsimp [sequence]
    apply seq_support_nil_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens formula)
  have hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set := by
    dsimp [certificateSequence]
    exact standard_token_sequence_admissible
      (certificates.map HilbertLineCertificateCode.value)
  have hCertificateSequenceClosed :
      Term.freeSupport certificateSequence = [] := by
    dsimp [certificateSequence]
    exact standard_token_sequence_freeSupport_nil
      (certificates.map HilbertLineCertificateCode.value)
  rcases fs_checked_trace_line_classification_of_index
      hTrace index hIndex with
    ⟨formula, certificate, hFormulaGet,
      hCertificateGet, hClassification⟩
  rcases hClassification with
    hLogical | hTheory | hModusPonens
  · rcases hLogical with
      ⟨payload, hCertificate, hCheck, hFormula⟩
    subst certificate
    have hFormulaCode :=
      ProofT.ZFC.formula_sequence_apply_eq_code
        fs_zfc_support_raw_contains_standard_sequence_semantics
        fs_zfc_support_raw_contains_godel_quotation
        hRows hFormulaGet
    have hCertificateCode :=
      fs_zfc_support_raw_standard_logical_certificate_code_at
        hCertificateGet
    have hLogicalCode :=
      CertifiedProof.fs_zfc_support_raw_logical_certificate_condition_of_check
        hCheck hFormula
    have hResult :=
      ProofT.ZFC.logical_line_of_components
        verifier hContract
        sequence certificateSequence index payload
        hSequence hCertificateSequence
        hSequenceClosed hCertificateSequenceClosed
        (code := fs_zfc_formula_code_term formula)
        (fs_zfc_formula_code_term_code_boundary formula).2
        hFormulaCode hCertificateCode hLogicalCode
    simpa [sequence, certificateSequence] using hResult
  · rcases hTheory with
      ⟨payload, hCertificate, hCheck, hFormula⟩
    subst certificate
    have hFormulaCode :
        Derives fs_zfc_support_raw_theory [] (
          sequence ·ₘ numₘ(index) ≐ₘ
            fs_zfc_formula_code_term formula) := by
      simpa [sequence] using
        ProofT.ZFC.formula_sequence_apply_eq_code
          fs_zfc_support_raw_contains_standard_sequence_semantics
          fs_zfc_support_raw_contains_godel_quotation
          hRows hFormulaGet
    have hCurrent :
        Term.Admissible
          (sequence ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        sequence (numₘ(index)) hSequence
        (finite_numeral_term_admissible index)
    have hCurrentClosed :
        Term.freeSupport
          (sequence ·ₘ numₘ(index)) = [] := by
      simp [Term.freeSupport, Term.freeSupportList,
        hSequenceClosed, finite_numeral_term_freeSupport]
    have hVerifierRight :
        Derives fs_zfc_support_raw_theory [] (
          verifier.condition
            (fs_zfc_formula_code_term formula)
            (numₘ(payload))) := by
      exact hTheoryCertificate hCheck
    have hVerifier :
        Derives fs_zfc_support_raw_theory [] (
          verifier.condition
            (sequence ·ₘ numₘ(index))
            (numₘ(payload))) :=
      ProofT.certificate_condition_of_code_eq
        verifier hContract
        (sequence ·ₘ numₘ(index))
        (fs_zfc_formula_code_term formula)
        (numₘ(payload))
        hCurrent
        (fs_zfc_formula_code_term_admissible formula)
        hCurrentClosed
        (fs_zfc_formula_code_term_freeSupport_nil formula)
        (finite_numeral_term_freeSupport payload)
        hFormulaCode hVerifierRight
    have hCertificateCode :=
      fs_zfc_support_raw_standard_theory_certificate_code_at
        hCertificateGet
    have hResult :=
      ProofT.ZFC.theory_line_of_components
        verifier hContract
        sequence certificateSequence index payload
        hSequence hCertificateSequence
        hSequenceClosed hCertificateSequenceClosed
        hCertificateCode hVerifier
    simpa [sequence, certificateSequence] using hResult
  · rcases hModusPonens with
      ⟨implicationIndex, premiseIndex, antecedent, consequent,
        hCertificate, hImplicationGet, hPremiseGet,
        hPremiseEarlier, hImplicationEarlier, hFormula⟩
    subst certificate
    subst formula
    have hAntecedent :
        Formula.Admissible antecedent :=
      hRows antecedent (List.mem_of_getElem? hPremiseGet)
    have hImplication :
        Formula.Admissible (Formula.imp antecedent consequent) :=
      hRows (Formula.imp antecedent consequent)
        (List.mem_of_getElem? hImplicationGet)
    have hConsequent :
        Formula.Admissible consequent :=
      Formula.Admissible.imp_right hImplication
    rcases GodelQuotation.Numbered.quote?_exists hAntecedent with
      ⟨antecedentCode, hAntecedentQuote⟩
    rcases GodelQuotation.Numbered.quote?_exists hConsequent with
      ⟨consequentCode, hConsequentQuote⟩
    have hImplicationQuote :
        GodelQuotation.Numbered.quote?
            (Formula.imp antecedent consequent) =
          some (imp_codeₘ(antecedentCode, consequentCode)) :=
      quote_implication_code
        hAntecedentQuote hConsequentQuote
    have hPremiseCode :
        Derives fs_zfc_support_raw_theory [] (
          sequence ·ₘ numₘ(premiseIndex) ≐ₘ
            antecedentCode) := by
      simpa [sequence] using
        ProofT.ZFC.formula_sequence_code_eq
          hRows hPremiseGet hAntecedentQuote
    have hImplicationCode :
        Derives fs_zfc_support_raw_theory [] (
          sequence ·ₘ numₘ(implicationIndex) ≐ₘ
            imp_codeₘ(antecedentCode, consequentCode)) := by
      simpa [sequence] using
        ProofT.ZFC.formula_sequence_code_eq
          hRows hImplicationGet hImplicationQuote
    have hConclusionCode :
        Derives fs_zfc_support_raw_theory [] (
          sequence ·ₘ numₘ(index) ≐ₘ
            consequentCode) := by
      simpa [sequence] using
        ProofT.ZFC.formula_sequence_code_eq
          hRows hFormulaGet hConsequentQuote
    have hPremiseTerm :
        Term.Admissible
          (sequence ·ₘ numₘ(premiseIndex)) SetSort.set :=
      function_application_term_admissible
        sequence (numₘ(premiseIndex)) hSequence
        (finite_numeral_term_admissible premiseIndex)
    have hImplicationTerm :
        Term.Admissible
          (sequence ·ₘ numₘ(implicationIndex)) SetSort.set :=
      function_application_term_admissible
        sequence (numₘ(implicationIndex)) hSequence
        (finite_numeral_term_admissible implicationIndex)
    have hConclusionTerm :
        Term.Admissible
          (sequence ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        sequence (numₘ(index)) hSequence
        (finite_numeral_term_admissible index)
    have hAntecedentCode :=
      GodelQuotation.Numbered.quote?_code_boundary
        hAntecedentQuote
    have hConsequentCode :=
      GodelQuotation.Numbered.quote?_code_boundary
        hConsequentQuote
    have hPremiseFormulaCode :
        Derives fs_zfc_support_raw_theory [] (
          formula_codeₘ(
            sequence ·ₘ numₘ(premiseIndex))) :=
      ProofT.formula_code_of_eq
        (sequence ·ₘ numₘ(premiseIndex))
        antecedentCode
        hPremiseTerm hAntecedentCode.1 hPremiseCode
        (fs_zfc_support_raw_derives_of_godel_quotation
          (GodelQuotation.Numbered.quote?_is_formula_code
            hAntecedentQuote))
    have hImplicationFormulaCode :
        Derives fs_zfc_support_raw_theory [] (
          formula_codeₘ(
            sequence ·ₘ numₘ(implicationIndex))) :=
      ProofT.formula_code_of_eq
        (sequence ·ₘ numₘ(implicationIndex))
        (imp_codeₘ(antecedentCode, consequentCode))
        hImplicationTerm
        (GodelQuotation.Numbered.quote?_code_boundary
          hImplicationQuote).1
        hImplicationCode
        (fs_zfc_support_raw_derives_of_godel_quotation
          (GodelQuotation.Numbered.quote?_is_formula_code
            hImplicationQuote))
    have hConclusionFormulaCode :
        Derives fs_zfc_support_raw_theory [] (
          formula_codeₘ(
            sequence ·ₘ numₘ(index))) :=
      ProofT.formula_code_of_eq
        (sequence ·ₘ numₘ(index))
        consequentCode
        hConclusionTerm hConsequentCode.1 hConclusionCode
        (fs_zfc_support_raw_derives_of_godel_quotation
          (GodelQuotation.Numbered.quote?_is_formula_code
            hConsequentQuote))
    have hConstructorCongruence :
        Derives fs_zfc_support_raw_theory [] (
          imp_codeₘ(
              sequence ·ₘ numₘ(premiseIndex),
              sequence ·ₘ numₘ(index)) ≐ₘ
            imp_codeₘ(antecedentCode, consequentCode)) :=
      Metatheory.Derives.binary_term_constructor_congr_of_equalities
        (fun left right => imp_codeₘ(left, right))
        (fun left right hLeft hRight =>
          implication_formula_code_term_admissible
            left right hLeft hRight)
        (by
          intro parameter replacement left right
          simp [Term.substituteFree])
        (sequence ·ₘ numₘ(premiseIndex))
        antecedentCode
        (sequence ·ₘ numₘ(index))
        consequentCode
        hPremiseTerm hAntecedentCode.1
        hConclusionTerm hConsequentCode.1
        hPremiseCode hConclusionCode
    have hConstructorSymmetric :
        Derives fs_zfc_support_raw_theory [] (
          imp_codeₘ(antecedentCode, consequentCode) ≐ₘ
            imp_codeₘ(
              sequence ·ₘ numₘ(premiseIndex),
              sequence ·ₘ numₘ(index))) :=
      Metatheory.Derives.equality_symm
        hConstructorCongruence
    have hImplicationShape :
        Derives fs_zfc_support_raw_theory [] (
          sequence ·ₘ numₘ(implicationIndex) ≐ₘ
            imp_codeₘ(
              sequence ·ₘ numₘ(premiseIndex),
              sequence ·ₘ numₘ(index))) :=
      Metatheory.Derives.equality_trans
        hImplicationCode hConstructorSymmetric
    have hModusPonens :
        Derives fs_zfc_support_raw_theory [] (
          modus_ponensₘ(
            sequence ·ₘ numₘ(premiseIndex),
            sequence ·ₘ numₘ(implicationIndex),
            sequence ·ₘ numₘ(index))) :=
      modus_ponens_derives_of_condition
        (T := fs_zfc_support_raw_theory)
        (fun formula hFormula =>
          fs_zfc_support_raw_contains_logical_rules hFormula)
        (sequence ·ₘ numₘ(premiseIndex))
        (sequence ·ₘ numₘ(implicationIndex))
        (sequence ·ₘ numₘ(index))
        hPremiseTerm hImplicationTerm hConclusionTerm
        hPremiseFormulaCode hImplicationFormulaCode
        hConclusionFormulaCode hImplicationShape
    have hImplicationEarlierCode :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(implicationIndex) ∈ₘ numₘ(index)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          implicationIndex index hImplicationEarlier)
    have hPremiseEarlierCode :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(premiseIndex) ∈ₘ
            numₘ(implicationIndex)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          premiseIndex implicationIndex hPremiseEarlier)
    have hCertificateCode :=
      fs_zfc_support_raw_standard_modus_ponens_certificate_code_at
        hCertificateGet
    have hResult :=
      ProofT.ZFC.modus_ponens_line_of_components
        verifier hContract sequence certificateSequence
        index implicationIndex premiseIndex
        hSequence hCertificateSequence
        hSequenceClosed hCertificateSequenceClosed
        hCertificateCode hImplicationEarlierCode
        hPremiseEarlierCode hModusPonens
    simpa [sequence, certificateSequence] using hResult

/-! ## checked trace 的完整序列条件 -/

/--
非空 checked trace 自动回放为对象层证书化证明序列条件。

该接口不再要求调用方提供逐行证明、行 admissibility 或编号互异性；
这些数据分别由 checked trace 和固定保留编号直接决定。
-/
theorem ProofT.ZFC.trace_sequence_condition
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {formula : SetFormula},
        enumeration.certificate_verifier
            certificate formula = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term formula)
              (numₘ(certificate))))
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace
        enumeration
        fs_logical_axiom_canonical_check
        proof certificates)
    (hNonempty : proof ≠ []) :
    Derives fs_zfc_support_raw_theory [] (
      CertifiedProof.sequence_condition_with_ids
        verifier
        (standard_sequence
          (proof.map (fun formula =>
            standard_token_sequence
              (certified_row_tokens formula))))
        (standard_token_sequence
          (certificates.map
            HilbertLineCertificateCode.value))
        ProofT.line_index_id
        ProofT.certificate_code_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        ProofT.mp_implication_id
        ProofT.mp_premise_id) := by
  have hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula := by
    intro formula hFormula
    exact fs_checked_trace_admissible_of_mem
      hTrace hFormula
  have hLength :
      proof.length = certificates.length :=
    (fs_checked_trace_certificates_length hTrace).symm
  have hComponents :=
    fs_zfc_support_raw_standard_certified_sequence_components
      certificates hRows hNonempty hLength
  let sequence : SetTerm :=
    standard_sequence
      (proof.map (fun formula =>
        standard_token_sequence
          (certified_row_tokens formula)))
  let certificateSequence : SetTerm :=
    standard_token_sequence
      (certificates.map HilbertLineCertificateCode.value)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hElementsClosed :
      ∀ element,
        element ∈
          proof.map (fun formula =>
            standard_token_sequence
              (certified_row_tokens formula)) →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens formula)
  have hLineConclusion :
      Formula.Admissible
        (CertifiedProof.line_condition_with_ids
          verifier
          sequence certificateSequence
          (x#ProofT.line_index_id)
          ProofT.certificate_code_id
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id
          ProofT.mp_implication_id
          ProofT.mp_premise_id) :=
      CertifiedProof.line_condition_with_ids_admissible
      verifier
      sequence certificateSequence
      (x#ProofT.line_index_id)
      ProofT.certificate_code_id
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
      ProofT.mp_implication_id
      ProofT.mp_premise_id
      hSequence
      (by
        dsimp [certificateSequence]
        exact standard_token_sequence_admissible
          (certificates.map
            HilbertLineCertificateCode.value))
      (set_variable_admissible 900)
  have hFormulaConclusion :
      Formula.Admissible
        (verifier.formula_condition
          (sequence ·ₘ
            x#ProofT.line_index_id)) :=
    verifier.formula_condition_admissible
      (sequence ·ₘ x#ProofT.line_index_id)
      (function_application_term_admissible
        sequence
        (x#ProofT.line_index_id)
        hSequence
        (set_variable_admissible
          ProofT.line_index_id))
  have hCombinedConclusion :
      Formula.Admissible
        (verifier.formula_condition
            (sequence ·ₘ
              x#ProofT.line_index_id) ∧ₘ
          CertifiedProof.line_condition_with_ids
            verifier
            sequence certificateSequence
            (x#ProofT.line_index_id)
            ProofT.certificate_code_id
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
            ProofT.mp_implication_id
            ProofT.mp_premise_id) :=
    Formula.Admissible.conj
      hFormulaConclusion hLineConclusion
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(proof.length)) := by
    have hDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(
            standard_sequence
              (proof.map (fun formula =>
                standard_token_sequence
                  (certified_row_tokens formula)))) ≐ₘ
            numₘ(proof.length)) := by
      simpa [List.length_map] using
        standard_sequence_domain_eq_numeral_length
          (by
            intro element hElement
            rcases List.mem_map.mp hElement with
              ⟨formula, hFormula, rfl⟩
            exact standard_token_sequence_admissible
              (certified_row_tokens formula))
          (stdseq_element_fresh_of_support_nil hElementsClosed 0)
          (stdseq_element_fresh_of_support_nil hElementsClosed 1)
    have hDomainRaw :
        Derives fs_zfc_support_raw_theory [] (
          domₘ(
            standard_sequence
              (proof.map (fun formula =>
                standard_token_sequence
                  (certified_row_tokens formula)))) ≐ₘ
            numₘ(proof.length)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        hDomainStd
    simpa [sequence] using hDomainRaw
  have hAllLines :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set, ProofT.line_index_id],
          ((x#ProofT.line_index_id ∈ₘ domₘ(sequence)) ⟶ₘ
          (verifier.formula_condition
              (sequence ·ₘ
                  x#ProofT.line_index_id) ∧ₘ
              CertifiedProof.line_condition_with_ids
                verifier
                sequence certificateSequence
                (x#ProofT.line_index_id)
                ProofT.certificate_code_id
                ProofT.lc_sequence_id
                ProofT.lc_formula_trace_id
                ProofT.lc_last_index_id
                ProofT.lc_line_index_id
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id
                ProofT.mp_implication_id
                ProofT.mp_premise_id))) := by
    apply fs_zfc_support_raw_finite_domain_forall_imp
      sequence proof.length ProofT.line_index_id
      (verifier.formula_condition
          (sequence ·ₘ
            x#ProofT.line_index_id) ∧ₘ
        CertifiedProof.line_condition_with_ids
          verifier
          sequence certificateSequence
          (x#ProofT.line_index_id)
          ProofT.certificate_code_id
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id
          ProofT.mp_implication_id
          ProofT.mp_premise_id)
      hSequence hCombinedConclusion hDomain
    intro index hIndex
    have hFormula :=
      ProofT.formula_condition_at
        fs_zfc_support_raw_contains_standard_sequence_semantics
        fs_zfc_support_raw_standard_token_sequence_replay
        verifier hContract hRows ProofT.line_index_id
        index hIndex
    have hLine :=
      ProofT.ZFC.line_condition_at
        enumeration verifier hContract hTheoryCertificate
        hTrace index hIndex
    let equality : SetFormula :=
      x#ProofT.line_index_id ≐ₘ
        numₘ(index)
    let Γ : Context signature := [equality]
    nd_apply FirstOrder.Derives.impIntro
    have hEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          equality :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
    have hFormulaAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          verifier.formula_condition
            (sequence ·ₘ
              x#ProofT.line_index_id) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken_cons
          (by simpa [sequence] using hFormula))
        (by simpa [equality] using hEquality)
    have hLineAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          CertifiedProof.line_condition_with_ids
            verifier
            sequence certificateSequence
            (x#ProofT.line_index_id)
            ProofT.certificate_code_id
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
            ProofT.mp_implication_id
            ProofT.mp_premise_id :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken_cons
          (by
            simpa [sequence, certificateSequence]
              using hLine))
        (by simpa [equality] using hEquality)
    simpa [Γ, equality] using
      FirstOrder.Derives.conjIntro
        hFormulaAt hLineAt
  apply
    fs_zfc_support_raw_certified_sequence_condition_with_ids_of_components
      verifier
      sequence certificateSequence
      ProofT.line_index_id
      ProofT.certificate_code_id
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
      ProofT.mp_implication_id
      ProofT.mp_premise_id
  · simpa [sequence] using hComponents.1
  · simpa [certificateSequence] using hComponents.2.1
  · simpa [sequence, certificateSequence] using
      hComponents.2.2.1
  · simpa [sequence] using hComponents.2.2.2
  · exact hAllLines

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
