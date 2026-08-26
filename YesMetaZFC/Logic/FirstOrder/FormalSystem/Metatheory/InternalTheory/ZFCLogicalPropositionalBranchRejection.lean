import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPayloadFailureInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Support.Base

/-!
# 命题逻辑证书分支的 checked 拒绝

本模块把宿主层 payload 失败视图接入对象层 unary、binary、ternary 基础逻辑
证书。证明只打开证书条件自身携带的有限见证，并调用二元 payload 反演核。
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

/-- 对象变量项的自由支持只含自身。 -/
private theorem fs_zfc_support_raw_set_variable_fresh
    (source target : FreeVarId)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉
      Term.freeSupport (x#target) := by
  intro hMember
  change
    (SetSort.set, source) ∈
      [(SetSort.set, target)] at hMember
  exact hNe <| congrArg Prod.snd <|
    List.mem_singleton.mp hMember

/-- 对象变量在闭 numeral 上的函数应用不增加自由变量。 -/
private theorem fs_zfc_support_raw_set_application_numeral_fresh
    (source target : FreeVarId)
    (value : Nat)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉
      Term.freeSupport (x#target ·ₘ numₘ(value)) := by
  intro hMember
  simp [Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport] at hMember
  exact
    fs_zfc_support_raw_set_variable_fresh
      source target hNe hMember

/-- 在空背景中把一个打开见证的反证提升过一层存在量词。 -/
private theorem fs_zfc_support_raw_exists_imp_falsum
    (eigen : FreeVarId)
    (body : SetFormula)
    (hImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ Formula.falsum) :
    ([] : Context signature)
      ⊢ₘ[fs_zfc_support_raw_theory]
        (∃ₘ[SetSort.set, eigen], body) ⟶ₘ
          Formula.falsum := by
  apply FirstOrder.Derives.exists_imp_of_imp
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (sort := SetSort.set)
    (eigen := eigen)
    (body := body)
    (conclusion := Formula.falsum)
  · intro proposition hProposition
    rw [(fs_zfc_support_raw_theory_sentence hProposition).2]
    exact List.not_mem_nil
  · intro proposition hProposition
    exact False.elim (List.not_mem_nil hProposition)
  · exact List.not_mem_nil
  · exact hImp

/--
单公式 payload 的 checked 失败否定对应对象证书分支。

构造器的支持同态只用于证明内部 trace 对打开后的 witness body 新鲜。
-/
theorem fs_zfc_support_raw_logical_unary_base_certificate_neg_of_payload_failure
    (raw tag freeBase : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, componentId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, componentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ component,
        Term.Admissible component SetSort.set →
          Term.Admissible (constructor component) SetSort.set)
    (hConstructorSupport :
      ∀ component freeVariable,
        freeVariable ∈ Term.freeSupport (constructor component) →
          freeVariable ∈ Term.freeSupport component)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, componentId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hFailure :
      FSNamedFormulaPayloadArityFailure
        freeBase (godel_unpair_value raw).2 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(1),
      logical_formula_payload_component_condition_with_ids
        (x#componentId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#componentId)]
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hComponent :
      Term.Admissible (x#componentId) SetSort.set :=
    set_variable_admissible componentId
  have hNumeric :
      Term.Admissible (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hTracePayload : traceId ≠ payloadId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSequence : traceId ≠ sequenceId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceComponent : traceId ≠ componentId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hIndexPayload : indexId ≠ payloadId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSequence : indexId ≠ sequenceId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexComponent : indexId ≠ componentId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hFormulaTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport formulaCode :=
    hReservedFresh formulaCode (by simp) traceId (by simp)
  have hCertificateTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport certificate :=
    hReservedFresh certificate (by simp) traceId (by simp)
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible tag) hPayload
    · exact nat_sequence_code_condition_with_ids_admissible
        (x#sequenceId) (x#payloadId) traceId indexId
        hSequence hPayload
    · exact Formula.Admissible.equal
        (domain_term_admissible (x#sequenceId) hSequence)
        (finite_numeral_term_admissible 1)
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#componentId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hComponent hNumeric
    · exact Formula.Admissible.equal hFormulaCode
        (hConstructorAdmissible (x#componentId) hComponent)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ Formula.falsum := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hRestOne :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hRestTwo :=
      FirstOrder.Derives.conjElimRight hRestOne
    have hDomainField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#sequenceId) ≐ₘ numₘ(1) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestTwo
    have hComponentField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#componentId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hRestTwo
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with rfl | rfl | rfl | rfl | rfl
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        rcases hFieldSupport with hCertificateMember | hPayloadEq
        · exact hCertificateTraceFresh hCertificateMember
        · exact hTracePayload hPayloadEq
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId payloadId hTracePayload)
              hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList, finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#componentId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId componentId hTraceComponent)
              hMember
        · simp [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport] at hMember
          exact hTraceSequence hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport (constructor (x#componentId)) := by
          simp [Formula.freeSupport] at hFieldSupport
          rcases hFieldSupport with hFormulaMember | hConstructorMember
          · exact (hFormulaTraceFresh hFormulaMember).elim
          · exact hConstructorMember
        exact
          (fs_zfc_support_raw_set_variable_fresh
            traceId componentId hTraceComponent) <|
            hConstructorSupport
              (x#componentId) (SetSort.set, traceId)
              hConstructorMember
    cases hFailure with
    | length_mismatch hLength =>
        exact fs_zfc_support_raw_logical_payload_length_falsum
          raw tag 1 (x#payloadId) (x#sequenceId)
          traceId indexId hPayload hSequence hTraceNeIndex
          (fs_zfc_support_raw_set_variable_fresh
            traceId sequenceId hTraceSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId sequenceId hIndexSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId payloadId hIndexPayload)
          hTraceFreshContext hPair hSequenceField hDomainField hLength
    | component_failure componentIndex hComponentIndex hLength hDecode =>
        have hIndexZero : componentIndex = 0 := by
          have : componentIndex < 1 := by
            simpa [hLength] using hComponentIndex
          omega
        subst componentIndex
        exact fs_zfc_support_raw_logical_payload_component_falsum
          raw tag freeBase 0
          (x#payloadId) (x#sequenceId) (x#componentId)
          (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hPayload hSequence hComponent hNumeric
          hTraceNeIndex
          (fs_zfc_support_raw_set_variable_fresh
            traceId sequenceId hTraceSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId sequenceId hIndexSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId payloadId hIndexPayload)
          (fs_zfc_support_raw_set_variable_fresh
            traceId componentId hTraceComponent)
          (fs_zfc_support_raw_set_variable_fresh
            indexId componentId hIndexComponent)
          (fs_zfc_support_raw_set_application_numeral_fresh
            indexId sequenceId 0 hIndexSequence)
          hTraceFreshContext hPair hSequenceField
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set)
            (x#sequenceId ·ₘ numₘ(0)))
          hComponentField
          hComponentIndex hDecode
  let componentExists : SetFormula :=
    ∃ₘ[SetSort.set, componentId], body
  let sequenceExists : SetFormula :=
    ∃ₘ[SetSort.set, sequenceId], componentExists
  let payloadExists : SetFormula :=
    ∃ₘ[SetSort.set, payloadId], sequenceExists
  have hComponentImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          componentExists ⟶ₘ Formula.falsum := by
    simpa [componentExists] using
      fs_zfc_support_raw_exists_imp_falsum
        componentId body hBodyImp
  have hSequenceImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          sequenceExists ⟶ₘ Formula.falsum := by
    simpa [sequenceExists] using
      fs_zfc_support_raw_exists_imp_falsum
        sequenceId componentExists hComponentImp
  have hPayloadImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          payloadExists ⟶ₘ Formula.falsum := by
    simpa [payloadExists] using
      fs_zfc_support_raw_exists_imp_falsum
        payloadId sequenceExists hSequenceImp
  have hConditionAdmissible :
      Formula.Admissible
        (logical_unary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId componentId traceId indexId) :=
    logical_unary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate
      payloadId sequenceId componentId traceId indexId
      hConstructorAdmissible hFormulaCode hCertificate
  nd_apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionAdmissible)
  let condition : SetFormula :=
    logical_unary_base_certificate_condition_with_ids
      tag constructor formulaCode certificate
      payloadId sequenceId componentId traceId indexId
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hConditionAdmissible)
  have hPayloadImpAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition ⟶ₘ Formula.falsum := by
    simpa [condition,
      logical_unary_base_certificate_condition_with_ids,
      payloadExists, sequenceExists, componentExists, body] using
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature))
        (Δ := Γ) (by simp) hPayloadImp
  exact FirstOrder.Derives.impElim hPayloadImpAt hConditionAt

/--
双公式 payload 的 checked 失败否定对应对象证书分支。

字段失败只按索引选择左右组件；对象层反演仍只消费统一的二元序列关系。
-/
theorem fs_zfc_support_raw_logical_binary_base_certificate_neg_of_payload_failure
    (raw tag freeBase : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ left right,
        Term.Admissible left SetSort.set →
        Term.Admissible right SetSort.set →
          Term.Admissible (constructor left right) SetSort.set)
    (hConstructorSupport :
      ∀ left right freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor left right) →
          freeVariable ∈ Term.freeSupport left ∨
            freeVariable ∈ Term.freeSupport right)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, leftId, rightId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hFailure :
      FSNamedFormulaPayloadArityFailure
        freeBase (godel_unpair_value raw).2 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(2),
      logical_formula_payload_component_condition_with_ids
        (x#leftId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#rightId) (x#sequenceId ·ₘ numₘ(1))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#leftId) (x#rightId)]
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hLeft :
      Term.Admissible (x#leftId) SetSort.set :=
    set_variable_admissible leftId
  have hRight :
      Term.Admissible (x#rightId) SetSort.set :=
    set_variable_admissible rightId
  have hNumericLeft :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hNumericRight :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(1)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hTracePayload : traceId ≠ payloadId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSequence : traceId ≠ sequenceId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceLeft : traceId ≠ leftId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceRight : traceId ≠ rightId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hIndexPayload : indexId ≠ payloadId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSequence : indexId ≠ sequenceId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexLeft : indexId ≠ leftId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexRight : indexId ≠ rightId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hFormulaTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport formulaCode :=
    hReservedFresh formulaCode (by simp) traceId (by simp)
  have hCertificateTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport certificate :=
    hReservedFresh certificate (by simp) traceId (by simp)
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible tag) hPayload
    · exact nat_sequence_code_condition_with_ids_admissible
        (x#sequenceId) (x#payloadId) traceId indexId
        hSequence hPayload
    · exact Formula.Admissible.equal
        (domain_term_admissible (x#sequenceId) hSequence)
        (finite_numeral_term_admissible 2)
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#leftId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hLeft hNumericLeft
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#rightId) (x#sequenceId ·ₘ numₘ(1))
          traceId indexId hRight hNumericRight
    · exact Formula.Admissible.equal hFormulaCode
        (hConstructorAdmissible
          (x#leftId) (x#rightId) hLeft hRight)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ Formula.falsum := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hRestOne :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hRestTwo :=
      FirstOrder.Derives.conjElimRight hRestOne
    have hDomainField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#sequenceId) ≐ₘ numₘ(2) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestTwo
    have hRestThree :=
      FirstOrder.Derives.conjElimRight hRestTwo
    have hLeftField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#leftId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestThree
    have hRightField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#rightId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hRestThree
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        rcases hFieldSupport with hCertificateMember | hPayloadEq
        · exact hCertificateTraceFresh hCertificateMember
        · exact hTracePayload hPayloadEq
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId payloadId hTracePayload)
              hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList, finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#leftId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId leftId hTraceLeft)
              hMember
        · exact
            (fs_zfc_support_raw_set_application_numeral_fresh
              traceId sequenceId 0 hTraceSequence)
              hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#rightId) (x#sequenceId ·ₘ numₘ(1))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId rightId hTraceRight)
              hMember
        · exact
            (fs_zfc_support_raw_set_application_numeral_fresh
              traceId sequenceId 1 hTraceSequence)
              hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport
                (constructor (x#leftId) (x#rightId)) := by
          simp [Formula.freeSupport] at hFieldSupport
          rcases hFieldSupport with hFormulaMember | hConstructorMember
          · exact (hFormulaTraceFresh hFormulaMember).elim
          · exact hConstructorMember
        rcases hConstructorSupport
            (x#leftId) (x#rightId)
            (SetSort.set, traceId) hConstructorMember with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId leftId hTraceLeft)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId rightId hTraceRight)
              hMember
    cases hFailure with
    | length_mismatch hLength =>
        exact fs_zfc_support_raw_logical_payload_length_falsum
          raw tag 2 (x#payloadId) (x#sequenceId)
          traceId indexId hPayload hSequence hTraceNeIndex
          (fs_zfc_support_raw_set_variable_fresh
            traceId sequenceId hTraceSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId sequenceId hIndexSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId payloadId hIndexPayload)
          hTraceFreshContext hPair hSequenceField hDomainField hLength
    | component_failure componentIndex hComponentIndex hLength hDecode =>
        have hComponentBound : componentIndex < 2 := by
          simpa [hLength] using hComponentIndex
        by_cases hZero : componentIndex = 0
        · subst componentIndex
          exact fs_zfc_support_raw_logical_payload_component_falsum
            raw tag freeBase 0
            (x#payloadId) (x#sequenceId) (x#leftId)
            (x#sequenceId ·ₘ numₘ(0))
            traceId indexId hPayload hSequence hLeft hNumericLeft
            hTraceNeIndex
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId sequenceId hIndexSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId payloadId hIndexPayload)
            (fs_zfc_support_raw_set_variable_fresh
              traceId leftId hTraceLeft)
            (fs_zfc_support_raw_set_variable_fresh
              indexId leftId hIndexLeft)
            (fs_zfc_support_raw_set_application_numeral_fresh
              indexId sequenceId 0 hIndexSequence)
            hTraceFreshContext hPair hSequenceField
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (x#sequenceId ·ₘ numₘ(0)))
            hLeftField hComponentIndex hDecode
        · have hOne : componentIndex = 1 := by omega
          subst componentIndex
          exact fs_zfc_support_raw_logical_payload_component_falsum
            raw tag freeBase 1
            (x#payloadId) (x#sequenceId) (x#rightId)
            (x#sequenceId ·ₘ numₘ(1))
            traceId indexId hPayload hSequence hRight hNumericRight
            hTraceNeIndex
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId sequenceId hIndexSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId payloadId hIndexPayload)
            (fs_zfc_support_raw_set_variable_fresh
              traceId rightId hTraceRight)
            (fs_zfc_support_raw_set_variable_fresh
              indexId rightId hIndexRight)
            (fs_zfc_support_raw_set_application_numeral_fresh
              indexId sequenceId 1 hIndexSequence)
            hTraceFreshContext hPair hSequenceField
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (x#sequenceId ·ₘ numₘ(1)))
            hRightField hComponentIndex hDecode
  let rightExists : SetFormula :=
    ∃ₘ[SetSort.set, rightId], body
  let leftExists : SetFormula :=
    ∃ₘ[SetSort.set, leftId], rightExists
  let sequenceExists : SetFormula :=
    ∃ₘ[SetSort.set, sequenceId], leftExists
  let payloadExists : SetFormula :=
    ∃ₘ[SetSort.set, payloadId], sequenceExists
  have hRightImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          rightExists ⟶ₘ Formula.falsum := by
    simpa [rightExists] using
      fs_zfc_support_raw_exists_imp_falsum
        rightId body hBodyImp
  have hLeftImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          leftExists ⟶ₘ Formula.falsum := by
    simpa [leftExists] using
      fs_zfc_support_raw_exists_imp_falsum
        leftId rightExists hRightImp
  have hSequenceImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          sequenceExists ⟶ₘ Formula.falsum := by
    simpa [sequenceExists] using
      fs_zfc_support_raw_exists_imp_falsum
        sequenceId leftExists hLeftImp
  have hPayloadImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          payloadExists ⟶ₘ Formula.falsum := by
    simpa [payloadExists] using
      fs_zfc_support_raw_exists_imp_falsum
        payloadId sequenceExists hSequenceImp
  have hConditionAdmissible :
      Formula.Admissible
        (logical_binary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId leftId rightId traceId indexId) :=
    logical_binary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate
      payloadId sequenceId leftId rightId traceId indexId
      hConstructorAdmissible hFormulaCode hCertificate
  nd_apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionAdmissible)
  let condition : SetFormula :=
    logical_binary_base_certificate_condition_with_ids
      tag constructor formulaCode certificate
      payloadId sequenceId leftId rightId traceId indexId
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hConditionAdmissible)
  have hPayloadImpAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition ⟶ₘ Formula.falsum := by
    simpa [condition,
      logical_binary_base_certificate_condition_with_ids,
      payloadExists, sequenceExists, leftExists, rightExists, body] using
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature))
        (Δ := Γ) (by simp) hPayloadImp
  exact FirstOrder.Derives.impElim hPayloadImpAt hConditionAt

/--
三公式 payload 的 checked 失败否定对应对象证书分支。

长度正确时失败索引必为 `0`、`1` 或 `2`，每一支直接调用公共组件反演核。
-/
theorem fs_zfc_support_raw_logical_ternary_base_certificate_neg_of_payload_failure
    (raw tag freeBase : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hTraceFresh :
      traceId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hIndexFresh :
      indexId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ first second third,
        Term.Admissible first SetSort.set →
        Term.Admissible second SetSort.set →
        Term.Admissible third SetSort.set →
          Term.Admissible
            (constructor first second third) SetSort.set)
    (hConstructorSupport :
      ∀ first second third freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor first second third) →
          freeVariable ∈ Term.freeSupport first ∨
            freeVariable ∈ Term.freeSupport second ∨
              freeVariable ∈ Term.freeSupport third)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, firstId, secondId, thirdId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hFailure :
      FSNamedFormulaPayloadArityFailure
        freeBase (godel_unpair_value raw).2 3) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId firstId secondId thirdId
        traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        (x#firstId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#secondId) (x#sequenceId ·ₘ numₘ(1))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
        traceId indexId,
      formulaCode ≐ₘ
        constructor (x#firstId) (x#secondId) (x#thirdId)]
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hFirst :
      Term.Admissible (x#firstId) SetSort.set :=
    set_variable_admissible firstId
  have hSecond :
      Term.Admissible (x#secondId) SetSort.set :=
    set_variable_admissible secondId
  have hThird :
      Term.Admissible (x#thirdId) SetSort.set :=
    set_variable_admissible thirdId
  have hNumericFirst :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hNumericSecond :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(1)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hNumericThird :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(2)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(2)) hSequence
      (finite_numeral_term_admissible 2)
  have hTracePayload : traceId ≠ payloadId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSequence : traceId ≠ sequenceId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceFirst : traceId ≠ firstId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSecond : traceId ≠ secondId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceThird : traceId ≠ thirdId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hIndexPayload : indexId ≠ payloadId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSequence : indexId ≠ sequenceId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexFirst : indexId ≠ firstId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSecond : indexId ≠ secondId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexThird : indexId ≠ thirdId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hFormulaTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport formulaCode :=
    hReservedFresh formulaCode (by simp) traceId (by simp)
  have hCertificateTraceFresh :
      (SetSort.set, traceId) ∉ Term.freeSupport certificate :=
    hReservedFresh certificate (by simp) traceId (by simp)
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible tag) hPayload
    · exact nat_sequence_code_condition_with_ids_admissible
        (x#sequenceId) (x#payloadId) traceId indexId
        hSequence hPayload
    · exact Formula.Admissible.equal
        (domain_term_admissible (x#sequenceId) hSequence)
        (finite_numeral_term_admissible 3)
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#firstId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hFirst hNumericFirst
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#secondId) (x#sequenceId ·ₘ numₘ(1))
          traceId indexId hSecond hNumericSecond
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
          traceId indexId hThird hNumericThird
    · exact Formula.Admissible.equal hFormulaCode
        (hConstructorAdmissible
          (x#firstId) (x#secondId) (x#thirdId)
          hFirst hSecond hThird)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ Formula.falsum := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hRestOne :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hRestTwo :=
      FirstOrder.Derives.conjElimRight hRestOne
    have hDomainField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#sequenceId) ≐ₘ numₘ(3) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestTwo
    have hRestThree :=
      FirstOrder.Derives.conjElimRight hRestTwo
    have hFirstField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#firstId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestThree
    have hRestFour :=
      FirstOrder.Derives.conjElimRight hRestThree
    have hSecondField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#secondId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestFour
    have hThirdField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hRestFour
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        rcases hFieldSupport with hCertificateMember | hPayloadEq
        · exact hCertificateTraceFresh hCertificateMember
        · exact hTracePayload hPayloadEq
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId payloadId hTracePayload)
              hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList, finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#firstId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId firstId hTraceFirst)
              hMember
        · exact
            (fs_zfc_support_raw_set_application_numeral_fresh
              traceId sequenceId 0 hTraceSequence)
              hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#secondId) (x#sequenceId ·ₘ numₘ(1))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId secondId hTraceSecond)
              hMember
        · exact
            (fs_zfc_support_raw_set_application_numeral_fresh
              traceId sequenceId 1 hTraceSequence)
              hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId thirdId hTraceThird)
              hMember
        · exact
            (fs_zfc_support_raw_set_application_numeral_fresh
              traceId sequenceId 2 hTraceSequence)
              hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport
                (constructor
                  (x#firstId) (x#secondId) (x#thirdId)) := by
          simp [Formula.freeSupport] at hFieldSupport
          rcases hFieldSupport with hFormulaMember | hConstructorMember
          · exact (hFormulaTraceFresh hFormulaMember).elim
          · exact hConstructorMember
        rcases hConstructorSupport
            (x#firstId) (x#secondId) (x#thirdId)
            (SetSort.set, traceId) hConstructorMember with
          hMember | hMember | hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId firstId hTraceFirst)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId secondId hTraceSecond)
              hMember
        · exact
            (fs_zfc_support_raw_set_variable_fresh
              traceId thirdId hTraceThird)
              hMember
    cases hFailure with
    | length_mismatch hLength =>
        exact fs_zfc_support_raw_logical_payload_length_falsum
          raw tag 3 (x#payloadId) (x#sequenceId)
          traceId indexId hPayload hSequence hTraceNeIndex
          (fs_zfc_support_raw_set_variable_fresh
            traceId sequenceId hTraceSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId sequenceId hIndexSequence)
          (fs_zfc_support_raw_set_variable_fresh
            indexId payloadId hIndexPayload)
          hTraceFreshContext hPair hSequenceField hDomainField hLength
    | component_failure componentIndex hComponentIndex hLength hDecode =>
        have hComponentBound : componentIndex < 3 := by
          simpa [hLength] using hComponentIndex
        by_cases hZero : componentIndex = 0
        · subst componentIndex
          exact fs_zfc_support_raw_logical_payload_component_falsum
            raw tag freeBase 0
            (x#payloadId) (x#sequenceId) (x#firstId)
            (x#sequenceId ·ₘ numₘ(0))
            traceId indexId hPayload hSequence hFirst hNumericFirst
            hTraceNeIndex
            (fs_zfc_support_raw_set_variable_fresh
              traceId sequenceId hTraceSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId sequenceId hIndexSequence)
            (fs_zfc_support_raw_set_variable_fresh
              indexId payloadId hIndexPayload)
            (fs_zfc_support_raw_set_variable_fresh
              traceId firstId hTraceFirst)
            (fs_zfc_support_raw_set_variable_fresh
              indexId firstId hIndexFirst)
            (fs_zfc_support_raw_set_application_numeral_fresh
              indexId sequenceId 0 hIndexSequence)
            hTraceFreshContext hPair hSequenceField
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (x#sequenceId ·ₘ numₘ(0)))
            hFirstField hComponentIndex hDecode
        · by_cases hOne : componentIndex = 1
          · subst componentIndex
            exact fs_zfc_support_raw_logical_payload_component_falsum
              raw tag freeBase 1
              (x#payloadId) (x#sequenceId) (x#secondId)
              (x#sequenceId ·ₘ numₘ(1))
              traceId indexId hPayload hSequence hSecond hNumericSecond
              hTraceNeIndex
              (fs_zfc_support_raw_set_variable_fresh
                traceId sequenceId hTraceSequence)
              (fs_zfc_support_raw_set_variable_fresh
                indexId sequenceId hIndexSequence)
              (fs_zfc_support_raw_set_variable_fresh
                indexId payloadId hIndexPayload)
              (fs_zfc_support_raw_set_variable_fresh
                traceId secondId hTraceSecond)
              (fs_zfc_support_raw_set_variable_fresh
                indexId secondId hIndexSecond)
              (fs_zfc_support_raw_set_application_numeral_fresh
                indexId sequenceId 1 hIndexSequence)
              hTraceFreshContext hPair hSequenceField
              (FirstOrder.Derives.eq_refl_m
                (sort := SetSort.set)
                (x#sequenceId ·ₘ numₘ(1)))
              hSecondField hComponentIndex hDecode
          · have hTwo : componentIndex = 2 := by omega
            subst componentIndex
            exact fs_zfc_support_raw_logical_payload_component_falsum
              raw tag freeBase 2
              (x#payloadId) (x#sequenceId) (x#thirdId)
              (x#sequenceId ·ₘ numₘ(2))
              traceId indexId hPayload hSequence hThird hNumericThird
              hTraceNeIndex
              (fs_zfc_support_raw_set_variable_fresh
                traceId sequenceId hTraceSequence)
              (fs_zfc_support_raw_set_variable_fresh
                indexId sequenceId hIndexSequence)
              (fs_zfc_support_raw_set_variable_fresh
                indexId payloadId hIndexPayload)
              (fs_zfc_support_raw_set_variable_fresh
                traceId thirdId hTraceThird)
              (fs_zfc_support_raw_set_variable_fresh
                indexId thirdId hIndexThird)
              (fs_zfc_support_raw_set_application_numeral_fresh
                indexId sequenceId 2 hIndexSequence)
              hTraceFreshContext hPair hSequenceField
              (FirstOrder.Derives.eq_refl_m
                (sort := SetSort.set)
                (x#sequenceId ·ₘ numₘ(2)))
              hThirdField hComponentIndex hDecode
  let thirdExists : SetFormula :=
    ∃ₘ[SetSort.set, thirdId], body
  let secondExists : SetFormula :=
    ∃ₘ[SetSort.set, secondId], thirdExists
  let firstExists : SetFormula :=
    ∃ₘ[SetSort.set, firstId], secondExists
  let sequenceExists : SetFormula :=
    ∃ₘ[SetSort.set, sequenceId], firstExists
  let payloadExists : SetFormula :=
    ∃ₘ[SetSort.set, payloadId], sequenceExists
  have hThirdImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          thirdExists ⟶ₘ Formula.falsum := by
    simpa [thirdExists] using
      fs_zfc_support_raw_exists_imp_falsum
        thirdId body hBodyImp
  have hSecondImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          secondExists ⟶ₘ Formula.falsum := by
    simpa [secondExists] using
      fs_zfc_support_raw_exists_imp_falsum
        secondId thirdExists hThirdImp
  have hFirstImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          firstExists ⟶ₘ Formula.falsum := by
    simpa [firstExists] using
      fs_zfc_support_raw_exists_imp_falsum
        firstId secondExists hSecondImp
  have hSequenceImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          sequenceExists ⟶ₘ Formula.falsum := by
    simpa [sequenceExists] using
      fs_zfc_support_raw_exists_imp_falsum
        sequenceId firstExists hFirstImp
  have hPayloadImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          payloadExists ⟶ₘ Formula.falsum := by
    simpa [payloadExists] using
      fs_zfc_support_raw_exists_imp_falsum
        payloadId sequenceExists hSequenceImp
  have hConditionAdmissible :
      Formula.Admissible
        (logical_ternary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId firstId secondId thirdId
          traceId indexId) :=
    logical_ternary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate
      payloadId sequenceId firstId secondId thirdId
      traceId indexId hConstructorAdmissible
      hFormulaCode hCertificate
  nd_apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionAdmissible)
  let condition : SetFormula :=
    logical_ternary_base_certificate_condition_with_ids
      tag constructor formulaCode certificate
      payloadId sequenceId firstId secondId thirdId
      traceId indexId
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hConditionAdmissible)
  have hPayloadImpAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition ⟶ₘ Formula.falsum := by
    simpa [condition,
      logical_ternary_base_certificate_condition_with_ids,
      payloadExists, sequenceExists, firstExists,
      secondExists, thirdExists, body] using
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature))
        (Δ := Γ) (by simp) hPayloadImp
  exact FirstOrder.Derives.impElim hPayloadImpAt hConditionAt

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
